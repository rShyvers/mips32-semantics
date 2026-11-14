import Semantics.Manual.Operation
import Semantics.Manual.Encoding
import Semantics.Manual.Interrupts
import Semantics.Manual.Timer
import Semantics.Manual.Reset

/-!
# Manual.Cycle — one instruction time

`InstructionTime impl oracle dec a` is the architectural state after one instruction time from `a`:

1. **Interrupt.** If an interrupt is taken (`InterruptTaken`, MD00090 Vol III Rev 6.02 §6.1, p.72),
   the general exception processing with `ExcCode = Int` (§6.2.3, p.86-88; §6.2.26, p.102) instead of
   the instruction: interrupts have "the highest priority relative to the next instruction" (Table
   6.7, p.84; Table 6.6, p.83). A processor in the lower power mode of `WAIT` restarts: "If the
   pipeline restarts as the result of an enabled interrupt, that interrupt is taken between the WAIT
   instruction and the following instruction" (MD00086 Vol II-A Rev 6.06, WAIT, p.442).
2. **Lower power mode** (`WAIT`): `LowPowerTime`.
3. **Nullified instruction**: the previous instruction's `I+1:` statements called
   `NullifyCurrentInstruction()` (MD00086 Vol II-A Rev 6.06 §2.2.2.5.4, p.26): the instruction is
   neither fetched nor executed and raises no exception; no statement assigns `PC`, so it advances by
   4 (§1.3, Table 1.1, p.6).
4. **Fetch** (`InstructionFetch`, §2.2.2.4.2, Figure 2.29, p.25), **decode** by the format diagrams
   (`dec`, `DecoderSound`), and **execute**: a CTI in a delay slot is UNPREDICTABLE (BEQ p.72;
   `Oracle.ctiInSlot`); an instruction of an unusable coprocessor's encoding space raises Coprocessor
   Unusable (Vol III §6.2.22, p.100), which "takes priority over the Reserved Instruction exception"
   (MD00086 Vol II-A Rev 6.06 Table A.1, p.449); a word that matches no format diagram raises Reserved
   Instruction (§6.2.21; Table A.1, p.449: "Executing such an instruction must cause a Reserved
   Instruction exception"); otherwise the Operation runs.
5. **Completion.** A signalled exception enters the general exception processing from the state the
   Operation had reached. Otherwise `PC` becomes, in this order: the delay slot `PC + 4` when the
   Operation scheduled `I+1:` statements (and those are recorded in `BranchDelay`/`Nullify`); a `PC`
   assigned at time `I`; the target of the previous branch's `I+1: PC ← …` (`BranchDelay`); else
   `PC + 4`.
6. **Timer** (`TimerTick`), after the instruction.

**Representation of `I+1:` (stated here, as the plan requires).** `BranchDelay` holds the `PC` that
follows the delay-slot instruction: a taken branch's target, and for a not-taken branch (`I+1`
assigns nothing) or a nullifying one `branchPC + 8`, which is "PC + 4" of the delay slot at
`branchPC + 4`. Both give the next `PC` the manual gives; `BranchDelay.isSome` is
`InstructionInBranchDelaySlot`.
-/

namespace Manual

/-- **The control transfer instructions** that may not be placed in a delay slot (MD00086 Vol II-A
Rev 6.06, BEQ, Restrictions, p.72: "CTIs include all branches and jumps, NAL, ERET, ERETNC, DERET,
WAIT, and PAUSE"; `NAL` is the encoding of `BLTZAL r0`, `ERETNC`/`DERET` do not exist on this
profile). -/
def IsCTI : Instruction → Bool
  | .beq .. | .bne .. | .blez .. | .bgtz .. | .bltz .. | .bgez .. | .bltzal .. | .bgezal ..
  | .j .. | .jal .. | .jr .. | .jalr ..
  | .beql .. | .bnel .. | .blezl .. | .bgtzl .. | .bltzl .. | .bgezl .. | .bltzall .. | .bgezall ..
  | .bc1f .. | .bc1t .. | .bc1fl .. | .bc1tl .. | .eret | .wait .. => true
  | i => IsPAUSE i

/-- `dec` decodes by the transcribed format diagrams: an instruction it returns for `w` has the
diagram `w` whenever that diagram is transcribed (`enc`). Completeness (every word matching a
diagram is decoded to that instruction, and only such words) is stated with the full `enc` in 7D. -/
def DecoderSound (dec : W32 → Option Instruction) : Prop :=
  ∀ w i v, dec w = some i → enc i = some v → v = w

/-- The state after the Operation of an instruction completed without an exception (point 5 of the
module doc). `a` is the state the instruction time started with. -/
def Complete (a : Arch) (f : Frame) : Arch :=
  match f.delay with
  | some d =>
    { f.arch with
        PC := a.PC + 4#32
        BranchDelay := some (match d with | .jump t => t | _ => a.PC + 8#32)
        Nullify := d == .nullify }
  | none =>
    match f.pcSet with
    | some p => { f.arch with PC := p, BranchDelay := none }
    | none => { f.arch with PC := a.BranchDelay.getD (a.PC + 4#32), BranchDelay := none }

/-- **Execute instruction `i`, fetched as `w`** (points 4-5). `none`: `i`'s page is not transcribed
yet. -/
def Execute (c : Ctx) (w : W32) (i : Instruction) (a : Arch) : Option Arch :=
  let gep := fun e (x : Arch) => GeneralExceptionProcessing c.oracle e x
  if IsCTI i && a.BranchDelay.isSome then
    match c.oracle.ctiInSlot a i with
    | .signal e => some (gep e a)
    | .arbitrary a' => some a'
    | .proceed => runOperation
  else runOperation
where
  /-- The coprocessor-usability checks, then the Operation (points 4-5). -/
  runOperation : Option Arch :=
    if InCop1Space w && !StatusCU1 a then
      some (GeneralExceptionProcessing c.oracle (.CoprocessorUnusable 1) a)
    else if InCop0Space w && !CP0Usable a then
      some (GeneralExceptionProcessing c.oracle (.CoprocessorUnusable 0) a)
    else
      match Operation i with
      | none => none
      | some op =>
        match op.run c { arch := a } with
        | (.ok (), f) => some (Complete a f)
        | (.signal e, f) => some (GeneralExceptionProcessing c.oracle e f.arch)

/-- **A word that matches no format diagram** (point 4): Coprocessor Unusable for the encoding space
of an unusable coprocessor (COP2 is never usable: `Status.CU2` reads 0, there is no coprocessor 2),
else Reserved Instruction. -/
def Undecodable (w : W32) (a : Arch) : Exception :=
  if InCop0Space w && !CP0Usable a then .CoprocessorUnusable 0
  else if InCop1Space w && !StatusCU1 a then .CoprocessorUnusable 1
  else if InCop2Space w then .CoprocessorUnusable 2
  else .ReservedInstruction

/-- **Fetch, decode, execute** (point 4). -/
def FetchExecute (c : Ctx) (dec : W32 → Option Instruction) (a : Arch) : Option Arch :=
  match InstructionFetch.run c { arch := a } with
  | (.signal e, f) => some (GeneralExceptionProcessing c.oracle e f.arch)
  | (.ok w, _) =>
    match dec w with
    | none => some (GeneralExceptionProcessing c.oracle (Undecodable w a) a)
    | some i => Execute c w i a

/-- **One instruction time** (points 1-6). `none` only when the instruction fetched is one whose
page is not transcribed yet (sub-wave 7A). -/
def InstructionTime (i : Impl) (o : Oracle) (dec : W32 → Option Instruction) (a : Arch) :
    Option Arch :=
  let c : Ctx := { impl := i, oracle := o }
  let r :=
    if InterruptTaken i a then
      -- an interrupt also restarts a pipeline stopped by `WAIT` (WAIT, p.442)
      some { GeneralExceptionProcessing o .Interrupt a with LowPower := false }
    else if a.LowPower then some (LowPowerTime i a)
    else if a.Nullify then some { a with PC := a.PC + 4#32, BranchDelay := none, Nullify := false }
    else FetchExecute c dec a
  r.map (TimerTick i)

end Manual
