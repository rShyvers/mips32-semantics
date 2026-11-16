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
3. (Release 6 has no branch-likely instruction, so no instruction time is nullified.)
4. **Fetch** (`InstructionFetch`, §2.2.2.4.2, Figure 2.29, p.25), **decode** by the format diagrams
   (`dec`, `DecoderSound`), and **execute**: a word that matches a diagram but has an UNPREDICTABLE
   field value is resolved by the oracle (`UnpredictableEncoding`, `Unpredictable`; §2.1.1, p.12);
   a CTI in a delay slot signals Reserved Instruction ("Release 6: If a control transfer instruction
   (CTI) is executed in the delay slot of a branch or jump, Release 6 implementations are required to
   signal a Reserved Instruction exception", BEQ, Restrictions, p.72); an instruction of an unusable coprocessor's encoding space raises Coprocessor
   Unusable (Vol III §6.2.22, p.100), which "takes priority over the Reserved Instruction exception"
   (MD00086 Vol II-A Rev 6.06 Table A.1, p.449); a word that matches no format diagram raises Reserved
   Instruction (§6.2.21; Table A.1, p.449: "Executing such an instruction must cause a Reserved
   Instruction exception"); otherwise the Operation runs.
5. **Completion.** A signalled exception enters the general exception processing from the state the
   Operation had reached. Otherwise `PC` becomes, in this order: the delay slot `PC + 4` when the
   Operation scheduled `I+1:` statements (and those are recorded in `BranchDelay`); a `PC`
   assigned at time `I`; the target of the previous branch's `I+1: PC ← …` (`BranchDelay`); else
   `PC + 4`.
6. **Timer** (`TimerTick`), after the instruction.

**Representation of `I+1:` (stated here, as the plan requires).** `BranchDelay` holds the `PC` that
follows the delay-slot instruction: a taken branch's target, and for a not-taken branch (`I+1`
assigns nothing, and `NAL`) `branchPC + 8`, which is "PC + 4" of the delay slot at
`branchPC + 4`. Both give the next `PC` the manual gives; `BranchDelay.isSome` is
`InstructionInBranchDelaySlot`.

-- BEGIN R6-3
**Compact branches and forbidden slots** (Release 6). A compact branch or jump assigns `PC` at time
`I` when taken (no delay slot). A conditional compact branch that is not taken leaves the next
instruction in its forbidden slot (`Delay.forbiddenSlot`, set by the page's Operation, `Ops.
ForbiddenSlot`); `Complete` records it in `BranchDelay` as `fallThrough` is, `branchPC + 8`. The
manual gives the forbidden slot the delay slot's rules: "In Release 6, if a CTI is placed in a branch
delay slot or a compact branch forbidden slot, implementations are required to signal a Reserved
Instruction exception" (MD00082 Vol I-A Rev 6.01 §5.3.2.1, p.62; "but only when the branch is not
taken", B<cond>C p.84), and an exception there reports `EPC` = the branch with `BD` set (§5.3.2.2,
p.62; DECISIONS D6). So point 4's CTI check and the general exception processing apply to it
unchanged, through `BranchDelay.isSome`.
-- END R6-3
-/

namespace Manual

/-- **The control transfer instructions** that may not be placed in a delay slot (MD00086 Vol II-A
Rev 6.06, BEQ, Restrictions, p.72: "CTIs include all branches and jumps, NAL, ERET, ERETNC, DERET,
WAIT, and PAUSE"; `DERET` is not on this profile) or a forbidden slot (B<cond>C,
Restrictions, p.84; MD00082 Vol I-A Rev 6.01 §5.3.2.1, p.62). "All branches and jumps" includes the
Release 6 compact branches and jumps. -/
def IsCTI : Instruction → Bool
  | .beq .. | .bne .. | .blez .. | .bgtz .. | .bltz .. | .bgez .. | .nal .. | .bal ..
  | .j .. | .jal .. | .jalr .. | .jalrHb .. | .eret | .wait .. | .pause => true
  -- BEGIN R6-2
  | .eretnc => true
  -- END R6-2
  -- BEGIN R6-3
  | .bc .. | .balc .. | .beqc .. | .bnec .. | .bltc .. | .bgec .. | .bltuc .. | .bgeuc ..
  | .blezc .. | .bgezc .. | .bgtzc .. | .bltzc .. | .beqzc .. | .bnezc ..
  | .blezalc .. | .bgezalc .. | .bgtzalc .. | .bltzalc .. | .beqzalc .. | .bnezalc ..
  | .bovc .. | .bnvc .. | .jic .. | .jialc .. => true
  -- END R6-3
  | _ => false

/-- `dec` decodes by the format diagrams: an instruction it returns for `w` has the diagram `w`
(`enc`; every constructor has a diagram since 7B). The model's `decode` satisfies it since 7R (the
`JR`/`JALR` hint field is no longer ignored); proved in 7D (`Refine.decoderSound_decode`,
`Semantics/Refine/Decode.lean`; on the trusted surface), and also checked by `#guard`s
(`Semantics/Tests/ManualTests.lean`). Completeness on the model's well-formed instructions
(`decode` returns `i` for the diagram of `i`) is `Refine.decode_of_enc`; it is not part of this
definition. -/
def DecoderSound (dec : W32 → Option Instruction) : Prop :=
  ∀ w i v, dec w = some i → enc i = some v → v = w

/-- The state after the Operation of an instruction completed without an exception (point 5 of the
module doc). `a` is the state the instruction time started with. -/
def Complete (a : Arch) (f : Frame) : Arch :=
  match f.delay with
  | some d =>
    { f.arch with
        PC := a.PC + 4#32
        BranchDelay := some (match d with
          | .jump t => t
          | .fallThrough => a.PC + 8#32
          -- BEGIN R6-3
          | .forbiddenSlot => a.PC + 8#32
          -- END R6-3
          ) }
  | none =>
    match f.pcSet with
    | some p => { f.arch with PC := p, BranchDelay := none }
    | none => { f.arch with PC := a.BranchDelay.getD (a.PC + 4#32), BranchDelay := none }

/-- **Execute instruction `i`, fetched as `w`** (points 4-5). `none` only if `Operation i = none`,
which no constructor has since 7B. -/
def Execute (c : Ctx) (w : W32) (i : Instruction) (a : Arch) : Option Arch :=
  if IsCTI i && a.BranchDelay.isSome then
    -- Release 6: a CTI in a delay slot signals Reserved Instruction (BEQ, Restrictions, p.72)
    some (GeneralExceptionProcessing c.impl c.oracle .ReservedInstruction a)
  else runOperation
where
  /-- The coprocessor-usability checks, then the Operation (points 4-5). -/
  runOperation : Option Arch :=
    if InCop1Space w && !StatusCU1 a then
      some (GeneralExceptionProcessing c.impl c.oracle (.CoprocessorUnusable 1) a)
    else if InCop0Space w && !CP0Usable a then
      some (GeneralExceptionProcessing c.impl c.oracle (.CoprocessorUnusable 0) a)
    else
      match Operation i with
      | none => none
      | some op =>
        match op.run c { arch := a } with
        | (.ok (), f) => some (Complete a f)
        | (.signal e, f) => some (GeneralExceptionProcessing c.impl c.oracle e f.arch)

/-- **A word that matches no format diagram** (point 4): Coprocessor Unusable for the encoding space
of an unusable coprocessor (COP2 is never usable: `Status.CU2` reads 0, there is no coprocessor 2),
else Reserved Instruction. -/
def Undecodable (w : W32) (a : Arch) : Exception :=
  if InCop0Space w && !CP0Usable a then .CoprocessorUnusable 0
  else if InCop1Space w && !StatusCU1 a then .CoprocessorUnusable 1
  else if InCop2Space w then .CoprocessorUnusable 2
  else .ReservedInstruction

/-- **A word with an UNPREDICTABLE field value** (`UnpredictableEncoding`, point 4): the word is in
the encoding space of the diagram it matches, so the coprocessor-usability check of that space comes
first, as for every instruction of the space ("the Coprocessor Unavailable exception takes priority
over the Reserved Instruction exception", MD00086 Vol II-A Rev 6.06 Table A.1, p.449); then the
oracle's outcome (`Oracle.unpredictableEncoding`; `.proceed` treats the word as matching no
diagram). -/
def Unpredictable (c : Ctx) (w : W32) (a : Arch) : Arch :=
  let gep := fun e (x : Arch) => GeneralExceptionProcessing c.impl c.oracle e x
  if InCop1Space w && !StatusCU1 a then gep (.CoprocessorUnusable 1) a
  else if InCop0Space w && !CP0Usable a then gep (.CoprocessorUnusable 0) a
  else
    match c.oracle.unpredictableEncoding a w with
    | .signal e => gep e a
    | .arbitrary a' => a'
    | .proceed => gep (Undecodable w a) a

/-- **Fetch, decode, execute** (point 4). -/
def FetchExecute (c : Ctx) (dec : W32 → Option Instruction) (a : Arch) : Option Arch :=
  match InstructionFetch.run c { arch := a } with
  | (.signal e, f) => some (GeneralExceptionProcessing c.impl c.oracle e f.arch)
  | (.ok w, _) =>
    match dec w with
    | none =>
      if UnpredictableEncoding w then some (Unpredictable c w a)
      else some (GeneralExceptionProcessing c.impl c.oracle (Undecodable w a) a)
    | some i => Execute c w i a

/-- **One instruction time** (points 1-6). `none` only if the instruction fetched had no
transcribed Operation, which no constructor has since 7B (the `Option` is kept from 7A). -/
def InstructionTime (i : Impl) (o : Oracle) (dec : W32 → Option Instruction) (a : Arch) :
    Option Arch :=
  let c : Ctx := { impl := i, oracle := o }
  let r :=
    if InterruptTaken i a then
      -- an interrupt also restarts a pipeline stopped by `WAIT` (WAIT, p.442)
      some { GeneralExceptionProcessing i o .Interrupt a with LowPower := false }
    else if a.LowPower then some (LowPowerTime i a)
    else FetchExecute c dec a
  r.map (TimerTick i)

end Manual
