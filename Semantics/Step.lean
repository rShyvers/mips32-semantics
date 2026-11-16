import Semantics.Exec.Base
import Semantics.Exec.IntArith
import Semantics.Exec.Shift
import Semantics.Exec.BitOps
import Semantics.Exec.Immediate
import Semantics.Exec.Memory
import Semantics.Exec.Atomic
import Semantics.Exec.Branch
import Semantics.Exec.Jump
import Semantics.Exec.Trap
import Semantics.Exec.Syscall
import Semantics.Exec.System
import Semantics.Exec.Cp0
import Semantics.Exec.FpuMove
import Semantics.Exec.FpuControl
import Semantics.Exec.FpuMemory
import Semantics.Exec.FpuArith
import Semantics.Exec.FpuConvert

/-!
# Step — small-step semantics of the modeled MIPS32 Release 6 instruction set

`step` executes one instruction; `run` is `step` iterated with a fuel bound
and nothing else. Ground truth: the latest manual revisions in
`manuals/` are normative, read for the pre-Release-6 wording
(MD00082 Vol I-A Rev 6.01, MD00086 Vol II-A Rev 6.06, MD00090 Vol III
Rev 6.02; see CLAUDE.md), summarised per instruction in
`docs/spec/INSTRUCTION-REF.md`. Comments below that cite "MD00086 Rev 2.50"
with a table or page number are historical citations of that older revision.
Pinned conventions and divergences from the MARS test oracle are in
`docs/spec/SPEC-NOTES.md` §9.

## What `step` does

`step : State → State` is one instruction time of the processor and nothing else. It is total by
its type: the manual has no halting state, and every behaviour the model implements is a state
transition (possibly to the exception vector). Loading a program, the MARS-style `syscall`
services and the conventions for stopping a run are the environment's, not the processor's; they
are in `Semantics/Env.lean`.

0. **Interrupt / standby** (`stepCore`): if an interrupt is requested and enabled
   (`interruptTaken`), take the Interrupt exception (`takeInterrupt`) instead of steps 1-3; after a
   `wait` (`State.standby`) the processor stays stopped until a request restarts it.
1. **Fetch** the word at `pc` (in the byte order of `profile`, little-endian) (`readMemWord s s.pc`): the virtual `pc` is translated
   by the Fixed Mapping MMU (`State.lean`, `translate`) and the word read from physical memory
   `State.physMem`. A misaligned `pc`, or a `pc` outside useg in User Mode, raises Address Error
   (AdEL, `BadVAddr = pc`). Memory that was never written reads as 0 (`State.lean`; 0 encodes
   `sll $0, $0, 0`, a no-op).
2. **Decode** it (`Instruction.decode`, strict). A word that does not decode raises Reserved
   Instruction (or Coprocessor Unusable for an unusable coprocessor's encoding space).
3. **Execute** it (`execInstr`; the effect of each instruction is in its family's file
   `Semantics/Exec/<Family>.lean`, dispatched by `execBody` through `execTables`). Steps 1-3 are
   `execute`; steps 0-3 are `stepCore`.
4. **Timer**: `Count` advances and is compared with `Compare` (`timerTick`; `step = timerTick ∘
   stepCore`). The rate is a pin: one increment per `step`.

Because fetch reads `physMem`, a store to the instruction stream changes what is executed (MD00086
Vol II-A Rev 6.06, SYNCI, p.412). The model has no caches, so `synci` has nothing to synchronize.

## Branch delay slots

`State.pendingBranch = some t` means "the instruction at `pc` is in a delay
slot; control goes to `t` after it". Every branch/jump sets it (taken: the
target; not taken: `pc + 8`). Every non-control-flow instruction goes
through `mkNext`/`advance`, which commits a pending target. A control-transfer
instruction in a delay slot raises Reserved Instruction, as Release 6 requires (`execInstr`).
Release 6 has no branch-likely instructions, so no instruction is ever nullified.

## Exceptions

`exceptionEntry` implements the general exception sequence (MD00090,
"General Exception Processing"): `EPC`/`Cause.BD` (only if `EXL` was 0),
`Cause.ExcCode`, `Status.EXL ← 1`, `PC ←` the general vector (`BEV`
selects which; `EBase` supplies the base when `BEV = 0`), and the pending
branch is abandoned. Raised here: Integer Overflow (`add`/`sub`),
Address Error (misaligned load/store/fetch, or a kernel address referenced from User Mode;
sets `BadVAddr`), Interrupt (`takeInterrupt`, vector offset `0x180` or `0x200` by `Cause.IV`), Reserved
Instruction, Coprocessor Unusable (`Cause.CE` = the unit), Floating Point,
System Call (`syscall`, always), Breakpoint, Trap.

## Floating point

All FP arithmetic is `Semantics/FpOps.lean` (`Mips.Fp`): exact results on bit
patterns, one correctly-rounded pack under FCSR.RM, IEEE flags. No host
`Float` appears anywhere in `step`. Every coprocessor-1 instruction first
checks `Status.CU1` (`usesCop1`); arithmetic instructions finish through
`fpFinishS`/`fpFinishD`, which update FCSR with
`Mips.Fp.fpUpdate` and take the Floating Point exception instead of writing
the destination when an enabled exception was raised.

## Operating modes

Kernel Mode and User Mode (MD00090 Vol III Rev 6.02 ch.3, p.21-23; `kernelMode`, `userMode`):
Supervisor Mode and Debug Mode are not implemented. A coprocessor-0 instruction (`usesCop0`), an
undecodable COP0 word or a CACHE word (`isCop0Word`) executed outside Kernel Mode with
`Status.CU0 = 0` raises Coprocessor Unusable with `Cause.CE = 0` (§6.2.22, p.100). The User-Mode
address check (a reference outside useg from User Mode is an Address Error, Table 4.2, p.30)
belongs to the MMU: every memory access goes through the six `readMem*`/`writeMem*` functions of
`State.lean`, which translate through `translate` (`kernelMode`/`userMode` are defined there).

## Address translation

The MMU is the Fixed Mapping MMU (`Config.MT = 3`, `configValue`; MD00090 Vol III Rev 6.02
Appendix A.1, p.313-317), implemented once in `State.lean` (`fixedMappingPA`, `translate`):
kseg0/kseg1 → the low 512 MB, useg/kuseg → `VA + 1 GB` (`ERL = 0`) or `VA` (`ERL = 1`), kseg2/kseg3
→ `VA`.

## Interrupts

Interrupt compatibility mode only (MD00090 Vol III Rev 6.02 §6.1.1.1, p.73; VI and EIC modes are
optional and absent): request `i` is `Cause.IPi & Status.IMi` (`interruptRequests`), taken when
`Status.IE = 1` and `EXL = ERL = 0` (`interruptsEnabled`). The sources: software requests `IP1..IP0`
(written by `mtc0`), the timer (`Cause.TI`, merged into `IP7`: `IntCtl.IPTI = 7`) and the six
hardware lines `State.hwInt` (inputs; the environment holds them deasserted). `IntCtl` and `SRSCtl`
are constants (`intCtlValue`, `srsCtlValue`: no vectored interrupts, no shadow sets).

## Reset

`resetException` is the Reset exception (§6.2.5, p.89-90) applied to a state; `resetState` is
`resetException powerOnState`, the machine after a cold reset.

## Not modeled

Vectored Interrupt and EIC interrupt modes, TLB (the MMU is the Fixed Mapping MMU), caches, GPR
shadow sets beyond the normal GPRs (`SRSCtl.HSS = 0`), EJTAG (see `docs/spec/SPEC-NOTES.md`).
-/

/-! ## Dispatch to the instruction families -/

/-- **The execution tables**, one per instruction family (`Semantics/Exec/<Family>.lean`). Each
returns the instruction's effect for the instructions of its family and `none` for every other;
every instruction belongs to exactly one family. A later wave adds an instruction to its family's
table only. -/
def execTables : List (State → Instruction → Option State) :=
  [execIntArith, execShift, execBitOps, execImmediate, execMemory, execAtomic,
   execBranch, execJump, execTrap, execSyscall, execSystem, execCp0,
   execFpuMove, execFpuControl, execFpuMemory, execFpuArith, execFpuConvert]

/-- The effect of the already-fetched, already-decoded instruction `instr` in state `s`, **after**
`execInstr`'s guards (no control transfer in a delay slot; the coprocessor usable for the
instructions that need it): the result of the family table that has `instr`. Total: every case
yields the next state (possibly at the exception vector); the fallback `s` is never reached
(every constructor is in a table). -/
def execBody (s : State) (instr : Instruction) : State :=
  (execTables.findSome? (fun f => f s instr)).getD s

/-- `exec_unfold`: reduce `execBody s i`, for `i` a constructor application, to that instruction's
arm of its family table (a proof convenience: `execBody s i` *is* that arm, by definition). -/
macro "exec_unfold" : tactic =>
  `(tactic| dsimp only [execBody, execTables, List.findSome?, execIntArith, execShift, execBitOps,
    execImmediate, execMemory, execAtomic, execBranch, execJump, execTrap, execSyscall, execSystem,
    execCp0, execFpuMove, execFpuControl, execFpuMemory, execFpuArith, execFpuConvert, Option.getD])

/-- Execute the already-fetched, already-decoded instruction `instr` in
state `s`.

First check: if `s` is in a delay slot (`s.pendingBranch = some _`) and
`instr` is a control-transfer instruction (`isBranchLike`), raise Reserved
Instruction, as Release 6 requires ("Release 6: If a control transfer instruction
(CTI) is executed in the delay slot of a branch or jump, Release 6 implementations
are required to signal a Reserved Instruction exception", MD00086 Vol II-A Rev 6.06,
BEQ, p.72; MD00082 Vol I-A Rev 6.01 §5.3.2.1, p.62). The exception is
taken in the delay slot: `EPC` = the branch, `Cause.BD = 1` (`exceptionEntry`).
(The test is written `isBranchLike instr && …` in that order so that it reduces
to `false` by computation for any non-branch instruction, whatever `s` is.)

Second check: a coprocessor-1 instruction (`usesCop1`) with `Status.CU1 = 0`
raises Coprocessor Unusable (`Cause.CE = 1`) and does nothing else.

Third check: a coprocessor-0 instruction (`usesCop0`) executed when coprocessor 0 is not usable
(`cp0Usable`: not Kernel Mode and `Status.CU0 = 0`) raises Coprocessor Unusable (`Cause.CE = 0`)
and does nothing else (MD00090 Vol III Rev 6.02 §6.2.22, p.100). The second and third checks
concern disjoint sets of instructions, so their order does not matter. The first check comes
before the third: `eret` or `wait` in a delay slot is UNDEFINED (ERET p.177, WAIT p.442) and the
pin is Reserved Instruction in every mode.

Otherwise the instruction's effect is `execBody s instr`. -/
def execInstr (s : State) (instr : Instruction) : State :=
  if isBranchLike instr && s.pendingBranch.isSome then
    takeException s excCodeRI
  else if usesCop1 instr && !cu1Enabled s then
    takeCoprocessorUnusable s
  else if usesCop0 instr && !cp0Usable s then
    takeCop0Unusable s
  else execBody s instr

/-- **Fetch, decode, execute**: the instruction part of one instruction time (`step` adds the timer).

* Fetch is `readMemWord s s.pc`, a word read (byte order of `profile`) from physical memory through the MMU
  (`translate`); it fails only for a misaligned `pc` or a `pc` outside useg in User Mode, which
  raise Address Error (AdEL) with `BadVAddr = pc` (MD00090 Vol III Rev 6.02 §6.2.9, p.92-93).
* A word that does not decode: Reserved Instruction — except that a COP0 or
  CACHE word (`isCop0Word`) raises Coprocessor Unusable (`CE = 0`) when
  coprocessor 0 is not usable (`cp0Usable`), a word in coprocessor 1's
  encoding space (`isCop1Word`) raises Coprocessor Unusable (`CE = 1`) when
  `Status.CU1 = 0`, and a word in coprocessor 2's (`isCop2Word`) always raises
  Coprocessor Unusable (`CE = 2`): the model has no coprocessor 2 and
  `Status.CU2` reads 0.
* Otherwise `execInstr`. -/
def execute (s : State) : State :=
  match readMemWord s s.pc with
  | none => takeAddressException s excCodeAdEL s.pc
  | some w =>
    match decode w with
    | none =>
      if isCop0Word w && !cp0Usable s then takeCop0Unusable s
      else if isCop1Word w && !cu1Enabled s then takeCoprocessorUnusable s
      else if isCop2Word w then exceptionEntry s excCodeCpU 2#32
      else takeException s excCodeRI
    | some instr => execInstr s instr

/-- **The processor's part of one instruction time**, before the timer:

1. If an interrupt is requested and enabled (`interruptTaken`), take the Interrupt exception
   (`takeInterrupt`) and execute nothing. An interrupt is asynchronous and "the highest priority
   relative to the next instruction" (MD00090 Vol III Rev 6.02 Table 6.7, p.84); Table 6.6 (p.83)
   puts "Interrupt" above every instruction-fetch and instruction exception (Address Error -
   Instruction fetch, Instruction Validity, Execution, data-access exceptions), below only Reset,
   Soft Reset, the EJTAG debug exceptions, NMI and Machine Check, none of which `step` raises (Reset
   is applied by the environment, `resetException`). So the check comes before the fetch.
2. Else, in standby (`State.standby`, after `wait`): `standbyStep` (stay, or restart).
3. Else fetch, decode and execute the instruction at `pc` (`execute`).

Execution hazards on the interrupt state (MD00090 Vol III §6.1.2.1, Table 6.5, p.82: `mtc0` to
`Status` IM/ERL/EXL/IE or to `Cause` IP1..0, `ei`, `di`, made visible "no later than the instruction
following the EHB") are cleared at once: the change is seen by the next step's check (pin; `ehb` is
`sll $0, $0, 3`, a no-op). -/
def stepCore (s : State) : State :=
  if interruptTaken s then takeInterrupt s
  else if s.standby then standbyStep s
  else execute s

/-- **One instruction time**: the processor's part (`stepCore`: take an interrupt, or stay in
standby, or fetch, decode and execute the instruction at `pc`), then advance the timer (`timerTick`:
`Count` + 1 unless `Cause.DC = 1`; `Cause.TI` set when `Count = Compare`). There is no halting
case: the result is always the next architectural state.

The timer is applied to the state the instruction (or the exception) produced, so an instruction
reads the `Count` the step started with (`mfc0`, `rdhwr`), and a `Count`/`Compare`/`Cause.DC` written
by `mtc0` is what the timer then compares and advances. A timer request raised by this step's tick
is seen by the next step's interrupt check. -/
def step (s : State) : State := timerTick (stepCore s)

/-- The bare machine run: `step` iterated `n` times from `s`. It knows nothing about programs,
services or halting (those are `Semantics/Env.lean`'s `runHosted`). Total by structural
recursion on `n`. -/
def run (s : State) : Nat → State
  | 0 => s
  | n + 1 => run (step s) n

/-! ## Reset -/

/-- **The Reset exception** (cold reset), taken from state `s` (MD00090 Vol III Rev 6.02 §6.2.5
"Reset Exception", p.89-90). "On a Reset Exception, only the following registers have defined
state"; the Operation (p.89-90), restricted to the registers this model has:

```
StatusBEV ← 1;  StatusERL ← 1
StatusRP ← 0;  StatusTS ← 0;  StatusSR ← 0;  StatusNMI ← 0   -- not implemented: read as 0
CauseDC ← 0
HWREna ← 0
EBaseExceptionBase ← 0                                     -- EBase reads 0x8000_0000
Config ← ConfigurationState;  ConfigK0 ← 2                 -- "Suggested"; Config1..3 fixed
                                     -- K23, KU: reset "Undefined" (p.233), pinned to 2 like K0
if InstructionInBranchDelaySlot then ErrorEPC ← restartPC  # PC of branch/jump
else ErrorEPC ← restartPC                                  # PC of instruction
PC ← 0xBFC0 0000
```

`IntCtlVS ← 0`, `SRSCtlHSS ← HighestImplementedShadowSet` and `SRSCtlESS/PSS/CSS ← 0` (p.90) hold
already: `IntCtl` and `SRSCtl` are constants with `VS = 0`, `HSS = ESS = PSS = CSS = 0`
(`intCtlValue`, `srsCtlValue`). The rest of the Operation names
registers the model does not implement (Random, PageMask, PageGrain, Wired, EntryHi, SRSMap, WatchLo,
PerfCnt) or constants (`Config1`/`Config2`/`Config3 ← ConfigurationState`: `config1Value`,
`config2Value`, `config3Value`): nothing to do. `Count`, `Compare` and `Cause.TI` are not in the list (reset state
"Undefined", Tables 9.44, 9.46, 9.52, p.183, 187, 209): they keep their values. Every register the section does not list keeps whatever it held: its
reset state is undefined, and keeping it is one legal value (pin). In particular the other
`Status` bits (`UM`, `EXL`, `IE`, `IM`, `CU0`, `CU1`) are unchanged; with `ERL = 1` the processor
is in Kernel Mode regardless (§3.2, p.21). Two further pins: the pending branch is dropped (the
reset "aborts state machines", p.89; "restart PC" is the branch when the interrupted instruction
was in a delay slot, `s.pc - 4`), and `LLbit` is cleared (its reset state is not given). A processor
in standby restarts ("The assertion of any reset or NMI must restart the pipeline and the
corresponding exception must be taken", MD00086 Vol II-A Rev 6.06, WAIT, p.442): `standby ← false`.
The hardware interrupt lines `hwInt` are inputs and keep their values. -/
def resetException (s : State) : State :=
  { s with
      cp0Status := s.cp0Status ||| statusBevMask ||| statusErlMask
      cp0Cause := s.cp0Cause &&& ~~~causeDcMask
      cp0HWREna := 0#32
      cp0EBase := ebaseFixedBits
      cp0ConfigK0 := 2#3
      cp0ConfigK23 := 2#3
      cp0ConfigKU := 2#3
      cp0ErrorEpc := if s.pendingBranch.isSome then s.pc - 4#32 else s.pc
      pc := resetVector
      pendingBranch := none
      llBit := false
      standby := false }

/-- **The state after a cold reset**: the Reset exception applied to `powerOnState` (whose
values for the registers the reset leaves undefined are all pinned to 0, `State.lean`). So
`pc = 0xBFC0_0000`, `Status = BEV | ERL` (0x0040_0004: Kernel Mode, bootstrap vectors, CU0 = CU1
= 0), `Cause = 0`, `Count = Compare = 0`, no timer interrupt pending, `HWREna = 0`, `EBase` reads 0x8000_0000, `Config.K0 = K23 = KU = 2`, `ErrorEPC = 0` (the restart PC
of a power-on reset is not meaningful, p.89: "this value may or may not be predictable if the
Reset Exception was taken as the result of power being applied to the processor"), every GPR,
FPR and `FCSR` 0, memory empty. Properties: `Specs/Reset.lean`. -/
def resetState : State := resetException powerOnState
