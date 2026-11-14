import Semantics.Word
import Semantics.Types

/-!
# Manual.Arch — the architectural state as the manuals name it

The independent specification (`docs/MANUAL-SPEC.md`) reads and writes this record, never the model's
`State`. It is the manual's state with the manual's register names, held as plain functions so that
two equal states are equal values (`Mem : PAddr → UInt8`, `GPR : Fin 32 → W32`). The model's state
is projected onto it by `Refine.abs` (`Semantics/Refine/Abs.lean`), which is not part of the spec.

Sources (printed pages):

* GPRs, `HI`/`LO`, `PC`: MD00082 Vol I-A Rev 6.01 §2.8.4 ("CPU Registers"); MD00086 Vol II-A Rev
  6.06 §1.3, Table 1.1, p.5-6 (`GPR[x]`, `HI`, `LO`, `PC`, `LLbit`, `I:`/`I+n:`).
* FPRs and `FCSR`: MD00082 Vol I-A Rev 6.01 §6.4-6.5 (32-bit FPU, `Status.FR = 0`).
* CP0 registers: MD00090 Vol III Rev 6.02 chapter 9, by name (`Status` §9.32, `Cause` §9.36, `EPC`
  §9.38, `BadVAddr` §9.24, `ErrorEPC` §9.68, `EBase` §9.41, `Config` §9.45, `Count` §9.27,
  `Compare` §9.30, `HWREna` §9.23).

The spec keeps a CP0 register as a whole word only where the manual's field table makes every bit
either R/W or "0/ignored on write" under this profile; the reading of each field is in
`Manual/CP0.lean`, by bit position.
-/

namespace Manual

/-- A register file after writing `v` into register `x`. -/
def update (f : Fin 32 → W32) (x : Fin 32) (v : W32) : Fin 32 → W32 :=
  fun y => if y = x then v else f y

/-- The **delayed effect** of the previous instruction's `I+1:` statements (MD00086 Vol II-A Rev
6.06 §1.3, Table 1.1, p.6: "The effect of pseudocode statements for the current instruction labeled
I+1 appears to occur “at the same time” as the effect of pseudocode statements labeled I for the
following instruction"). Only branches and jumps have `I+1:` statements in the modeled set. -/
inductive Delay where
  /-- `I+1: PC ← target` (a taken branch, a jump). -/
  | jump (target : W32)
  /-- `I+1:` assigns nothing (a not-taken ordinary branch): the following instruction is still in
  the branch's delay slot, and `PC` is "automatically incremented by ... 4" after it (Table 1.1,
  p.6). -/
  | fallThrough
  /-- `I+1: NullifyCurrentInstruction()` (a not-taken branch-likely; §2.2.2.5.4, p.26). -/
  | nullify
  deriving DecidableEq, Repr

/-- **The architectural state between two instruction times.** -/
structure Arch where
  /-- `PC` (Table 1.1, p.6): the address of the instruction of the current instruction time. -/
  PC : W32
  /-- `GPR[x]` (Table 1.1, p.5). `GPR[0]` is read through `Manual.readGPR`, which returns 0 (Vol I-A
  §2.8.4: "r0 is hard-wired to a value of zero"); the stored value at index 0 is never read. -/
  GPR : Fin 32 → W32
  /-- `HI` (Table 1.1, p.5). -/
  HI : W32
  /-- `LO` (Table 1.1, p.5). -/
  LO : W32
  /-- `FPR[x]`, the 32 32-bit floating-point registers of a 32-bit FPU (`FP32RegistersMode = 1`;
  MD00082 Vol I-A Rev 6.01 §6.4.1). -/
  FPR : Fin 32 → W32
  /-- `FCSR` (MD00082 Vol I-A Rev 6.01 §6.5.4, Table 6.8, p.92-95), as a word; bits 22..18 read 0
  (`FIR.Has2008 = 0`). -/
  FCSR : W32
  /-- Physical memory, one byte per physical address (`pAddr`). -/
  Mem : PAddr → UInt8
  /-- `LLbit` (Table 1.1, p.6). -/
  LLbit : Bool
  /-- The aligned virtual address of the last `LL`, which an `SC` compares with its own ("An SC will
  fail if the aligned address of the SC does not match that of the preceding LL", MD00086 Vol II-A
  Rev 6.06, SC, p.347). -/
  LLAddr : W32
  /-- CP0 `Status` (12, 0; Vol III §9.32). -/
  Status : W32
  /-- CP0 `Cause` (13, 0; Vol III §9.36): the software-written and exception-written bits. `TI` and
  `IP7..IP2` are not stored here: they are `CauseTI` and the inputs `HW` (`Manual.CauseRead`). -/
  Cause : W32
  /-- CP0 `EPC` (14, 0; Vol III §9.38). -/
  EPC : W32
  /-- CP0 `BadVAddr` (8, 0; Vol III §9.24). -/
  BadVAddr : W32
  /-- CP0 `ErrorEPC` (30, 0; Vol III §9.68). -/
  ErrorEPC : W32
  /-- CP0 `EBase` (15, 1; Vol III §9.41), as stored (read through `Manual.EBaseRead`). -/
  EBase : W32
  /-- `Config.K0` (16, 0, bits 2..0; Vol III Table 9.64, p.235). -/
  ConfigK0 : BitVec 3
  /-- `Config.K23` (16, 0, bits 30..28; Vol III Table 9.64, p.233). -/
  ConfigK23 : BitVec 3
  /-- `Config.KU` (16, 0, bits 27..25; Vol III Table 9.64, p.233). -/
  ConfigKU : BitVec 3
  /-- CP0 `Count` (9, 0; Vol III §9.27, p.183). -/
  Count : W32
  /-- CP0 `Compare` (11, 0; Vol III §9.30, p.187). -/
  Compare : W32
  /-- `Cause.TI` (bit 30; Vol III Table 9.52, p.209): the timer interrupt is pending. -/
  CauseTI : Bool
  /-- CP0 `HWREna` (7, 0; Vol III §9.23, p.175). -/
  HWREna : W32
  /-- The hardware interrupt request lines `HW5..HW0` (inputs; Vol III Table 6.2, p.73). -/
  HW : BitVec 6
  /-- The processor is in the lower power mode entered by `WAIT` (MD00086 Vol II-A Rev 6.06, WAIT,
  p.442: "stalling the pipeline at the completion of the instruction and entering a lower power
  mode"). -/
  LowPower : Bool
  /-- The `I+1:` effect of the previous instruction, still to happen in this instruction time
  (`Delay`), represented as the target `PC` after the current instruction: `some t` for `jump t`;
  `some (branchPC + 8)` for `fallThrough` and `nullify` (the current instruction is the delay slot
  at `branchPC + 4`, and "If no value is assigned to PC during an instruction time ... it is
  automatically incremented by ... 4", Table 1.1, p.6). `isSome` is exactly "the instruction at
  `PC` is in a branch delay slot" (`InstructionInBranchDelaySlot`, Vol III §6.2.3, p.87). -/
  BranchDelay : Option W32
  /-- The previous instruction's `I+1:` statements called `NullifyCurrentInstruction()`: the
  instruction of this instruction time is nullified (MD00086 Vol II-A Rev 6.06 §2.2.2.5.4, p.26). -/
  Nullify : Bool

end Manual
