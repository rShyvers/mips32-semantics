import Semantics.Word
import Semantics.Types

/-!
# Manual.Arch — the architectural state as the manuals name it

The independent specification (`docs/MANUAL-SPEC.md`) reads and writes this record, never the model's
`State`. It is the manual's state with the manual's register names, held as plain functions so that
two equal states are equal values (`Mem : PAddr → UInt8`, `GPR : Fin 32 → W32`). The model's state
is projected onto it by `Refine.abs` (`Semantics/Refine/Abs.lean`), which is not part of the spec.

Sources (printed pages):

* GPRs, `PC`: MD00082 Vol I-A Rev 6.01 §2.8.4 ("CPU Registers"); MD00086 Vol II-A Rev
  6.06 §1.3, Table 1.1, p.5-6 (`GPR[x]`, `PC`, `LLbit`, `I:`/`I+n:`). Release 6 has no `HI`/`LO`
  (the instructions that used them are removed) and no branch-likely instructions, so no
  `NullifyCurrentInstruction()`.
* FPRs and `FCSR`: MD00082 Vol I-A Rev 6.01 §6.4-6.5 (the Release 6 64-bit FPU, `Status.FR = 1`
  read-only, `FIR.Has2008 = 1`, `FCSR.NAN2008 = ABS2008 = 1` read-only).
* CP0 registers: MD00090 Vol III Rev 6.02 chapter 9, by name (`Status` §9.32, `Cause` §9.36, `EPC`
  §9.38, `BadVAddr` §9.24, `ErrorEPC` §9.68, `EBase` §9.41, `Config` §9.45, `Count` §9.27,
  `Compare` §9.30, `HWREna` §9.23; Release 6: `UserLocal` §9.11, `BadInstr` §9.25, `BadInstrP`
  §9.26, `KScratch1..6` §9.70, `Config5.SBRI` §9.50; `LLAddr` §9.52 is `LLbit` plus an address
  field this profile does not implement).

The spec keeps a CP0 register as a whole word only where the manual's field table makes every bit
either R/W or "0/ignored on write" under this profile; the reading of each field is in
`Manual/CP0.lean`, by bit position.
-/

namespace Manual

/-- A register file after writing `v` into register `x`. -/
def update {α : Type} (f : Fin 32 → α) (x : Fin 32) (v : α) : Fin 32 → α :=
  fun y => if y = x then v else f y

/-- The **delayed effect** of the previous instruction's `I+1:` statements (MD00086 Vol II-A Rev
6.06 §1.3, Table 1.1, p.6: "The effect of pseudocode statements for the current instruction labeled
I+1 appears to occur “at the same time” as the effect of pseudocode statements labeled I for the
following instruction"). Only branches and jumps have `I+1:` statements in the modeled set. -/
inductive Delay where
  /-- `I+1: PC ← target` (a taken branch, a jump). -/
  | jump (target : W32)
  /-- `I+1:` assigns nothing (a not-taken ordinary branch, and `NAL`, "considered to be a not-taken
  branch, with a delay slot", NAL p.306): the following instruction is still in the branch's delay
  slot, and `PC` is "automatically incremented by ... 4" after it (Table 1.1, p.6). -/
  | fallThrough
  /-- A conditional compact branch was not taken: the following instruction is in its **forbidden
  slot** (Release 6; MD00082 Vol I-A Rev 6.01 §5.3.2, p.62: conditional compact branches "do not
  have a delay slot; they have instead a forbidden slot"; B<cond>C, Restrictions, p.84). It is not
  an `I+1:` statement of the page: the Operation assigns nothing to `PC` and the next instruction is
  `PC + 4`; what the slot changes is the rule for that instruction, which the manual gives as the
  delay slot's: a CTI there signals Reserved Instruction (§5.3.2.1, p.62), and "If an exception or
  interrupt prevents the completion of an instruction in a delay slot or forbidden slot, the
  hardware reports an Exception PC (CP0 EPC) of the branch, with a status bit set ... to indicate
  that the exception was for the instruction in the delay slot of the branch" (§5.3.2.2, p.62;
  DECISIONS D6, a pin: MD00090 Vol III Rev 6.02 §6.2.3, p.87, tests only
  `InstructionInBranchDelaySlot`). So it is recorded in `BranchDelay` as `fallThrough` is. -/
  | forbiddenSlot
  deriving DecidableEq, Repr

/-- **The architectural state between two instruction times.** -/
structure Arch where
  /-- `PC` (Table 1.1, p.6): the address of the instruction of the current instruction time. -/
  PC : W32
  /-- `GPR[x]` (Table 1.1, p.5). `GPR[0]` is read through `Manual.readGPR`, which returns 0 (Vol I-A
  §2.8.4: "r0 is hard-wired to a value of zero"); the stored value at index 0 is never read. -/
  GPR : Fin 32 → W32
  /-- `FPR[x]`, the 32 64-bit floating-point registers of the 64-bit FPU (`Status.FR = 1`, so
  `FP32RegistersMode` is 1: `Manual.FP32RegistersMode`; MD00082 Vol I-A Rev 6.01 §6.4.1, p.84). -/
  FPR : Fin 32 → BitVec 64
  /-- `FCSR` (MD00082 Vol I-A Rev 6.01 §6.5.4, Table 6.8, p.92-95), its R/W fields as a word
  (`FCSRWritable`); the other bits are 0 here, and `FCSRRead` adds the read-only `ABS2008` and
  `NAN2008`, which read 1 in Release 6. -/
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
  `some (branchPC + 8)` for `fallThrough` (the current instruction is the delay slot
  at `branchPC + 4`, and "If no value is assigned to PC during an instruction time ... it is
  automatically incremented by ... 4", Table 1.1, p.6). `isSome` is exactly "the instruction at
  `PC` is in a branch delay slot" (`InstructionInBranchDelaySlot`, Vol III §6.2.3, p.87).
  It is also `some (branchPC + 8)` in the forbidden slot of a not-taken conditional compact branch
  (`Delay.forbiddenSlot`), which the manual treats as a delay slot (DECISIONS D6).
  -/
  BranchDelay : Option W32
  /-- CP0 `UserLocal` (4, 2; Vol III §9.11, Table 9.19, p.143). -/
  UserLocal : W32
  /-- CP0 `BadInstr` (8, 1; Vol III §9.25, Table 9.42, p.179). -/
  BadInstr : W32
  /-- CP0 `BadInstrP` (8, 2; Vol III §9.26, Table 9.43, p.181). -/
  BadInstrP : W32
  /-- CP0 `KScratch1..6` (31, 2..7; Vol III §9.70, Table 9.84, p.311): `KScratch k` is
  `KScratch(k+1)` at select `k + 2`. -/
  KScratch : Fin 6 → W32
  /-- `Config5.SBRI` (16, 5, bit 6; Vol III §9.50, Table 9.69, p.263), the only R/W field of
  `Config5` on this profile. -/
  Config5SBRI : Bool

/-- **The R/W fields of FCSR** on this profile (MD00082 Vol I-A Rev 6.01 Table 6.8, p.92-94): `FS`
(24), `Cause` (17..12), `Enables` (11..7), `Flags` (6..2), `RM` (1..0). The FCC bits 31..25, 23 are "R0
... Reserved (Release 6)" (p.92); `Impl` (22..21) is not implemented ("If these bits are not
implemented, they must be ignored on write and read as zero", p.93); bit 20 "Reserved for future use;
reads as zero"; `ABS2008` (19) and `NAN2008` (18) are read-only ("R", p.93-94). -/
def FCSRWritable : W32 := 0x0103FFFF#32

/-- **A write of `v` to FCSR**: the R/W fields take the value, the others ignore the write. -/
def FCSRWrite (v : W32) : W32 := v &&& FCSRWritable

/-- **FCSR as read**: the R/W fields, and `ABS2008` = `NAN2008` = 1 ("1 (Release 6)", Table 6.8,
p.93-94). -/
def FCSRRead (a : Arch) : W32 := (a.FCSR &&& FCSRWritable) ||| 0x000C0000#32

end Manual
