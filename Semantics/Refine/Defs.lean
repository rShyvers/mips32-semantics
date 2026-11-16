import Semantics.Manual.Relation
import Semantics.Step

/-!
# Refine.Defs — the vocabulary of the refinement statements (definitions only)

The top theorems (`Refine/Step.lean`, `Refine/Determinism.lean`, and their restatements in
`Semantics/Statements.lean`) relate the model to the manual specification (`Semantics/Manual/*`)
through the definitions of this file, and only these:

* `abs : State → Manual.Arch`, the model's state seen as the manual's state: a field-by-field
  projection; the register arrays are read with `readReg`/`readFpReg` and the physical-memory map
  with `HashMap.get?` (unwritten bytes read 0);
* `Inv`, the invariant of the reachable states under which `step` refines the manual's instruction
  time (`Good`, `FcsrReservedZero`, `StatusImplemented`).

They are part of the trusted base of those theorems (a wrong `abs` or a vacuous `Inv` would make
them say less). This file holds no theorem; the lemmas about `abs` are in `Refine/Abs.lean`, the
proofs that `Inv` holds at reset and is preserved by `step` in `Refine/Invariant.lean` and
`Refine/Step.lean`. See `docs/MANUAL-SPEC.md` I.5.
-/

namespace Refine

open Manual

/-- The physical memory of the model as a total function (unwritten bytes read 0). -/
def memOf (m : Std.HashMap PAddr UInt8) : PAddr → UInt8 := fun pa => (m.get? pa).getD 0

/-- **The model's state as the manual's state.** -/
def abs (s : State) : Arch where
  PC := s.pc
  GPR := fun i => readReg s i
  FPR := fun i => readFpReg s i
  FCSR := s.fcsr
  Mem := memOf s.physMem
  LLbit := s.llBit
  LLAddr := s.llAddr
  Status := s.cp0Status
  Cause := s.cp0Cause
  EPC := s.cp0Epc
  BadVAddr := s.cp0BadVAddr
  ErrorEPC := s.cp0ErrorEpc
  EBase := s.cp0EBase
  ConfigK0 := s.cp0ConfigK0
  ConfigK23 := s.cp0ConfigK23
  ConfigKU := s.cp0ConfigKU
  Count := s.cp0Count
  Compare := s.cp0Compare
  CauseTI := s.cp0TimerInt
  HWREna := s.cp0HWREna
  HW := s.hwInt
  LowPower := s.standby
  BranchDelay := s.pendingBranch

/-- **The states the refinement is stated for**: both register files have 32 entries
(`State.RegFilesWF`, preserved by `step`, `step_preserves_wellFormed`) and `$zero` reads 0 (preserved
by `step`, `step_preserves_zero_register`). -/
def Good (s : State) : Prop := s.regs.size = 32 ∧ s.fpRegs.size = 32 ∧ readReg s 0 = 0#32

/-- FCSR bits 22..18 read as zero (MD00082 Vol I-A Rev 6.01, Table 6.8, p.93-94: `Impl` 22..21,
bit 20, `ABS2008` 19, `NAN2008` 18; `FIR.Has2008 = 0`).
-- W5: with the Release 6 FPU of this profile `NAN2008 = ABS2008 = 1` read-only (DECISIONS D2). -/
def FcsrReservedZero (s : State) : Prop := s.fcsr &&& 0x007C0000#32 = 0#32

/-- `Status` holds only implemented (writable) bits. -/
def StatusImplemented (s : State) : Prop := s.cp0Status &&& statusWriteMask = s.cp0Status

/-- **The invariant of the reachable states** (each conjunct is needed by some refinement):
* `Good s`: both register files have 32 entries and `$zero` reads 0 (every per-instruction theorem);
* `FcsrReservedZero s`: FCSR bits 22..18 are 0 (`cfc1_refines`: they "read as zero");
* `StatusImplemented s`: `Status` holds only implemented bits (`resetException_refines_manual`).
`step` preserves it, `resetState`, `hostedStart` and `load p` establish it (`Refine/Step.lean`). -/
def Inv (s : State) : Prop := Good s ∧ FcsrReservedZero s ∧ StatusImplemented s

end Refine
