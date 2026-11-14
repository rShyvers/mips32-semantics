import Semantics.Refine.Instr
import Semantics.Manual.Relation
import Semantics.Refine.Decode
import Semantics.Specs.RegFileSize
import Semantics.Specs.Invariants
import Semantics.Env

/-!
# Refine.Step — `step` refines the manual's instruction time (7D)

The assembly of the independent correctness theorem:

* **The invariant** `Inv` (`Refine/Instr.lean`: `Good`, `FcsrReservedZero`, `StatusImplemented`).
  No path of the cycle needs anything else (`s.nullified = false` on the execute path comes from
  `stepCore`'s own case split, `enc i = some w` from `decode_enc`). `step` preserves it
  (`step_preserves_inv`), `resetState`, `hostedStart` and `load p` establish it.
* **The paths** (`Refine/Cycle.lean`) and the per-instruction hypothesis (`Refine/Instr.lean`),
  assembled: `stepCore_abs`, `step_eq_manual_of`.
* **The top theorems**, stated from `PendingRefines` (the per-instruction refinements of the
  constructors not yet covered): `step_eq_manual`, `step_refines_manual`, `run_refines_manual`,
  and the reset theorems (unconditional).
-/

namespace Refine

open Manual

/-! ## The invariant -/

theorem step_preserves_good (s : State) (h : Good s) : Good (step s) := by
  obtain ⟨h1, h2, h0⟩ := h
  obtain ⟨e1, e2⟩ := step_preserves_regfile_sizes s
  exact ⟨e1.trans h1, e2.trans h2, (step_preserves_zero_register s).trans h0⟩

/-- **`step` preserves the invariant.** -/
theorem step_preserves_inv (s : State) (h : Inv s) : Inv (step s) :=
  ⟨step_preserves_good s h.1, step_preserves_fcsrReservedZero s h.2.1,
    step_preserves_statusImplemented s h.2.2⟩

theorem run_preserves_inv (s : State) (n : Nat) (h : Inv s) : Inv (run s n) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih _ (step_preserves_inv s h)

theorem resetException_inv (s : State) (h : Inv s) : Inv (resetException s) :=
  ⟨h.1, resetException_fcsrReservedZero s h.2.1, resetException_statusImplemented s h.2.2⟩

theorem inv_resetState : Inv resetState :=
  ⟨⟨by decide, by decide, by decide⟩, resetState_fcsrReservedZero, resetState_statusImplemented⟩

theorem inv_hostedStart : Inv hostedStart :=
  ⟨⟨by decide, by decide, by decide⟩, hostedStart_fcsrReservedZero, hostedStart_statusImplemented⟩

/-- **The loader establishes the invariant.** -/
theorem inv_load (p : Program) : Inv (load p) :=
  ⟨inv_hostedStart.1, load_fcsrReservedZero p, load_statusImplemented p⟩

/-! ## Assembly -/

/-- **Fetch, decode, execute** (`Manual.FetchExecute` under the model's choices, with the model's
`decode`) is the model's `execute`, given the per-instruction refinements. -/
theorem execute_abs (s : State) (hg : Inv s) (hn : s.nullified = false)
    (hI : ∀ i, InstrRefines i) :
    FetchExecute modelCtx decode (abs s) = some (abs (execute s)) := by
  unfold FetchExecute
  rw [fetch_run]
  unfold execute
  cases hf : readMemWord s s.pc with
  | none => exact congrArg some (fetchError_abs s)
  | some w =>
    simp only
    cases hd : decode w with
    | none =>
      simp only
      rw [← undecodable_abs s w hd]
      cases UnpredictableEncoding w <;> rfl
    | some i => exact hI i s w hg hn hd (decode_enc w i hd)

/-- **The processor's part of the instruction time** (`Manual.InstructionTime` before the timer)
is `stepCore`. -/
theorem stepCore_abs (s : State) (hg : Inv s) (hI : ∀ i, InstrRefines i) :
    (if InterruptTaken modelImpl (abs s) then
        some { GeneralExceptionProcessing modelImpl modelOracle .Interrupt (abs s) with
          LowPower := false }
      else if (abs s).LowPower then some (LowPowerTime modelImpl (abs s))
      else if (abs s).Nullify then
        some { abs s with PC := (abs s).PC + 4#32, BranchDelay := none, Nullify := false }
      else FetchExecute modelCtx decode (abs s)) = some (abs (stepCore s)) := by
  rw [interruptTaken_abs]
  unfold stepCore
  cases hi : interruptTaken s
  · simp only [Bool.false_eq_true, ite_false]
    show (if s.standby then _ else _) = _
    cases hs : s.standby
    · simp only [Bool.false_eq_true, ite_false]
      show (if s.nullified then _ else _) = _
      cases hn : s.nullified
      · simp only [Bool.false_eq_true, ite_false]
        exact execute_abs s hg hn hI
      · simp only [ite_true]; rfl
    · simp only [ite_true]; rw [standbyStep_abs]
  · simp only [ite_true]; rw [takeInterrupt_abs s hi]

/-- **`step` refines one instruction time of the manual**, given the per-instruction refinement
of every instruction. -/
theorem step_eq_manual_of (s : State) (hg : Inv s) (hI : ∀ i, InstrRefines i) :
    InstructionTime modelImpl modelOracle decode (abs s) = some (abs (step s)) := by
  have h := stepCore_abs s hg hI
  unfold InstructionTime
  simp only
  rw [show ({ impl := modelImpl, oracle := modelOracle } : Ctx) = modelCtx from rfl, h]
  simp only [Option.map_some, step, timerTick_abs]

/-! ## The top theorems (conditional on the pending per-instruction refinements) -/

/-- **`step` is one instruction time of the manual** under the model's implementation constants and
choices (`modelImpl`, `modelOracle`), with the model's `decode` as the spec's decoder
(`Manual.DecoderSound decode`, `decoderSound_decode`), from every state of the invariant. Stated
from `PendingRefines` until the per-instruction theorems of every constructor exist. -/
theorem step_eq_manual (hP : PendingRefines) (s : State) (hg : Inv s) :
    InstructionTime modelImpl modelOracle decode (abs s) = some (abs (step s)) :=
  step_eq_manual_of s hg (allInstrRefines_of hP)

/-- **`run` is a sequence of instruction times of the manual** (`Manual.InstructionTimes`). -/
theorem run_refines_manual (hP : PendingRefines) (s : State) (hg : Inv s) (n : Nat) :
    InstructionTimes modelImpl modelOracle decode n (abs s) = some (abs (run s n)) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [InstructionTimes, step_eq_manual hP s hg, Option.bind_some]
    exact ih (step s) (step_preserves_inv s hg)

/-! ## Reset -/

/-- **The Reset exception**: `resetException` is `Manual.ResetException` under the model's choices,
from every state whose `Status` holds only implemented bits. -/
theorem resetException_refines_manual (s : State) (h : StatusImplemented s) :
    abs (resetException s) = ResetException modelOracle (abs s) := by
  unfold StatusImplemented at h
  simp only [ResetException, modelOracle, statusWritable_eq]
  simp only [abs, resetException, h]
  rfl

theorem powerOn_statusImplemented : StatusImplemented powerOnState := by
  unfold StatusImplemented; decide

/-- **The state after a cold reset** is the manual's Reset exception applied to the power-on
state. -/
theorem resetState_refines_manual :
    abs resetState = ResetException modelOracle (abs powerOnState) :=
  resetException_refines_manual _ powerOn_statusImplemented

end Refine
