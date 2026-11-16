import Semantics.Refine.Instr
import Semantics.Manual.Relation
import Semantics.Refine.Decode
import Semantics.Refine.DecodeBridge  -- 12b
import Semantics.Specs.RegFileSize
import Semantics.Specs.Invariants
import Semantics.Env

/-!
# Refine.Step — `step` refines the manual's instruction time (7D)

The assembly of the independent correctness theorem:

* **The invariant** `Inv` (`Refine/Defs.lean`: `Good`, `FcsrReservedZero`, `StatusImplemented`).
  No path of the cycle needs anything else (`enc i = some w` comes from `decode_enc`). `step` preserves it
  (`step_preserves_inv`), `resetState`, `hostedStart` and `load p` establish it.
* **The paths** (`Refine/Cycle.lean`) and the per-instruction refinements of all 122 constructors
  (`allInstrRefines`, `Refine/Instr.lean`), assembled: `execute_abs`, `stepCore_abs`.
* **The top theorems**, unconditional on every state of the invariant: `step_eq_manual`,
  `run_refines_manual`, and the reset theorems (`step_refines_manual` and the determinism results
  are in `Refine/Determinism.lean`).
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
`decode`) is the model's `execute`. -/
theorem execute_abs (s : State) (hg : Inv s) :
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
    | some i => exact allInstrRefines i s w hg hd (decode_enc w i hd)

/-- **The processor's part of the instruction time** (`Manual.InstructionTime` before the timer)
is `stepCore`. -/
theorem stepCore_abs (s : State) (hg : Inv s) :
    (if InterruptTaken modelImpl (abs s) then
        some { GeneralExceptionProcessing modelImpl modelOracle .Interrupt (abs s) with
          LowPower := false }
      else if (abs s).LowPower then some (LowPowerTime modelImpl (abs s))
      else FetchExecute modelCtx decode (abs s)) = some (abs (stepCore s)) := by
  rw [interruptTaken_abs]
  unfold stepCore
  cases hi : interruptTaken s
  · simp only [Bool.false_eq_true, ite_false]
    show (if s.standby then _ else _) = _
    cases hs : s.standby
    · simp only [Bool.false_eq_true, ite_false]
      exact execute_abs s hg
    · simp only [ite_true]; rw [standbyStep_abs]
  · simp only [ite_true]; rw [takeInterrupt_abs s hi]

/-! ## The top theorems -/

-- 12b: the top theorems take the spec's own decoder `Manual.decodeDiagram` (`Manual/Decode.lean`);
-- the `_decode` versions, with the model's `decode`, are the step to them.
/-- `step` is one instruction time of the manual with the model's `decode` as the decoder. -/
theorem step_eq_manual_decode (s : State) (hg : Inv s) :
    InstructionTime modelImpl modelOracle decode (abs s) = some (abs (step s)) := by
  have h := stepCore_abs s hg
  unfold InstructionTime
  simp only
  rw [show ({ impl := modelImpl, oracle := modelOracle } : Ctx) = modelCtx from rfl, h]
  simp only [Option.map_some, step, timerTick_abs]

/-- **`step` is one instruction time of the manual** under the model's implementation constants and
choices (`modelImpl`, `modelOracle`), with the spec's own decoder `Manual.decodeDiagram` (the format
diagrams, `Manual/Decode.lean`; the model's `decode` agrees with it, `decode_agrees`,
`decode_none_rejected`), from every state of the invariant. -/
theorem step_eq_manual (s : State) (hg : Inv s) :
    InstructionTime modelImpl modelOracle decodeDiagram (abs s) = some (abs (step s)) := by
  rw [instructionTime_diagram]; exact step_eq_manual_decode s hg

/-- **`run` is a sequence of instruction times of the manual** (`Manual.InstructionTimes`), with the
spec's decoder. -/
theorem run_refines_manual (s : State) (hg : Inv s) (n : Nat) :
    InstructionTimes modelImpl modelOracle decodeDiagram n (abs s) = some (abs (run s n)) := by
  rw [instructionTimes_diagram]
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [InstructionTimes, step_eq_manual_decode s hg, Option.bind_some]
    exact ih (step s) (step_preserves_inv s hg)
-- end 12b

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
