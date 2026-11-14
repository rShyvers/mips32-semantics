import Semantics.Manual.Relation
import Semantics.Refine.Step

/-!
# Refine.Determinism — the model's choices are valid; the manual is deterministic where it makes none (7D)

* `modelOracle_valid`: every outcome of `modelOracle` is within the manual's limits
  (`Manual.Oracle.Valid`), so `Manual.Step` with the model's oracle is a behaviour the manual allows.
* `step_refines_manual`: `step` is a `Manual.Step`.
* `manual_step_deterministic`: from a `ChoiceFree` state, all valid oracles give the same instruction
  time.
-/

namespace Refine

open Manual

/-! ## The model's choices are valid -/

theorem modelOracle_valid : modelOracle.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a i; simp only [modelOracle]; split <;> trivial
  all_goals first
    | (intros; trivial)
    | (intro a r v
       refine ⟨rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
         fun _ _ => rfl⟩⟩)
    | (intro a fs t
       refine ⟨rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
         fun _ _ => rfl⟩⟩)
    | (intro a; exact ⟨rfl, rfl⟩)

/-- **`step` is an instruction time the manual allows** (`Manual.Step`, with the model's
implementation constants and decoder), from every state of the invariant. -/
theorem step_refines_manual (s : State) (hg : Inv s) :
    Manual.Step modelImpl decode (abs s) (abs (step s)) :=
  ⟨modelOracle, modelOracle_valid, step_eq_manual s hg⟩

/-! ## Determinism at choice-free states -/

theorem operation_oracleFree (ins : Instruction) (h : OracleFreeOp ins = true) (i : Impl)
    (o₁ o₂ : Oracle) (f : Frame) :
    (Operation ins).map (fun p => p.run (ctxOf i o₁) f) =
      (Operation ins).map (fun p => p.run (ctxOf i o₂) f) := by
  cases ins <;> simp only [OracleFreeOp, Bool.false_eq_true] at h <;> rfl

theorem load_instr (cca : BitVec 3) (n : Nat) (pa va : W32) (c : Ctx) (f : Frame) :
    LoadMemory cca n pa va .INSTRUCTION c f = (.ok (MemElemAt f.arch.Mem pa), f) := rfl
theorem addr_ctx (va : W32) (i : IorD) (l : LorS) (c1 c2 : Ctx) (f : Frame) :
    AddressTranslation va i l c1 f = AddressTranslation va i l c2 f := by
  obtain ⟨a, p, d⟩ := f
  simp only [AddressTranslation, bind, Pseudo.get, memory_address]
  by_cases hb : (UserMode a && bit va 31) = true
  · simp only [hb, ↓reduceIte]; cases l <;> rfl
  · rw [Bool.not_eq_true] at hb
    simp only [hb, Bool.false_eq_true, ↓reduceIte]; rfl
theorem fetch_oracleFree (c1 c2 : Ctx) (a : Arch) :
    InstructionFetch.run c1 { arch := a } = InstructionFetch.run c2 { arch := a } := by
  simp only [Pseudo.run, InstructionFetch, bind, PC]
  split
  · rfl
  · dsimp only
    rw [addr_ctx _ _ _ c1 c2]
    split <;> simp only [load_instr]

theorem gep_cpu (i : Impl) (o₁ o₂ : Oracle) (u : Nat) (a : Arch) :
    GeneralExceptionProcessing i o₁ (.CoprocessorUnusable u) a =
      GeneralExceptionProcessing i o₂ (.CoprocessorUnusable u) a := rfl

theorem execute_oracleFree (i : Impl) (o₁ o₂ : Oracle) (w : W32) (ins : Instruction) (a : Arch)
    (h : (!(IsCTI ins && a.BranchDelay.isSome) &&
          (if InCop1Space w && !StatusCU1 a then true
           else if InCop0Space w && !CP0Usable a then true
           else
             OracleFreeOp ins &&
               match Operation ins with
               | none => true
               | some op =>
                 match op.run (ctxOf i modelOracle) { arch := a } with
                 | (.ok (), _) => true
                 | (.signal (.CoprocessorUnusable _), _) => true
                 | (.signal _, _) => false)) = true) :
    Execute (ctxOf i o₁) w ins a = Execute (ctxOf i o₂) w ins a := by
  have e1 := fun hh => operation_oracleFree ins hh i o₁ modelOracle { arch := a }
  have e2 := fun hh => operation_oracleFree ins hh i o₂ modelOracle { arch := a }
  revert h e1 e2
  unfold Execute Execute.runOperation
  dsimp only
  generalize (IsCTI ins && a.BranchDelay.isSome) = bc
  generalize (InCop1Space w && !StatusCU1 a) = b1
  generalize (InCop0Space w && !CP0Usable a) = b0
  generalize OracleFreeOp ins = bo
  intro h e1 e2
  cases bc
  · cases b1
    · cases b0
      · cases bo
        · simp at h
        · simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ite_false] at h ⊢
          have e1 := e1 rfl; have e2 := e2 rfl
          revert h e1 e2
          cases Operation ins with
          | none => intros; rfl
          | some op =>
            simp only [Option.map_some, Option.some.injEq]
            intro h e1 e2
            simp only [Pseudo.run] at e1 e2 h ⊢
            rw [e1, e2]
            revert h
            rcases op (ctxOf i modelOracle) { arch := a } with ⟨r, f⟩
            rcases r with ⟨⟩ | e
            · intro; rfl
            · cases e <;> intro h <;> first
                | exact absurd h Bool.false_ne_true
                | rfl
      · rfl
    · rfl
  · simp at h

/-- **From a choice-free state, the instruction time does not depend on the oracle.** -/
theorem instructionTime_oracleFree (i : Impl) (dec : W32 → Option Instruction) (a : Arch)
    (h : ChoiceFree i dec a = true) (o₁ o₂ : Oracle) :
    InstructionTime i o₁ dec a = InstructionTime i o₂ dec a := by
  unfold ChoiceFree at h
  unfold InstructionTime
  by_cases hi : InterruptTaken i a = true
  · simp only [hi, ite_true] at h; cases h
  simp only [hi, Bool.false_eq_true, ite_false] at h ⊢
  by_cases hl : a.LowPower = true
  · simp only [hl, ite_true]
  simp only [hl, Bool.false_eq_true, ite_false] at h ⊢
  by_cases hn : a.Nullify = true
  · simp only [hn, ite_true]
  simp only [hn, Bool.false_eq_true, ite_false] at h ⊢
  congr 1
  show FetchExecute (ctxOf i o₁) dec a = FetchExecute (ctxOf i o₂) dec a
  unfold FetchExecute
  rw [fetch_oracleFree (ctxOf i o₁) (ctxOf i modelOracle), fetch_oracleFree (ctxOf i o₂) (ctxOf i modelOracle)]
  revert h
  rcases InstructionFetch.run (ctxOf i modelOracle) { arch := a } with ⟨r, f⟩
  rcases r with w | e
  · simp only
    cases hd : dec w with
    | none =>
      intro h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hu, hc⟩ := h
      simp only [hu, Bool.false_eq_true, ite_false]
      revert hc
      cases Undecodable w a <;> intro hc <;> first
        | exact absurd hc Bool.false_ne_true
        | exact congrArg some (gep_cpu i o₁ o₂ _ a)
    | some ins =>
      intro h
      exact execute_oracleFree i o₁ o₂ w ins a h
  · intro h; cases h

/-- **The manual is deterministic at a choice-free state**: all valid resolutions of the choices
give the same next state. -/
theorem manual_step_deterministic (i : Impl) (dec : W32 → Option Instruction) (a a₁ a₂ : Arch)
    (h : ChoiceFree i dec a = true) (h₁ : Manual.Step i dec a a₁) (h₂ : Manual.Step i dec a a₂) :
    a₁ = a₂ := by
  obtain ⟨o₁, -, e₁⟩ := h₁
  obtain ⟨o₂, -, e₂⟩ := h₂
  rw [instructionTime_oracleFree i dec a h o₁ o₂, e₂] at e₁
  exact (Option.some.inj e₁).symm

/-- **At a choice-free state, `step` is the only instruction time the manual allows.** -/
theorem step_unique_of_choiceFree (s : State) (hg : Inv s)
    (h : ChoiceFree modelImpl decode (abs s) = true) (a' : Arch)
    (h' : Manual.Step modelImpl decode (abs s) a') : a' = abs (step s) :=
  manual_step_deterministic _ _ _ _ _ h h' (step_refines_manual s hg)

end Refine
