import Semantics.Manual.Relation
import Semantics.Refine.ChoicePoints

/-!
# Refine.Determinism — the model's choices are valid; the manual is deterministic where it makes none

* `modelOracle_valid`: every outcome of `modelOracle` is within the manual's limits
  (`Manual.Oracle.Valid`), so `Manual.Step` with the model's oracle is a behaviour the manual allows.
* `step_refines_manual`: `step` is a `Manual.Step`.
* `manual_step_deterministic`: from a `ChoiceFree` state, all valid oracles give the same instruction
  time (via `instructionTime_oracleFree`; the Operation part is `operation_choiceFree`,
  `Refine/ChoicePoints.lean`).
* The other direction, proved for the `Cause.CE` choice only: `gep_causeCE_choice` (every exception
  other than Coprocessor Unusable gives two different `Cause` values under two valid oracles) and
  `interrupt_choice_exists` (an interrupt is a real choice). The full other direction, every row of
  `ConsultsOracle` included, is `choiceFree_exact` (`Refine/ChoiceExact.lean`).
-/

namespace Refine

open Manual

/-! ## The model's choices are valid -/

set_option linter.unusedSimpArgs false in
/-- A quiet NaN widened by the IEEE core (`CVT.D.S`) is a quiet NaN. -/
theorem qnan32_to64 (x : BitVec 32) (h : Mips.Fp.isQNaN32 x = true) :
    Mips.Fp.isQNaN64 (Mips.Fp.f32ToF64 false x).1 = true := by
  open Mips.Fp in
  simp only [isQNaN32, isQNaN64, f32ToF64, Format.withFlush, Format.flushIn, Bool.false_and, Bool.false_eq_true, ite_false,
    Format.quiet, Format.convert, Format.convertNaN, Format.isQNaN, Format.isNaN,
    Format.isSNaN, Format.expField, Format.fracField, Format.expMax, Format.pack, Format.signBit,
    Format.defaultQNaN, binary32, binary64, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h ⊢
  have hx := x.isLt
  generalize x.toNat = n at *
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLeDiff] at *
  simp only [h1, h2, h3, not_false_eq_true, and_self, ite_true, Nat.reduceEqDiff, ite_false,
    BitVec.toNat_ofNat, Bool.false_eq_true]
  repeat' split
  all_goals (try simp only [Nat.reducePow, Nat.reduceAdd, and_false, not_false_eq_true] at *)
  all_goals (first | omega | decide)

set_option linter.unusedSimpArgs false in
/-- A quiet NaN narrowed by the IEEE core (`CVT.S.D`) is a quiet NaN. -/
theorem qnan64_to32 (e : Mips.Fp.Env) (x : BitVec 64) (h : Mips.Fp.isQNaN64 x = true) :
    Mips.Fp.isQNaN32 (Mips.Fp.f64ToF32 e x).1 = true := by
  have hn : Mips.Fp.binary64.isNaN x.toNat = true := by
    revert h; simp only [Mips.Fp.isQNaN64, Mips.Fp.Format.isQNaN, Bool.and_eq_true]; exact fun h => h.1
  simp only [Mips.Fp.f64ToF32, Mips.Fp.Format.withFlush,
    Mips.Fp.Format.flushIn_of_isNaN _ e.flush _ (by decide) hn]
  open Mips.Fp in
  simp only [isQNaN32, isQNaN64, Format.quiet, Format.convert, Format.convertNaN, Format.isQNaN, Format.isNaN,
    Format.isSNaN, Format.expField, Format.fracField, Format.expMax, Format.pack, Format.signBit,
    Format.defaultQNaN, binary32, binary64, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h ⊢
  have hx := x.isLt
  generalize x.toNat = n at *
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLeDiff] at *
  simp only [h1, h2, h3, not_false_eq_true, and_self, ite_true, Nat.reduceEqDiff, ite_false,
    BitVec.toNat_ofNat, Bool.false_eq_true]
  repeat' split
  all_goals (try simp only [Nat.reducePow, Nat.reduceAdd, and_false, not_false_eq_true] at *)
  all_goals (first | omega | decide)

/-- The model's `extOutOfRange`, `insLsbAboveMsb`, `unpredictableEncoding`
outcomes do not name the state; its `badInstrNoWord`, `badInstrP` values are constants; its `divByZero` value does not name the state; its `fprUpper` value
is a function of the FPRs (accessible); its `.arbitrary` outcomes (`ctc1Unpredictable`) change `FCSR` only, so `LowPower`, the CP0 state, memory and the interrupt inputs `HW` are
unchanged. -/
theorem modelOracle_valid : modelOracle.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  -- restrictions 2 and 3
  · intros; trivial
  · intros; trivial   -- linkSourceIs31: `.proceed`
  · intro a fs t
    simp only [modelOracle]
    repeat' split
    all_goals first
      | trivial
      | exact ⟨rfl, ⟨fun _ _ _ => rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, rfl⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial
  -- restriction 1
  · intro _ _ _ _ _ _; trivial
  · intro _ _ _ _ _ _; trivial   -- linkSourceIs31
  · intro fs t a b _ _ hab
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hab
    simp only [modelOracle]
    repeat' split
    all_goals first
      | exact hab
      | exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      | (refine ⟨h1, h2, h3, ?_, h5, h6, h7, h8, h9, h10⟩; simp only [h4])
      | trivial
      | rfl
  · intro _ _ _ _ _; trivial
  · intro _ _ _ _ _; trivial
  · intro _ _ _ _ _ _; trivial
  · intro r a b _ _ hab; simp only [modelOracle, hab.2.2.1]  -- `fprUpper`
  -- (no `cfc1Unpredictable` value: CFC1 of FRE signals Reserved Instruction)
  -- BadInstr / BadInstrP: constants
  · intro _ _ _ _ _; rfl
  · intro _ _ _ _ _; rfl
  · intro _ _ _ _ _ _; rfl  -- divByZero
  -- UNDEFINED
  · intros; trivial
  -- QNaN
  · exact qnan32_to64
  · exact qnan64_to32 _
  -- Reset
  · intro a; exact ⟨rfl, rfl⟩

-- 12b: with the spec's decoder `Manual.decodeDiagram`
/-- **`step` is an instruction time the manual allows** (`Manual.Step`, with the model's
implementation constants and the spec's decoder), from every state of the invariant. -/
theorem step_refines_manual (s : State) (hg : Inv s) :
    Manual.Step modelImpl decodeDiagram (abs s) (abs (step s)) :=
  ⟨modelOracle, modelOracle_valid, step_eq_manual s hg⟩

/-! ## Determinism at choice-free states -/

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

/-- The faulting instruction word does not depend on the oracle where the fetch delivers a word. -/
theorem faultingWord_oracleFree (i : Impl) (o₁ o₂ : Oracle) (a : Arch) (hf : FetchOK i a = true) :
    FaultingInstructionWord i o₁ a = FaultingInstructionWord i o₂ a := by
  unfold FaultingInstructionWord
  unfold FetchOK at hf
  rw [show ({ impl := i, oracle := o₁ } : Ctx) = ctxOf i o₁ from rfl,
    show ({ impl := i, oracle := o₂ } : Ctx) = ctxOf i o₂ from rfl,
    fetch_oracleFree (ctxOf i o₁) (ctxOf i modelOracle), fetch_oracleFree (ctxOf i o₂) (ctxOf i modelOracle)]
  revert hf
  cases (InstructionFetch.run (ctxOf i modelOracle) { arch := a }).1 <;> intro hf
  · rfl
  · cases hf

/-- A Coprocessor Unusable exception in a delay slot from a state whose fetch delivers a word does
not depend on the oracle (its `Cause.CE` is the unit; `BadInstrP` is the branch). -/
theorem gep_cpu (i : Impl) (o₁ o₂ : Oracle) (u : Nat) (a : Arch) (hs : a.BranchDelay.isSome = true)
    (hf : FetchOK i a = true) :
    GeneralExceptionProcessing i o₁ (.CoprocessorUnusable u) a =
      GeneralExceptionProcessing i o₂ (.CoprocessorUnusable u) a := by
  have hw := faultingWord_oracleFree i o₁ o₂ a hf
  simp only [GeneralExceptionProcessing, AdditionalState, FaultingCoprocessorNumber, hw, hs,
    reduceCtorEq, ↓reduceIte]

theorem execute_oracleFree (i : Impl) (o₁ o₂ : Oracle) (w : W32) (ins : Instruction) (a : Arch)
    (hfa : FetchOK i a = true)
    (h : (!(IsCTI ins && a.BranchDelay.isSome) &&
          (if InCop1Space w && !StatusCU1 a then a.BranchDelay.isSome
           else if InCop0Space w && !CP0Usable a then a.BranchDelay.isSome
           else
             !ConsultsOracle ins a &&
               match Operation ins with
               | none => true
               | some op =>
                 match op.run (ctxOf i modelOracle) { arch := a } with
                 | (.ok (), _) => true
                 | (.signal (.CoprocessorUnusable _), g) => g.arch.BranchDelay.isSome && FetchOK i g.arch
                 | (.signal _, _) => false)) = true) :
    Execute (ctxOf i o₁) w ins a = Execute (ctxOf i o₂) w ins a := by
  have e1 := fun hh => operation_choiceFree ins a hh i o₁ modelOracle
  have e2 := fun hh => operation_choiceFree ins a hh i o₂ modelOracle
  cases hbc : (IsCTI ins && a.BranchDelay.isSome)
  · rw [hbc] at h
    unfold Execute
    simp only [hbc, Bool.false_eq_true, ite_false]
    revert h e1 e2
    unfold Execute.runOperation
    generalize (InCop1Space w && !StatusCU1 a) = b1
    generalize (InCop0Space w && !CP0Usable a) = b0
    generalize ConsultsOracle ins a = bo
    intro h e1 e2
    cases b1
    · cases b0
      · cases bo
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
                | (simp only [Bool.and_eq_true] at h
                   exact congrArg some (gep_cpu i o₁ o₂ _ f.arch h.1 h.2))
        · simp at h
      · simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ite_true, ite_false] at h ⊢
        exact congrArg some (gep_cpu i o₁ o₂ _ a h hfa)
    · simp only [Bool.not_false, Bool.true_and, ite_true] at h ⊢
      exact congrArg some (gep_cpu i o₁ o₂ _ a h hfa)
  · rw [hbc] at h; simp at h

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
  congr 1
  show FetchExecute (ctxOf i o₁) dec a = FetchExecute (ctxOf i o₂) dec a
  unfold FetchExecute
  rw [fetch_oracleFree (ctxOf i o₁) (ctxOf i modelOracle), fetch_oracleFree (ctxOf i o₂) (ctxOf i modelOracle)]
  revert h
  rcases hR : InstructionFetch.run (ctxOf i modelOracle) { arch := a } with ⟨r, f⟩
  rcases r with w | e
  · have hfa : FetchOK i a = true := by unfold FetchOK; rw [hR]
    simp only
    cases hd : dec w with
    | none =>
      intro h
      simp only
      by_cases hu : UnpredictableEncoding w = true
      · simp only [hu, ite_true, Bool.and_eq_true] at h ⊢
        obtain ⟨hc, hs⟩ := h
        congr 1
        unfold Unpredictable
        by_cases h1 : (InCop1Space w && !StatusCU1 a) = true
        · simp only [h1, ite_true]; exact gep_cpu i o₁ o₂ _ a hs hfa
        · by_cases h0 : (InCop0Space w && !CP0Usable a) = true
          · simp only [h1, h0, ite_true, Bool.false_eq_true, ite_false]; exact gep_cpu i o₁ o₂ _ a hs hfa
          · simp only [h1, h0, Bool.or_self, Bool.false_eq_true] at hc
      · simp only [hu, Bool.false_eq_true, ite_false] at h ⊢
        revert h
        cases Undecodable w a <;> intro hc <;> first
          | exact absurd hc Bool.false_ne_true
          | exact congrArg some (gep_cpu i o₁ o₂ _ a hc hfa)
    | some ins =>
      intro h
      exact execute_oracleFree i o₁ o₂ w ins a hfa h
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
    (h : ChoiceFree modelImpl decodeDiagram (abs s) = true) (a' : Arch)
    (h' : Manual.Step modelImpl decodeDiagram (abs s) a') : a' = abs (step s) :=  -- 12b
  manual_step_deterministic _ _ _ _ _ h h' (step_refines_manual s hg)

/-! ## The other direction: choices that matter -/

/-- The model's oracle with `Cause.CE` loaded with 1 instead of 0 for the exceptions other than
Coprocessor Unusable: a valid oracle too (`causeCE` is not restricted). -/
def modelOracleCE1 : Oracle := { modelOracle with causeCE := fun _ _ => 1#2 }

theorem modelOracleCE1_valid : modelOracleCE1.Valid := modelOracle_valid

/-- **`Cause.CE` is a real choice**: for every exception other than Coprocessor Unusable, two valid
oracles give different `Cause` registers after the general exception processing (MD00090 Vol III
Rev 6.02 §6.2.3, p.87: "The CE field is loaded, but not defined"). -/
theorem gep_causeCE_choice (i : Impl) (e : Exception) (a : Arch)
    (he : ∀ u, e ≠ .CoprocessorUnusable u) :
    (GeneralExceptionProcessing i modelOracle e a).Cause ≠
      (GeneralExceptionProcessing i modelOracleCE1 e a).Cause := by
  intro h
  have := congrArg (fun x => BitVec.getLsbD x 28) h
  cases e <;> first
    | exact absurd rfl (he _)
    | simp [GeneralExceptionProcessing, FaultingCoprocessorNumber, modelOracle, modelOracleCE1] at this

/-- **An interrupt is a choice point** (two valid oracles give different instruction times). -/
theorem interrupt_not_choiceFree (i : Impl) (dec : W32 → Option Instruction) (a : Arch)
    (h : InterruptTaken i a = true) :
    InstructionTime i modelOracle dec a ≠ InstructionTime i modelOracleCE1 dec a := by
  intro he
  simp only [InstructionTime, h, ite_true, Option.map_some, Option.some.injEq] at he
  have hc := congrArg Arch.Cause he
  simp only [TimerTick] at hc
  exact gep_causeCE_choice i .Interrupt a (fun _ h => nomatch h) hc
/-- **`ChoiceFree` is exact at an interrupt**: when an interrupt is taken (`ChoiceFree` is `false`),
two valid resolutions of the manual's choices give different instruction times. -/
theorem interrupt_choice_exists (i : Impl) (dec : W32 → Option Instruction) (a : Arch)
    (h : InterruptTaken i a = true) :
    ∃ o₁ o₂ : Oracle, o₁.Valid ∧ o₂.Valid ∧
      InstructionTime i o₁ dec a ≠ InstructionTime i o₂ dec a :=
  ⟨modelOracle, modelOracleCE1, modelOracle_valid, modelOracleCE1_valid,
    interrupt_not_choiceFree i dec a h⟩

end Refine
