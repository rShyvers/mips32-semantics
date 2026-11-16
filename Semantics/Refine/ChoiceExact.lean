import Semantics.Refine.ChoiceRowsFp

/-!
# Refine.ChoiceExact — `ChoiceFree` is exact

`choiceFree_exact`: at every state where `Manual.ChoiceFree modelImpl dec a` is `false`, two valid
oracles give different instruction times. With `manual_step_deterministic` (the other direction,
`Refine/Determinism.lean`), `ChoiceFree modelImpl dec a = true` holds exactly when all valid oracles
give the same instruction time (`choiceFree_iff`).

The cases of `ChoiceFree`:
* an interrupt: `interrupt_choice_exists`;
* an exception other than Coprocessor Unusable (instruction fetch, a word matching no diagram, a word
  with an UNPREDICTABLE field value, a CTI in a delay slot, an Operation that signals): two witness
  oracles with different `Cause.CE` (`gep_CE`; MD00090 Vol III Rev 6.02 §6.2.3, p.87);
* `ConsultsOracle ins a = true`: `consults_row` (the rows, `Refine/ChoiceRows*.lean`).

The witness oracles are `wo p (ceA a)` and `wo p' (ceB a)` (`Refine/ChoiceWitness.lean`): every
`Cause.CE` involved differs from the two others, so a signalled exception is told apart from another
signalled exception and from a completed instruction.
-/

namespace Refine

open Manual

/-- Every constructor has an Operation. -/
theorem operation_some (ins : Instruction) : ∃ op, Operation ins = some op := by
  cases ins <;> exact ⟨_, rfl⟩

set_option linter.unusedSimpArgs false in
/-- **Every row of `ConsultsOracle` is a real choice.** -/
theorem consults_row (ins : Instruction) (a : Arch) (h : ConsultsOracle ins a = true) : RowWitness ins a := by
  cases ins
  -- A 32-bit result stored into a 64-bit FPR (`fprUpper`): `fpr32_row` with the destination FPR.
  case lwc1 _ ft _ | mtc1 _ ft | cmpS _ ft _ _ => fpr32_row ft
  case movS fd _ | absS fd _ | negS fd _ | addS fd _ _ | subS fd _ _ | mulS fd _ _ | divS fd _ _
    | sqrtS fd _ | recipS fd _ | rsqrtS fd _ | roundWS fd _ | truncWS fd _ | ceilWS fd _
    | floorWS fd _ | cvtWS fd _ | roundWD fd _ | truncWD fd _ | ceilWD fd _ | floorWD fd _
    | cvtWD fd _ | cvtSD fd _ | cvtSW fd _ | cvtSL fd _ | selS fd _ _ | seleqzS fd _ _
    | selnezS fd _ _ | maddfS fd _ _ | msubfS fd _ _ | maxS fd _ _ | minS fd _ _ | maxaS fd _ _
    | minaS fd _ _ | classS fd _ | rintS fd _ => fpr32_row fd
  -- A compact branch-and-link with `rt = 31`: the witness oracle signals (`row_sig`).
  case blezalc | bgezalc | bgtzalc | bltzalc | beqzalc | bnezalc =>
    simp only [ConsultsOracle, beq_iff_eq] at h
    exact row_sig rfl fun _ => by
      simp only [Ops.BLEZALC, Ops.BGEZALC, Ops.BGTZALC, Ops.BLTZALC, Ops.BEQZALC, Ops.BNEZALC, Ops.BZALC]
      runp
  -- Every other row has its own `rw_<ctor>` (`Refine/ChoiceRows*.lean`); for a constructor without
  -- one, `ConsultsOracle` is `false` and `h` is a contradiction.
  all_goals apply_ctor_lemma "rw_" "" else simp [ConsultsOracle] at h

/-! ## Telling two instruction times apart -/

/-- Two states differ in `Cause.CE`, in `Obs`, or (Release 6) in `BadInstrP` or `BadInstr`. -/
def Sep (x y : Arch) : Prop :=
  CEof x ≠ CEof y ∨ Obs x ≠ Obs y ∨ x.BadInstrP ≠ y.BadInstrP ∨ x.BadInstr ≠ y.BadInstr

theorem sep_ne (i : Impl) (x y : Arch) (h : Sep x y) : some (TimerTick i x) ≠ some (TimerTick i y) := by
  intro he; have he := Option.some.inj he
  rcases h with h | h | h | h
  · apply h; rw [← ce_timerTick i x, ← ce_timerTick i y, he]
  · apply h; rw [← obs_timerTick i x, ← obs_timerTick i y, he]
  · apply h; exact (congrArg Arch.BadInstrP he :)
  · apply h; exact (congrArg Arch.BadInstr he :)

/-- Two witness oracles that differ in `badInstrP`: an exception other than the Interrupt outside a
delay slot is told apart by `BadInstrP` (MD00090 Vol III Rev 6.02 §9.26, p.181). -/
theorem sep_bip (i : Impl) (e : Exception) (x : Arch) (he : e ≠ .Interrupt)
    (hs : x.BranchDelay.isSome = false) (ce₁ ce₂ : BitVec 2) :
    Sep (GeneralExceptionProcessing i (wo { bip := 0#32 } ce₁) e x)
      (GeneralExceptionProcessing i (wo { bip := 1#32 } ce₂) e x) := by
  right; right; left
  rw [gep_badInstrP i _ _ e x he hs, gep_badInstrP i _ _ e x he hs]; decide

/-- Two witness oracles that differ in `badInstrNoWord`: an exception other than the Interrupt from a
state whose fetch fails is told apart by `BadInstr` (§9.25, p.179). -/
theorem sep_bnw (i : Impl) (e : Exception) (x : Arch) (he : e ≠ .Interrupt)
    (hf : FetchOK i x = false) (ce₁ ce₂ : BitVec 2) :
    Sep (GeneralExceptionProcessing i (wo { bnw := 0#32 } ce₁) e x)
      (GeneralExceptionProcessing i (wo { bnw := 1#32 } ce₂) e x) := by
  right; right; right
  rw [gep_badInstr i _ _ e x he hf, gep_badInstr i _ _ e x he hf]; decide

theorem it_eq (o : Oracle) (dec : W32 → Option Instruction) (a : Arch) (hi : InterruptTaken modelImpl a = false)
    (hl : a.LowPower = false) :
    InstructionTime modelImpl o dec a = (FetchExecute (ctxOf modelImpl o) dec a).map (TimerTick modelImpl) := by
  simp only [InstructionTime, hi, hl, Bool.false_eq_true, ↓reduceIte]; rfl

/-- Two witness oracles whose fetch-and-execute results are separated give different instruction
times. -/
theorem exact_of (dec : W32 → Option Instruction) (a : Arch) (hi : InterruptTaken modelImpl a = false)
    (hl : a.LowPower = false) (p₁ p₂ : WP) (x y : Arch)
    (h₁ : FetchExecute (ctxOf modelImpl (wo p₁ (ceA a))) dec a = some x)
    (h₂ : FetchExecute (ctxOf modelImpl (wo p₂ (ceB a))) dec a = some y) (hs : Sep x y) :
    ∃ o₁ o₂ : Oracle, o₁.Valid ∧ o₂.Valid ∧
      InstructionTime modelImpl o₁ dec a ≠ InstructionTime modelImpl o₂ dec a :=
  ⟨_, _, wo_valid p₁ (ceA a), wo_valid p₂ (ceB a), by
    rw [it_eq _ dec a hi hl, it_eq _ dec a hi hl, h₁, h₂]; exact sep_ne _ x y hs⟩

theorem sep_gep (a : Arch) (p₁ p₂ : WP) (e₁ e₂ : Exception) (x y : Arch) (h₁ : NotCpU e₁) (h₂ : NotCpU e₂) :
    Sep (GeneralExceptionProcessing modelImpl (wo p₁ (ceA a)) e₁ x)
      (GeneralExceptionProcessing modelImpl (wo p₂ (ceB a)) e₂ y) := by
  left; rw [gep_CE _ _ _ _ _ h₁, gep_CE _ _ _ _ _ h₂]; exact ceA_ne_ceB a

theorem notCpU_RI : NotCpU .ReservedInstruction := fun _ h => nomatch h

/-- The instruction fetch signals Address Error only. -/
theorem fetch_notCpU (c : Ctx) (a : Arch) (e : Exception) (f : Frame)
    (h : InstructionFetch.run c { arch := a } = (.signal e, f)) : NotCpU e := by
  revert h
  simp only [Pseudo.run, InstructionFetch, bind, PC, AddressTranslation, Pseudo.get, SignalException, pure,
    LoadMemory, Pseudo.oracle, Pseudo.modify, ite_app2]
  by_cases h1 : (bits (memory_address a.PC) 1 0 != 0#2) = true
  · simp only [h1, ↓reduceIte]; intro h; simp only [Prod.mk.injEq, Result.signal.injEq] at h; rw [← h.1]; exact fun _ h => nomatch h
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (UserMode a && bit (memory_address (memory_address a.PC)) 31) = true
    · simp only [h2, ↓reduceIte]; intro h; simp only [Prod.mk.injEq, Result.signal.injEq] at h; rw [← h.1]; exact fun _ h => nomatch h
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      split <;> intro h <;> simp_all

/-- The state an instruction time ends in after the Operation run `r`. -/
def resOf (o : Oracle) (a : Arch) : Result Unit × Frame → Arch
  | (.ok (), f) => Complete a f
  | (.signal e, f) => GeneralExceptionProcessing modelImpl o e f.arch

theorem sep_run (a : Arch) (p₁ p₂ : WP) (P₁ P₂ : Arch → Prop) (hobs : ∀ x y, P₁ x → P₂ y → Obs x ≠ Obs y)
    (r₁ r₂ : Result Unit × Frame) (h₁ : RunP a P₁ r₁) (h₂ : RunP a P₂ r₂) :
    Sep (resOf (wo p₁ (ceA a)) a r₁) (resOf (wo p₂ (ceB a)) a r₂) := by
  obtain ⟨res₁, g₁⟩ := r₁; obtain ⟨res₂, g₂⟩ := r₂
  cases res₁ <;> cases res₂ <;> simp only [RunP] at h₁ h₂ <;> simp only [resOf]
  · right; left; rw [obs_complete, obs_complete]; exact hobs _ _ h₁.1 h₂.1
  · left; rw [ce_complete, h₁.2, gep_CE _ _ _ _ _ h₂]; exact (ceB_ne a).symm
  · left; rw [ce_complete, h₂.2, gep_CE _ _ _ _ _ h₁]; exact ceA_ne a
  · exact sep_gep a p₁ p₂ _ _ _ _ h₁ h₂

set_option maxHeartbeats 1000000 in
/-- **`ChoiceFree` is exact**: at every state where it is `false`, two valid resolutions of
the manual's choices give different instruction times. -/
theorem choiceFree_exact (dec : W32 → Option Instruction) (a : Arch)
    (h : ChoiceFree modelImpl dec a = false) :
    ∃ o₁ o₂ : Oracle, o₁.Valid ∧ o₂.Valid ∧
      InstructionTime modelImpl o₁ dec a ≠ InstructionTime modelImpl o₂ dec a := by
  unfold ChoiceFree at h
  cases hi : InterruptTaken modelImpl a
  case true => exact interrupt_choice_exists modelImpl dec a hi
  simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
  cases hl : a.LowPower
  case true => simp [hl] at h
  simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
  have hF : ∀ o, InstructionFetch.run (ctxOf modelImpl o) { arch := a } =
      InstructionFetch.run (ctxOf modelImpl modelOracle) { arch := a } := fun o => fetch_oracleFree _ _ a
  have hFE : ∀ o, FetchExecute (ctxOf modelImpl o) dec a =
      match InstructionFetch.run (ctxOf modelImpl modelOracle) { arch := a } with
      | (.signal e, f) => some (GeneralExceptionProcessing modelImpl o e f.arch)
      | (.ok w, _) =>
        match dec w with
        | none =>
          if UnpredictableEncoding w then some (Unpredictable (ctxOf modelImpl o) w a)
          else some (GeneralExceptionProcessing modelImpl o (Undecodable w a) a)
        | some i => Execute (ctxOf modelImpl o) w i a := by
    intro o; unfold FetchExecute; rw [hF o]; rfl
  rcases hR : InstructionFetch.run (ctxOf modelImpl modelOracle) { arch := a } with ⟨r, f⟩
  rw [hR] at h
  rw [hR] at hFE
  cases r with
  | signal e =>
    have he := fetch_notCpU _ a e f hR
    exact exact_of dec a hi hl {} {} _ _ (hFE _) (hFE _) (sep_gep a {} {} e e _ _ he he)
  | ok w =>
    simp only at h hFE
    cases hd : dec w with
    | none =>
      rw [hd] at h hFE
      by_cases hu : UnpredictableEncoding w = true
      · simp only [hu, ↓reduceIte] at h hFE
        by_cases hcc : ((InCop1Space w && !StatusCU1 a) || (InCop0Space w && !CP0Usable a)) = true
        · simp only [hcc, Bool.true_and] at h
          have hU : ∀ p ce, Unpredictable (ctxOf modelImpl (wo p ce)) w a =
              GeneralExceptionProcessing modelImpl (wo p ce)
                (.CoprocessorUnusable (if (InCop1Space w && !StatusCU1 a) = true then 1 else 0)) a := by
            intro p ce
            by_cases h1 : (InCop1Space w && !StatusCU1 a) = true
            · simp only [Unpredictable, h1, ↓reduceIte, ctxOf]
            · have h0 : (InCop0Space w && !CP0Usable a) = true := by simpa [h1] using hcc
              simp only [Unpredictable, h1, h0, ↓reduceIte, Bool.false_eq_true, ctxOf]
          exact exact_of dec a hi hl { bip := 0#32 } { bip := 1#32 } _ _ (by rw [hFE, hU]) (by rw [hFE, hU])
            (sep_bip _ _ a (by intro h; cases h) h _ _)
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hcc
        obtain ⟨h1, h0⟩ := hcc
        have hU : ∀ p ce, Unpredictable (ctxOf modelImpl (wo p ce)) w a =
            GeneralExceptionProcessing modelImpl (wo p ce) .ReservedInstruction a := by
          intro p ce; simp only [Unpredictable, h1, h0, Bool.false_eq_true, ↓reduceIte, ctxOf, wo, sigRI]
        exact exact_of dec a hi hl {} {} _ _ (by rw [hFE, hU]) (by rw [hFE, hU])
          (sep_gep a {} {} _ _ _ _ notCpU_RI notCpU_RI)
      · simp only [hu, Bool.false_eq_true, ↓reduceIte] at h hFE
        by_cases hcpu : ∃ u, Undecodable w a = .CoprocessorUnusable u
        · obtain ⟨u, hu'⟩ := hcpu
          rw [hu'] at h hFE
          exact exact_of dec a hi hl { bip := 0#32 } { bip := 1#32 } _ _ (hFE _) (hFE _)
            (sep_bip _ _ a (by intro h; cases h) h _ _)
        have hU : NotCpU (Undecodable w a) := fun u hu' => hcpu ⟨u, hu'⟩
        exact exact_of dec a hi hl {} {} _ _ (hFE _) (hFE _) (sep_gep a {} {} _ _ _ _ hU hU)
    | some ins =>
      rw [hd] at h hFE
      by_cases hc : (IsCTI ins && a.BranchDelay.isSome) = true
      · have hE : ∀ p ce, Execute (ctxOf modelImpl (wo p ce)) w ins a =
            some (GeneralExceptionProcessing modelImpl (wo p ce) .ReservedInstruction a) := by
          intro p ce; simp only [Execute, hc, ↓reduceIte, ctxOf, wo, sigRI]
        exact exact_of dec a hi hl {} {} _ _ (by rw [hFE]; exact hE _ _) (by rw [hFE]; exact hE _ _)
          (sep_gep a {} {} _ _ _ _ notCpU_RI notCpU_RI)
      simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.not_false, Bool.true_and] at h
      by_cases h1 : (InCop1Space w && !StatusCU1 a) = true
      · simp only [h1, ↓reduceIte] at h
        have hE : ∀ p ce, Execute (ctxOf modelImpl (wo p ce)) w ins a =
            some (GeneralExceptionProcessing modelImpl (wo p ce) (.CoprocessorUnusable 1) a) := by
          intro p ce; simp only [Execute, Execute.runOperation, hc, h1, Bool.false_eq_true, ↓reduceIte, ctxOf]
        exact exact_of dec a hi hl { bip := 0#32 } { bip := 1#32 } _ _ (by rw [hFE]; exact hE _ _)
          (by rw [hFE]; exact hE _ _) (sep_bip _ _ a (by intro h; cases h) h _ _)
      by_cases h0 : (InCop0Space w && !CP0Usable a) = true
      · simp only [h1, h0, ↓reduceIte, Bool.false_eq_true] at h
        have hE : ∀ p ce, Execute (ctxOf modelImpl (wo p ce)) w ins a =
            some (GeneralExceptionProcessing modelImpl (wo p ce) (.CoprocessorUnusable 0) a) := by
          intro p ce
          simp only [Execute, Execute.runOperation, hc, h1, h0, Bool.false_eq_true, ↓reduceIte, ctxOf]
        exact exact_of dec a hi hl { bip := 0#32 } { bip := 1#32 } _ _ (by rw [hFE]; exact hE _ _)
          (by rw [hFE]; exact hE _ _) (sep_bip _ _ a (by intro h; cases h) h _ _)
      simp only [Bool.not_eq_true] at h1 h0
      simp only [h1, h0, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨op, hop⟩ := operation_some ins
      have hE : ∀ p ce, Execute (ctxOf modelImpl (wo p ce)) w ins a =
          some (resOf (wo p ce) a (op.run (ctxOf modelImpl (wo p ce)) { arch := a })) := by
        intro p ce
        simp only [Execute, Execute.runOperation, hc, h1, h0, hop, Bool.false_eq_true, ↓reduceIte]
        rcases op.run (ctxOf modelImpl (wo p ce)) { arch := a } with ⟨res, g⟩
        cases res <;> rfl
      by_cases hco : ConsultsOracle ins a = true
      · obtain ⟨p₁, p₂, P₁, P₂, hobs, hrun⟩ := consults_row ins a hco
        exact exact_of dec a hi hl p₁ p₂ _ _ (by rw [hFE]; exact hE _ _) (by rw [hFE]; exact hE _ _)
          (sep_run a p₁ p₂ P₁ P₂ hobs _ _ (hrun op (ceA a) hop).1 (hrun op (ceB a) hop).2)
      · simp only [Bool.not_eq_true] at hco
        simp only [hco, Bool.not_false, Bool.true_and, hop] at h
        have hcf := fun ce => operation_choiceFree ins a hco modelImpl (wo {} ce) modelOracle
        simp only [hop, Option.map_some, Option.some.injEq] at hcf
        rcases hM : op.run (ctxOf modelImpl modelOracle) { arch := a } with ⟨res, g⟩
        rw [hM] at h hcf
        cases res with
        | ok u => simp at h
        | signal e =>
          by_cases hcpu : ∃ u, e = .CoprocessorUnusable u
          · obtain ⟨u, rfl⟩ := hcpu
            have hall : ∀ o, op.run (ctxOf modelImpl o) { arch := a } = (.signal (.CoprocessorUnusable u), g) := by
              intro o
              have := operation_choiceFree ins a hco modelImpl o modelOracle
              simp only [hop, Option.map_some, Option.some.injEq] at this
              rw [this, hM]
            have hE' : ∀ p ce, Execute (ctxOf modelImpl (wo p ce)) w ins a =
                some (GeneralExceptionProcessing modelImpl (wo p ce) (.CoprocessorUnusable u) g.arch) := by
              intro p ce; rw [hE, hall]; rfl
            simp only [Bool.and_eq_false_iff] at h
            rcases h with hs | hf
            · exact exact_of dec a hi hl { bip := 0#32 } { bip := 1#32 } _ _ (by rw [hFE]; exact hE' _ _)
                (by rw [hFE]; exact hE' _ _) (sep_bip _ _ g.arch (by intro h; cases h) hs _ _)
            · exact exact_of dec a hi hl { bnw := 0#32 } { bnw := 1#32 } _ _ (by rw [hFE]; exact hE' _ _)
                (by rw [hFE]; exact hE' _ _) (sep_bnw _ _ g.arch (by intro h; cases h) hf _ _)
          have he : NotCpU e := fun u hu => hcpu ⟨u, hu⟩
          have hrun : ∀ ce, RunP a (fun _ => False) (op.run (ctxOf modelImpl (wo {} ce)) { arch := a }) := by
            intro ce; rw [hcf ce]; exact he
          exact exact_of dec a hi hl {} {} _ _ (by rw [hFE]; exact hE _ _) (by rw [hFE]; exact hE _ _)
            (sep_run a {} {} _ _ (fun _ _ hx => hx.elim) _ _ (hrun _) (hrun _))

/-- **`ChoiceFree` characterizes determinism** (with `manual_step_deterministic`). -/
theorem choiceFree_iff (dec : W32 → Option Instruction) (a : Arch) :
    ChoiceFree modelImpl dec a = true ↔
      ∀ o₁ o₂ : Oracle, o₁.Valid → o₂.Valid →
        InstructionTime modelImpl o₁ dec a = InstructionTime modelImpl o₂ dec a := by
  constructor
  · intro h o₁ o₂ _ _; exact instructionTime_oracleFree modelImpl dec a h o₁ o₂
  · intro h
    cases hc : ChoiceFree modelImpl dec a
    · obtain ⟨o₁, o₂, h₁, h₂, hne⟩ := choiceFree_exact dec a hc
      exact absurd (h o₁ o₂ h₁ h₂) hne
    · rfl

end Refine
