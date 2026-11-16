import Semantics.Refine.Determinism

/-!
# Refine.ChoiceWitness — witness oracles for the exactness of `ChoiceFree` (wave 9)

The other direction of `ChoiceFree` (`Refine.choiceFree_exact`, `Refine/ChoiceExact.lean`) exhibits,
at every state where `ChoiceFree` is `false`, two valid oracles whose instruction times differ. The
oracles are taken from one family, `wo p ce`:

* every UNPREDICTABLE or UNDEFINED **operation** of the oracle signals Reserved Instruction (a valid
  outcome: MD00086 Vol II-A Rev 6.06 §1.2.1, p.3, "UNPREDICTABLE operations may cause ... arbitrary
  exceptions"; §1.2.2, p.4 for UNDEFINED);
* every **value** field is a constant chosen by the parameters `p : WP` (constants are
  non-interfering, `NIValue`), the QNaN fields among two fixed quiet NaNs (`QNaNValid`);
* `Cause.CE` is the constant `ce`.

`wo_valid`: every member of the family is valid.

**How a choice is shown to be real** (`RunP`). For a row of `ConsultsOracle` a lemma gives two
parameter sets `p₁`, `p₂` and two properties `P₁`, `P₂` of the state the Operation leaves, with
`P₁ x → P₂ y → Obs x ≠ Obs y`, and proves that the Operation run under `wo pₖ ce` (any `ce`) either
signals an exception other than Coprocessor Unusable, or completes in a state with `Pₖ` and the
`Cause.CE` field unchanged. The two `ce` are then chosen different from each other and from the
`Cause.CE` of the state (`ceA`, `ceB`): two signalled exceptions differ in `Cause.CE` (written with the
oracle's value, Vol III §6.2.3, p.87), a signalled exception and a completed instruction differ in
`Cause.CE` too, and two completed instructions differ in `Obs`.
-/

namespace Refine

open Manual

/-! ## The family -/

/-- The parameters of a witness oracle: the value fields. -/
structure WP where
  lc : Bool := false
  sc : Bool := true
  cf : W32 := 0#32
  rd : BitVec 64 := QA64
  anr : AbsNegNaN := .A'
  qd : Bool := true
  qs : Bool := true
  -- BEGIN R6-2
  bnw : W32 := 0#32
  bip : W32 := 0#32
  -- END R6-2
  dz : W32 := 0#32  -- R6-4: `divByZero`

/-- UNPREDICTABLE / UNDEFINED operations resolved as Reserved Instruction. -/
def sigRI : Outcome := .signal .ReservedInstruction

/-- **The witness oracle** with value parameters `p` and `Cause.CE` constant `ce`. -/
def wo (p : WP) (ce : BitVec 2) : Oracle where
  storeClearsLL := fun _ => p.sc
  causeCE := fun _ _ => ce
  resetUndefined := modelOracle.resetUndefined
  jalrRsIsRd := fun _ _ => sigRI
  -- BEGIN R6-3
  linkSourceIs31 := fun _ _ => sigRI
  -- END R6-3
  fprOddRead := fun _ _ => p.rd
  fprOddWrite := fun _ _ _ => sigRI
  cfc1Unpredictable := fun _ _ => p.cf
  ctc1Unpredictable := fun _ _ _ => sigRI
  extOutOfRange := fun _ => sigRI
  insLsbAboveMsb := fun _ => sigRI
  unpredictableEncoding := fun _ _ => sigRI
  ebaseWriteBEV0 := fun _ _ => sigRI
  loadClearsLL := fun _ => p.lc
  absNegNaN := p.anr
  cvtQNaNToD := fun _ => if p.qd then QA64 else QB64
  cvtQNaNToS := fun _ => if p.qs then QA32 else QB32
  -- BEGIN R6-2
  badInstrNoWord := fun _ => p.bnw
  badInstrP := fun _ => p.bip
  -- END R6-2
  divByZero := fun _ _ _ => p.dz  -- R6-4

/-- **Every witness oracle is valid.** -/
theorem wo_valid (p : WP) (ce : BitVec 2) : (wo p ce).Valid := by
  -- R6-3: two more conjuncts (`linkSourceIs31`)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  all_goals (try simp only [NIOutcome, NIValue])
  all_goals (intros; first | exact trivial | rfl | skip)
  · simp only [wo]; split
    · exact QA64_q
    · exact QB64_q
  · simp only [wo]; split
    · exact QA32_q
    · exact QB32_q
  · exact ⟨rfl, rfl⟩

/-! ## Choosing `Cause.CE` -/

/-- `Cause.CE` (bits 29..28) of a state. -/
def CEof (x : Arch) : BitVec 2 := x.Cause.extractLsb' 28 2

/-- Two values of `Cause.CE` different from each other and from that of `a`. -/
def ceA (a : Arch) : BitVec 2 := CEof a + 1#2
def ceB (a : Arch) : BitVec 2 := CEof a + 2#2

theorem ceA_ne (a : Arch) : ceA a ≠ CEof a := by
  unfold ceA; generalize CEof a = c; intro h; have := congrArg BitVec.toNat h
  simp [BitVec.toNat_add] at this; omega
theorem ceB_ne (a : Arch) : ceB a ≠ CEof a := by
  unfold ceB; generalize CEof a = c; intro h; have := congrArg BitVec.toNat h
  simp [BitVec.toNat_add] at this; omega
theorem ceA_ne_ceB (a : Arch) : ceA a ≠ ceB a := by
  unfold ceA ceB; generalize CEof a = c; intro h; have := congrArg BitVec.toNat h
  simp [BitVec.toNat_add] at this; omega

/-- An exception other than Coprocessor Unusable. -/
def NotCpU (e : Exception) : Prop := ∀ u, e ≠ .CoprocessorUnusable u

/-- After the general exception processing for such an exception, `Cause.CE` is the oracle's. -/
theorem gep_CE (i : Impl) (p : WP) (ce : BitVec 2) (e : Exception) (x : Arch) (he : NotCpU e) :
    CEof (GeneralExceptionProcessing i (wo p ce) e x) = ce := by
  have hf : FaultingCoprocessorNumber (wo p ce) x e = ce := by
    cases e <;> first | exact absurd rfl (he _) | rfl
  simp only [CEof, GeneralExceptionProcessing, hf]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl <;> simp

-- BEGIN R6-2
/-- After the general exception processing for an exception other than the Interrupt outside a delay
slot, `BadInstrP` is the oracle's (UNPREDICTABLE, MD00090 Vol III Rev 6.02 §9.26, p.181). -/
theorem gep_badInstrP (i : Impl) (p : WP) (ce : BitVec 2) (e : Exception) (x : Arch)
    (he : e ≠ .Interrupt) (hs : x.BranchDelay.isSome = false) :
    (GeneralExceptionProcessing i (wo p ce) e x).BadInstrP = p.bip := by
  have hs' : (AdditionalState e x).BranchDelay.isSome = false := by cases e <;> exact hs
  simp only [GeneralExceptionProcessing, he, hs', ↓reduceIte, Bool.false_eq_true]
  rfl

/-- After the general exception processing for an exception other than the Interrupt from a state
whose fetch fails, `BadInstr` is the oracle's (UNPREDICTABLE, MD00090 Vol III Rev 6.02 §9.25,
p.179). -/
theorem gep_badInstr (i : Impl) (p : WP) (ce : BitVec 2) (e : Exception) (x : Arch)
    (he : e ≠ .Interrupt) (hf : FetchOK i x = false) :
    (GeneralExceptionProcessing i (wo p ce) e x).BadInstr = p.bnw := by
  simp only [GeneralExceptionProcessing, he, ↓reduceIte]
  unfold FaultingInstructionWord
  unfold FetchOK at hf
  rw [show ({ impl := i, oracle := wo p ce } : Ctx) = ctxOf i (wo p ce) from rfl,
    fetch_oracleFree (ctxOf i (wo p ce)) (ctxOf i modelOracle)]
  revert hf
  cases (InstructionFetch.run (ctxOf i modelOracle) { arch := x }).1 <;> intro hf
  · cases hf
  · rfl
-- END R6-2

/-! ## What two completed instructions are compared on -/

/-- The parts of the state the rows compare. -/
def Obs (x : Arch) : Bool × (Fin 32 → W32) × (Fin 32 → W32) × W32 × (PAddr → UInt8) :=
  (x.LLbit, x.GPR, x.FPR, x.FCSR, x.Mem)

theorem obs_timerTick (i : Impl) (x : Arch) : Obs (TimerTick i x) = Obs x := rfl
theorem ce_timerTick (i : Impl) (x : Arch) : CEof (TimerTick i x) = CEof x := rfl
theorem obs_complete (a : Arch) (f : Frame) : Obs (Complete a f) = Obs f.arch := by
  unfold Complete; split
  · rfl
  · split <;> rfl
theorem ce_complete (a : Arch) (f : Frame) : CEof (Complete a f) = CEof f.arch := by
  unfold Complete; split
  · rfl
  · split <;> rfl

/-- **The result of one Operation run, as a row needs it**: an exception other than Coprocessor
Unusable, or completion in a state with `P` and the `Cause.CE` of `a`. -/
def RunP (a : Arch) (P : Arch → Prop) : Result Unit × Frame → Prop
  | (.ok _, f) => P f.arch ∧ CEof f.arch = CEof a
  | (.signal e, _) => NotCpU e

/-- **A row of `ConsultsOracle` is a real choice at `a`.** -/
def RowWitness (ins : Instruction) (a : Arch) : Prop :=
  ∃ (p₁ p₂ : WP) (P₁ P₂ : Arch → Prop), (∀ x y, P₁ x → P₂ y → Obs x ≠ Obs y) ∧
    ∀ op ce, Operation ins = some op →
      RunP a P₁ (op.run (ctxOf modelImpl (wo p₁ ce)) { arch := a }) ∧
      RunP a P₂ (op.run (ctxOf modelImpl (wo p₂ ce)) { arch := a })

/-! ## Simplification lemmas for the rows -/

@[simp] theorem writeGPR_LLbit (a : Arch) (x : Fin 32) (v : W32) : (writeGPR a x v).LLbit = a.LLbit := by
  unfold writeGPR; split <;> rfl
@[simp] theorem writeGPR_FPR (a : Arch) (x : Fin 32) (v : W32) : (writeGPR a x v).FPR = a.FPR := by
  unfold writeGPR; split <;> rfl
@[simp] theorem writeGPR_FCSR (a : Arch) (x : Fin 32) (v : W32) : (writeGPR a x v).FCSR = a.FCSR := by
  unfold writeGPR; split <;> rfl
@[simp] theorem writeGPR_Mem (a : Arch) (x : Fin 32) (v : W32) : (writeGPR a x v).Mem = a.Mem := by
  unfold writeGPR; split <;> rfl
@[simp] theorem writeGPR_Cause (a : Arch) (x : Fin 32) (v : W32) : (writeGPR a x v).Cause = a.Cause := by
  unfold writeGPR; split <;> rfl
@[simp] theorem CEof_writeGPR (a : Arch) (x : Fin 32) (v : W32) : CEof (writeGPR a x v) = CEof a := by
  simp only [CEof, writeGPR_Cause]
theorem writeGPR_GPR (a : Arch) (x : Fin 32) (v : W32) (h : x ≠ 0) : (writeGPR a x v).GPR x = v := by
  simp [writeGPR, h, update]

end Refine
