import Semantics.FpOpsCorrectDivSqrt

/-!
# FpOpsCorrectOps — the arithmetic operations are correctly rounded

For finite operands whose exact result is nonzero, `Format.add`/`sub`/`mul`/`div`/`sqrt` (no
flushing, FCSR.FS = 0) deliver the encoding and the flags of a `Rounded` record that meets
`Format.RoundSpec` for the exact sum / difference / product / quotient / square root. Also: the
finite values are in `Format.Unbounded`, so without overflow the result is correctly rounded to the
format's finite values (`roundSpec_representable`).
-/

namespace Mips.Fp

namespace Format

/-! ## Finite operands -/

theorem value_fields (f : Format) {n : Nat} {x : Rat} (h : f.value n = some x) :
    f.isNaN n = false ∧ f.isInf n = false ∧ (f.toExact n).toRat = x := by
  obtain ⟨-, h2⟩ := value_some_lt f h
  refine ⟨?_, ?_, value_toExact f h⟩ <;> simp [isNaN, isInf, h2]

theorem toExact_sig_ne_zero (f : Format) {n : Nat} {x : Rat} (h : f.value n = some x) (hx : x ≠ 0) :
    (f.toExact n).sig ≠ 0 := by
  intro h0
  apply hx
  rw [← value_toExact f h, Exact.toRat, h0]; simp

theorem isZero_false (f : Format) {n : Nat} {x : Rat} (h : f.value n = some x) (hx : x ≠ 0) :
    f.isZero n = false := by
  have := toExact_sig_ne_zero f h hx
  simp only [toExact] at this
  simp only [isZero]
  split at this <;> simp_all

theorem exact_sig_ne_zero {w : Exact} (h : w.toRat ≠ 0) : w.sig ≠ 0 := by
  intro h0; apply h; rw [Exact.toRat, h0]; simp

theorem roundEnv_eq (f : Format) (e : Env) (he : e.flush = false) (w : Exact) :
    f.roundEnv e w = ((f.roundCore e.rm false w).bits, (f.roundCore e.rm false w).flags e.enables) := by
  simp [roundEnv, he]

/-- The core's rounding of an exact value with a cut that agrees with it. -/
theorem round_spec_of (f : Format) (hf : f.WF) (e : Env) (he : e.flush = false) (w : Exact)
    (hw : w.sig ≠ 0) (c : Cut) (hc : c.Valid)
    (hag : CutAgree c w.toRat (w.exp + bitLen w.sig - ((f.fracBits + 1 : Nat) : Int) - 1)) :
    ∃ R : Rounded, f.RoundSpec e.rm c R ∧ f.roundEnv e w = (R.bits, R.flags e.enables) :=
  ⟨_, roundCore_correct f hf e.rm w hw c hc hag, f.roundEnv_eq e he w⟩

/-! ## The operations -/

/-- **`ADD.fmt`**: the correctly rounded sum. -/
theorem add_correct (f : Format) (hf : f.WF) (e : Env) (he : e.flush = false) {a b : Nat} {x y : Rat}
    (ha : f.value a = some x) (hb : f.value b = some y) (hxy : x + y ≠ 0) :
    ∃ R : Rounded, f.RoundSpec e.rm (Cut.ofRat (x + y)) R ∧ f.add e a b = (R.bits, R.flags e.enables) := by
  obtain ⟨na, ia, ea⟩ := value_fields f ha
  obtain ⟨nb, ib, eb⟩ := value_fields f hb
  have hw : (Exact.add e.rm (f.toExact a) (f.toExact b)).toRat = x + y := by
    rw [Exact.add_toRat, ea, eb]
  simp only [add, addCore, na, nb, ia, ib, Bool.or_false, Bool.false_eq_true, ite_false]
  rw [← hw]
  exact f.round_spec_of hf e he _ (exact_sig_ne_zero (by rw [hw]; exact hxy)) _ (Cut.ofRat_valid _)
    (CutAgree.ofRat _ _)

theorem fields_split (f : Format) (t m : Nat) (ht : t ≤ 1) (hm : m < 2 ^ (f.expBits + f.fracBits)) :
    f.expField (t * 2 ^ (f.expBits + f.fracBits) + m) = m / 2 ^ f.fracBits ∧
    f.fracField (t * 2 ^ (f.expBits + f.fracBits) + m) = m % 2 ^ f.fracBits ∧
    f.signBit (t * 2 ^ (f.expBits + f.fracBits) + m) = (t == 1) ∧
    t * 2 ^ (f.expBits + f.fracBits) + m < 2 ^ f.width := by
  have hF : 0 < 2 ^ f.fracBits := Nat.two_pow_pos _
  have hW : 0 < 2 ^ (f.expBits + f.fracBits) := Nat.two_pow_pos _
  have hmd : m / 2 ^ f.fracBits < 2 ^ f.expBits := by
    rw [Nat.div_lt_iff_lt_mul hF, ← Nat.pow_add]; exact hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [expField]
    rw [Nat.pow_add, show t * (2 ^ f.expBits * 2 ^ f.fracBits) + m = m + (t * 2 ^ f.expBits) * 2 ^ f.fracBits by
      rw [Nat.mul_assoc]; omega, Nat.add_mul_div_right _ _ hF, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hmd]
  · simp only [fracField]
    rw [Nat.pow_add, show t * (2 ^ f.expBits * 2 ^ f.fracBits) + m = m + (t * 2 ^ f.expBits) * 2 ^ f.fracBits by
      rw [Nat.mul_assoc]; omega, Nat.add_mul_mod_self_right]
  · simp only [signBit]
    rw [show t * 2 ^ (f.expBits + f.fracBits) + m = m + t * 2 ^ (f.expBits + f.fracBits) by omega,
      Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hm, Nat.zero_add]
    rcases (show t = 0 ∨ t = 1 by omega) with h | h <;> subst h <;> rfl
  · simp only [width, Nat.pow_add, Nat.pow_one] at *
    have : t * (2 ^ f.expBits * 2 ^ f.fracBits) ≤ 1 * (2 ^ f.expBits * 2 ^ f.fracBits) :=
      Nat.mul_le_mul_right _ ht
    have e : 2 * 2 ^ f.expBits * 2 ^ f.fracBits = 2 * (2 ^ f.expBits * 2 ^ f.fracBits) := by
      rw [Nat.mul_assoc]
    omega

theorem negBits_value (f : Format) {n : Nat} {y : Rat} (h : f.value n = some y) :
    f.value (f.negBits n) = some (-y) := by
  obtain ⟨hn, he⟩ := value_some_lt f h
  have hy := value_toExact f h
  have hW : 0 < 2 ^ (f.expBits + f.fracBits) := Nat.two_pow_pos _
  have hw2 : 2 ^ f.width = 2 * 2 ^ (f.expBits + f.fracBits) := by
    simp only [width]; rw [Nat.add_assoc, Nat.pow_add, Nat.pow_one]
  have hd := Nat.div_add_mod n (2 ^ (f.expBits + f.fracBits))
  have hm := Nat.mod_lt n hW
  have ht : n / 2 ^ (f.expBits + f.fracBits) ≤ 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hW]; omega
  generalize n / 2 ^ (f.expBits + f.fracBits) = t at *
  generalize n % 2 ^ (f.expBits + f.fracBits) = m at *
  have hn' : n = t * 2 ^ (f.expBits + f.fracBits) + m := by rw [Nat.mul_comm]; omega
  have hneg : f.negBits n = (1 - t) * 2 ^ (f.expBits + f.fracBits) + m := by
    obtain ⟨-, -, hs, -⟩ := f.fields_split t m ht hm
    simp only [negBits, hn', hs]
    rcases (show t = 0 ∨ t = 1 by omega) with h | h <;> subst h <;> simp <;> omega
  obtain ⟨e1, f1, s1, l1⟩ := f.fields_split t m ht hm
  obtain ⟨e2, f2, s2, l2⟩ := f.fields_split (1 - t) m (by omega) hm
  rw [hn'] at he hy
  rw [hneg, value_eq_toExact f _ l2 (by rw [e2, ← e1]; exact he), ← hy]
  congr 1
  simp only [toExact, e1, f1, s1, e2, f2, s2, Exact.toRat]
  rcases (show t = 0 ∨ t = 1 by omega) with h | h <;> subst h <;> split <;> simp <;> grind

/-- **`SUB.fmt`**: the correctly rounded difference. -/
theorem sub_correct (f : Format) (hf : f.WF) (e : Env) (he : e.flush = false) {a b : Nat} {x y : Rat}
    (ha : f.value a = some x) (hb : f.value b = some y) (hxy : x - y ≠ 0) :
    ∃ R : Rounded, f.RoundSpec e.rm (Cut.ofRat (x - y)) R ∧ f.sub e a b = (R.bits, R.flags e.enables) := by
  have hnb := f.negBits_value hb
  obtain ⟨na, -, -⟩ := value_fields f ha
  obtain ⟨nb, -, -⟩ := value_fields f hb
  have := f.add_correct hf e he ha hnb (by grind)
  simp only [sub, na, nb, Bool.or_false, Bool.false_eq_true, ite_false]
  simp only [add] at this
  obtain ⟨na', -, -⟩ := value_fields f hnb
  simp only [na, na', Bool.or_false, Bool.false_eq_true, ite_false] at this
  rw [show x - y = x + -y by grind]; exact this

/-- **`MUL.fmt`**: the correctly rounded product. -/
theorem mul_correct (f : Format) (hf : f.WF) (e : Env) (he : e.flush = false) {a b : Nat} {x y : Rat}
    (ha : f.value a = some x) (hb : f.value b = some y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ R : Rounded, f.RoundSpec e.rm (Cut.ofRat (x * y)) R ∧ f.mul e a b = (R.bits, R.flags e.enables) := by
  obtain ⟨na, ia, ea⟩ := value_fields f ha
  obtain ⟨nb, ib, eb⟩ := value_fields f hb
  have hw : (Exact.mul (f.toExact a) (f.toExact b)).toRat = x * y := by
    rw [Exact.mul_toRat, ea, eb]
  have hxy : x * y ≠ 0 := fun h => by rcases Rat.mul_eq_zero.1 h with h | h <;> contradiction
  simp only [mul, na, nb, ia, ib, Bool.or_false, Bool.false_eq_true, ite_false, Bool.false_and,
    Bool.and_false]
  rw [← hw]
  exact f.round_spec_of hf e he _ (exact_sig_ne_zero (by rw [hw]; exact hxy)) _ (Cut.ofRat_valid _)
    (CutAgree.ofRat _ _)

/-- **`DIV.fmt`**: the correctly rounded quotient. -/
theorem div_correct (f : Format) (hf : f.WF) (e : Env) (he : e.flush = false) {a b : Nat} {x y : Rat}
    (ha : f.value a = some x) (hb : f.value b = some y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ R : Rounded, f.RoundSpec e.rm (Cut.ofRat (x / y)) R ∧ f.div e a b = (R.bits, R.flags e.enables) := by
  obtain ⟨na, ia, ea⟩ := value_fields f ha
  obtain ⟨nb, ib, eb⟩ := value_fields f hb
  have za := f.isZero_false ha hx
  have zb := f.isZero_false hb hy
  obtain ⟨hw, hag⟩ := Exact.div_agree (f.fracBits + 1) _ _ (f.toExact_sig_ne_zero ha hx)
    (f.toExact_sig_ne_zero hb hy)
  rw [ea, eb] at hag
  simp only [div, na, nb, ia, ib, za, zb, Bool.or_false, Bool.false_eq_true, ite_false, Bool.false_and]
  exact f.round_spec_of hf e he _ hw _ (Cut.ofRat_valid _) hag

/-- **`SQRT.fmt`**: the correctly rounded square root of a positive operand. -/
theorem sqrt_correct (f : Format) (hf : f.WF) (e : Env) (he : e.flush = false) {a : Nat} {x : Rat}
    (ha : f.value a = some x) (hx : 0 < x) :
    ∃ R : Rounded, f.RoundSpec e.rm (Cut.sqrt x) R ∧ f.sqrt e a = (R.bits, R.flags e.enables) := by
  obtain ⟨na, ia, ea⟩ := value_fields f ha
  have hx0 : x ≠ 0 := by grind
  have za := f.isZero_false ha hx0
  have hs : (f.toExact a).sign = false := by
    have h := ea; rw [Exact.toRat_signed] at h
    cases hsg : (f.toExact a).sign
    · rfl
    · rw [hsg] at h; simp only [ite_true] at h
      have : (0 : Rat) ≤ ((f.toExact a).sig : Rat) * (2 : Rat) ^ (f.toExact a).exp :=
        Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (rat_two_zpow_pos _))
      grind
  have hsb : f.signBit a = false := by simp only [toExact] at hs; split at hs <;> exact hs
  obtain ⟨hw, hag⟩ := Exact.sqrt_agree (f.fracBits + 1) _ (f.toExact_sig_ne_zero ha hx0) hs
  rw [ea] at hag
  simp only [sqrt, na, ia, za, hsb, Bool.false_eq_true, ite_false]
  exact f.round_spec_of hf e he _ hw _ (Cut.sqrt_valid _) hag

end Format

end Mips.Fp
