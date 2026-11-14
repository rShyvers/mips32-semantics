import Semantics.FpOpsCorrectEnv

/-!
# FpOpsCorrectArith — `ADD`/`SUB`/`MUL`/`DIV`/`SQRT` on every operand

`Format.add`/`sub`/`mul`/`div`/`sqrt` meet `Format.AddSpec`/`MulSpec`/`DivSpec`/`SqrtSpec` of
`Semantics/FpOpsSpec.lean` for **all** `width`-bit operands (NaN, ±∞, ±0, finite) and every FCSR
environment (rounding mode, Enables, FS); the encodings they deliver are `width`-bit patterns.
-/

namespace Mips.Fp

namespace Format

variable (f : Format)

/-! ## Decomposing an encoding -/

theorem split_bits {n : Nat} (hn : n < 2 ^ f.width) :
    ∃ t m, t ≤ 1 ∧ m < 2 ^ (f.expBits + f.fracBits) ∧ n = t * 2 ^ (f.expBits + f.fracBits) + m := by
  have hW : 0 < 2 ^ (f.expBits + f.fracBits) := Nat.two_pow_pos _
  have hw2 : 2 ^ f.width = 2 * 2 ^ (f.expBits + f.fracBits) := by
    simp only [width]; rw [Nat.add_assoc, Nat.pow_add, Nat.pow_one]
  have hd := Nat.div_add_mod n (2 ^ (f.expBits + f.fracBits))
  refine ⟨n / 2 ^ (f.expBits + f.fracBits), n % 2 ^ (f.expBits + f.fracBits), ?_, Nat.mod_lt n hW, ?_⟩
  · rw [Nat.div_le_iff_le_mul_add_pred hW]; omega
  · rw [Nat.mul_comm]; omega

theorem eq_pack {n : Nat} (hn : n < 2 ^ f.width) :
    n = f.pack (f.signBit n) (f.expField n) (f.fracField n) := by
  obtain ⟨t, m, ht, hm, rfl⟩ := f.split_bits hn
  obtain ⟨e1, f1, s1, -⟩ := f.fields_split t m ht hm
  rw [e1, f1, s1]
  have := Nat.div_add_mod m (2 ^ f.fracBits)
  simp only [pack]
  rcases (show t = 0 ∨ t = 1 by omega) with h | h <;> subst h <;> simp <;> rw [Nat.mul_comm] <;> omega

theorem eq_inf_of_isInf {n : Nat} (hn : n < 2 ^ f.width) (h : f.isInf n = true) :
    n = f.inf (f.signBit n) := by
  simp only [isInf, Bool.and_eq_true, beq_iff_eq] at h
  have := f.eq_pack hn; rw [h.1, h.2] at this; exact this

theorem eq_zero_of_isZero {n : Nat} (hn : n < 2 ^ f.width) (h : f.isZero n = true) :
    n = f.zero (f.signBit n) := by
  simp only [isZero, Bool.and_eq_true, beq_iff_eq] at h
  have := f.eq_pack hn; rw [h.1, h.2] at this; exact this

/-- `negBits` flips the sign bit and keeps the exponent and fraction. -/
theorem negBits_fields {n : Nat} (hn : n < 2 ^ f.width) :
    f.negBits n < 2 ^ f.width ∧ f.expField (f.negBits n) = f.expField n ∧
    f.fracField (f.negBits n) = f.fracField n ∧ f.signBit (f.negBits n) = !f.signBit n := by
  obtain ⟨t, m, ht, hm, rfl⟩ := f.split_bits hn
  obtain ⟨e1, f1, s1, -⟩ := f.fields_split t m ht hm
  obtain ⟨e2, f2, s2, l2⟩ := f.fields_split (1 - t) m (by omega) hm
  have hneg : f.negBits (t * 2 ^ (f.expBits + f.fracBits) + m) = (1 - t) * 2 ^ (f.expBits + f.fracBits) + m := by
    simp only [negBits, s1]
    rcases (show t = 0 ∨ t = 1 by omega) with h | h <;> subst h <;> simp <;> omega
  rw [hneg, e1, f1, s1, e2, f2, s2]
  refine ⟨l2, rfl, rfl, ?_⟩
  rcases (show t = 0 ∨ t = 1 by omega) with h | h <;> subst h <;> rfl

/-! ## Flags of an exact zero -/

theorem roundEnv_zero (e : Env) (w : Exact) (hw : w.sig = 0) :
    f.roundEnv e w = (f.zero w.sign, {}) := by
  simp [roundEnv, roundCore_zero f _ _ w hw, Rounded.flags]

theorem flags_none : Flags.none = {} := rfl
theorem flags_invalidOnly : Flags.invalidOnly = { invalid := true } := rfl

/-! ## ADD, SUB -/

theorem Exact.add_zero (rm : RoundingMode) (a b : Exact) (h : (Exact.add rm a b).toRat = 0) :
    (Exact.add rm a b).sig = 0 ∧
      (Exact.add rm a b).sign = (if a.sign == b.sign then a.sign else decide (rm = .RM)) := by
  have h0 := (toRat_eq_zero_iff _).1 h
  refine ⟨h0, ?_⟩
  revert h0
  unfold Exact.add
  dsimp only
  generalize ((if a.sign = true then _ else _) + (if b.sign = true then _ else _) : Int) = S
  intro h
  by_cases hS : S = 0
  · simp [hS]
  · simp only [hS, ite_false] at h ⊢; omega

/-- The sum of two non-NaN operands (`addCore`) meets the non-NaN arms of `AddSpec`. -/
theorem addCore_spec (hf : f.WF) (e : Env) {a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width)
    (na : f.isNaN a = false) (nb : f.isNaN b = false) :
    f.AddSpec e false a b (f.addCore e a b) := by
  rcases f.classify hf a ha with ⟨h1, -⟩ | ⟨-, ia, za, da⟩ | ⟨-, ia, -, da, va, za⟩
  · simp [h1] at na
  all_goals rcases f.classify hf b hb with ⟨h1, -⟩ | ⟨-, ib, zb, db⟩ | ⟨-, ib, -, db, vb, zb⟩
  all_goals (try simp [h1] at nb)
  · -- ∞, ∞
    simp only [AddSpec, da, db, addCore, ia, ib, Bool.true_and, Bool.xor_false]
    by_cases hs : f.signBit a = f.signBit b
    · simp only [hs, bne_self_eq_false, ite_true, Bool.false_eq_true, ite_false, infBits_eq, flags_none]
      rw [← hs]; exact congrArg (·, _) (f.eq_inf_of_isInf ha ia)
    · simp only [hs, ite_false, invalidResult_eq]
      simp [bne_iff_ne, hs]
  · -- ∞, finite
    simp only [AddSpec, da, db, addCore, ia, ib, Bool.false_and, Bool.false_eq_true, ite_false, ite_true,
      infBits_eq, flags_none]
    exact congrArg (·, _) (f.eq_inf_of_isInf ha ia)
  · -- finite, ∞
    simp only [AddSpec, da, db, addCore, ia, ib, ite_true, Bool.false_eq_true, ite_false, infBits_eq,
      flags_none, Bool.xor_false]
    exact congrArg (·, _) (f.eq_inf_of_isInf hb ib)
  · -- finite, finite
    simp only [AddSpec, da, db, addCore, ia, ib, Bool.false_eq_true, ite_false, Bool.xor_false]
    have hw := Exact.add_toRat e.rm (f.toExact a) (f.toExact b)
    by_cases hv : (f.toExact a).toRat + (f.toExact b).toRat = 0
    · simp only [hv, ↓reduceIte]
      obtain ⟨h0, hsg⟩ := Exact.add_zero e.rm _ _ (by rw [hw]; exact hv)
      rw [f.roundEnv_zero e _ h0, hsg, zeroBits_eq]
      have sa : (f.toExact a).sign = f.signBit a := by simp only [toExact]; split <;> rfl
      have sb : (f.toExact b).sign = f.signBit b := by simp only [toExact]; split <;> rfl
      rw [sa, sb]
      by_cases hs : f.signBit a = f.signBit b <;> simp [hs]
    · simp only [hv, ↓reduceIte]; rw [← hw]
      exact f.roundEnv_spec_rat hf e _ (Format.exact_sig_ne_zero (by rw [hw]; exact hv))

/-- **`ADD.fmt` meets `AddSpec`** on every pair of `width`-bit operands. -/
theorem add_spec (hf : f.WF) (e : Env) {a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    f.AddSpec e false a b (f.add e a b) := by
  by_cases hn : f.isNaN a = true ∨ f.isNaN b = true
  · have hr : f.add e a b = (f.nanResult [a, b], f.nanFlags [a, b]) := by
      simp only [add]; rcases hn with h | h <;> simp [h]
    rw [hr]
    rcases hn with h | h
    · simp only [AddSpec, f.datum_of_nan h]; exact f.nanResult_spec hf _
    · rcases f.classify hf a ha with ⟨-, -, da⟩ | ⟨-, -, -, da⟩ | ⟨-, -, -, da, -⟩ <;>
        simp only [AddSpec, da, f.datum_of_nan h] <;> exact f.nanResult_spec hf _
  · simp only [not_or, Bool.not_eq_true] at hn
    have hr : f.add e a b = f.addCore e a b := by simp [add, hn.1, hn.2]
    rw [hr]; exact f.addCore_spec hf e ha hb hn.1 hn.2

theorem datum_negBits (hf : f.WF) {n : Nat} (hn : n < 2 ^ f.width) (nn : f.isNaN n = false) :
    f.datum (f.negBits n) = match f.datum n with
      | .inf t => .inf (!t)
      | .num t y => .num (!t) (-y)
      | .nan => .nan := by
  obtain ⟨l, e1, f1, s1⟩ := f.negBits_fields hn
  rcases f.classify hf n hn with ⟨h1, -⟩ | ⟨-, ib, -, db⟩ | ⟨-, ib, he, db, vb, -⟩
  · simp [h1] at nn
  · have ib' : f.isInf (f.negBits n) = true := by simp only [isInf, e1, f1] at ib ⊢; exact ib
    rw [db, f.datum_of_inf ib', s1]
  · rw [db, f.datum_of_finite l (by rw [e1]; exact he), s1]
    have := negBits_value f vb
    rw [value_eq_toExact f _ l (by rw [e1]; exact he)] at this
    rw [Option.some.inj this]

theorem isNaN_negBits {n : Nat} (hn : n < 2 ^ f.width) : f.isNaN (f.negBits n) = f.isNaN n := by
  obtain ⟨-, e1, f1, -⟩ := f.negBits_fields hn
  simp only [isNaN, e1, f1]

/-- **`SUB.fmt` meets `AddSpec` with `isSub`** on every pair of `width`-bit operands. -/
theorem sub_spec (hf : f.WF) (e : Env) {a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    f.AddSpec e true a b (f.sub e a b) := by
  by_cases hn : f.isNaN a = true ∨ f.isNaN b = true
  · have hr : f.sub e a b = (f.nanResult [a, b], f.nanFlags [a, b]) := by
      simp only [sub]; rcases hn with h | h <;> simp [h]
    rw [hr]
    rcases hn with h | h
    · simp only [AddSpec, f.datum_of_nan h]; exact f.nanResult_spec hf _
    · rcases f.classify hf a ha with ⟨-, -, da⟩ | ⟨-, -, -, da⟩ | ⟨-, -, -, da, -⟩ <;>
        simp only [AddSpec, da, f.datum_of_nan h] <;> exact f.nanResult_spec hf _
  · simp only [not_or, Bool.not_eq_true] at hn
    have hr : f.sub e a b = f.addCore e a (f.negBits b) := by simp [sub, hn.1, hn.2]
    rw [hr]
    have hl := (f.negBits_fields hb).1
    have h := f.addCore_spec hf e ha hl hn.1 (by rw [f.isNaN_negBits hb]; exact hn.2)
    have hd := f.datum_negBits hf hb hn.2
    rcases f.classify hf b hb with ⟨h1, -⟩ | ⟨-, -, -, db⟩ | ⟨-, -, -, db, -, -⟩
    · simp [h1] at hn
    all_goals rw [db] at hd; simp only at hd
    all_goals rcases f.classify hf a ha with ⟨h1, -⟩ | ⟨-, -, -, da⟩ | ⟨-, -, -, da, -, -⟩
    all_goals (try simp [h1] at hn)
    all_goals simp only [AddSpec, hd, db, da, Bool.xor_false, Bool.xor_true, Bool.false_eq_true,
      ite_false, ite_true] at h ⊢
    all_goals (try rw [← Rat.sub_eq_add_neg] at h)
    all_goals exact h

/-! ## MUL, DIV, SQRT -/

/-- **`MUL.fmt` meets `MulSpec`** on every pair of `width`-bit operands. -/
theorem mul_spec (hf : f.WF) (e : Env) {a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    f.MulSpec e a b (f.mul e a b) := by
  rcases f.classify hf a ha with ⟨na, -, da⟩ | ⟨na, ia, za, da⟩ | ⟨na, ia, -, da, va, za⟩
  · simp only [MulSpec, da, mul, na, Bool.true_or, ite_true]; exact f.nanResult_spec hf _
  all_goals rcases f.classify hf b hb with ⟨nb, -, db⟩ | ⟨nb, ib, zb, db⟩ | ⟨nb, ib, -, db, vb, zb⟩
  all_goals (try (simp only [MulSpec, da, db, mul, na, nb, Bool.or_true, ite_true]; exact f.nanResult_spec hf _))
  · simp [MulSpec, da, db, mul, na, nb, ia, ib, za, zb, infBits_eq, flags_none, bne]
  · simp only [MulSpec, da, db, mul, na, nb, ia, ib, za, Bool.or_false, Bool.false_eq_true, ite_false,
      Bool.true_and, Bool.false_and, ite_true]
    by_cases hz : (f.toExact b).toRat = 0
    · simp [hz, zb.1 hz, invalidResult_eq]
    · have : f.isZero b = false := by cases h : f.isZero b <;> simp_all
      simp [hz, this, infBits_eq, flags_none, bne]
  · simp only [MulSpec, da, db, mul, na, nb, ib, ia, zb, Bool.or_false, Bool.false_eq_true, ite_false,
      Bool.and_false, Bool.false_or, Bool.or_true, ite_true]
    by_cases hz : (f.toExact a).toRat = 0
    · simp [hz, za.1 hz, invalidResult_eq]
    · have : f.isZero a = false := by cases h : f.isZero a <;> simp_all
      simp [hz, this, infBits_eq, flags_none, bne]
  · simp only [MulSpec, da, db, mul, na, nb, ia, ib, Bool.or_false, Bool.false_eq_true, ite_false,
      Bool.false_and, Bool.and_false]
    have hw := Exact.mul_toRat (f.toExact a) (f.toExact b)
    by_cases hv : (f.toExact a).toRat * (f.toExact b).toRat = 0
    · simp only [hv, ↓reduceIte]
      have h0 : (Exact.mul (f.toExact a) (f.toExact b)).sig = 0 := (toRat_eq_zero_iff _).1 (by rw [hw]; exact hv)
      rw [f.roundEnv_zero e _ h0, zeroBits_eq]
      have sa : (f.toExact a).sign = f.signBit a := by simp only [toExact]; split <;> rfl
      have sb : (f.toExact b).sign = f.signBit b := by simp only [toExact]; split <;> rfl
      simp [Exact.mul, sa, sb, bne]
    · simp only [hv, ↓reduceIte]; rw [← hw]
      exact f.roundEnv_spec_rat hf e _ (Format.exact_sig_ne_zero (by rw [hw]; exact hv))

/-- **`DIV.fmt` meets `DivSpec`** on every pair of `width`-bit operands. -/
theorem div_spec (hf : f.WF) (e : Env) {a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    f.DivSpec e a b (f.div e a b) := by
  rcases f.classify hf a ha with ⟨na, -, da⟩ | ⟨na, ia, za, da⟩ | ⟨na, ia, -, da, va, za⟩
  · simp only [DivSpec, da, div, na, Bool.true_or, ite_true]; exact f.nanResult_spec hf _
  all_goals rcases f.classify hf b hb with ⟨nb, -, db⟩ | ⟨nb, ib, zb, db⟩ | ⟨nb, ib, -, db, vb, zb⟩
  all_goals (try (simp only [DivSpec, da, db, div, na, nb, Bool.or_true, ite_true]; exact f.nanResult_spec hf _))
  · simp [DivSpec, da, db, div, na, nb, ia, ib, invalidResult_eq]
  · simp [DivSpec, da, db, div, na, nb, ia, ib, za, infBits_eq, flags_none, bne]
  · simp [DivSpec, da, db, div, na, nb, ia, ib, zb, zeroBits_eq, flags_none, bne]
  · simp only [DivSpec, da, db, div, na, nb, ia, ib, Bool.or_false, Bool.false_eq_true, ite_false,
      Bool.and_false, Bool.false_or]
    have sa : (f.toExact a).sign = f.signBit a := by simp only [toExact]; split <;> rfl
    by_cases hy : (f.toExact b).toRat = 0
    · have zb' := zb.1 hy
      by_cases hx : (f.toExact a).toRat = 0
      · simp [hy, hx, zb', za.1 hx, invalidResult_eq]
      · have : f.isZero a = false := by cases h : f.isZero a <;> simp_all
        simp [hy, hx, zb', this, infBits_eq, bne]
    · have zb' : f.isZero b = false := by cases h : f.isZero b <;> simp_all
      by_cases hx : (f.toExact a).toRat = 0
      · simp [hy, hx, zb', za.1 hx, zeroBits_eq, flags_none, bne]
      · have za' : f.isZero a = false := by cases h : f.isZero a <;> simp_all
        simp only [hy, hx, zb', za', ite_false, Bool.and_false, Bool.false_eq_true]
        obtain ⟨hw, hag⟩ := Exact.div_agree (f.fracBits + 1) _ _ (exact_sig_ne_zero hx)
          (exact_sig_ne_zero hy)
        exact f.roundEnv_spec hf e _ hw _ (Cut.ofRat_valid _) hag

/-- **`SQRT.fmt` meets `SqrtSpec`** on every `width`-bit operand. -/
theorem sqrt_spec (hf : f.WF) (e : Env) {a : Nat} (ha : a < 2 ^ f.width) :
    f.SqrtSpec e a (f.sqrt e a) := by
  rcases f.classify hf a ha with ⟨na, -, da⟩ | ⟨na, ia, za, da⟩ | ⟨na, ia, -, da, va, za⟩
  · simp only [SqrtSpec, da, sqrt, na, ite_true]; exact f.nanResult_spec hf _
  · have hinf := f.eq_inf_of_isInf ha ia
    cases hs : f.signBit a
    · simp only [SqrtSpec, da, hs, sqrt, na, za, ia, Bool.false_eq_true, ite_false, ite_true,
        infBits_eq, flags_none]
      rw [hs] at hinf; rw [← hinf]
    · simp [SqrtSpec, da, hs, sqrt, na, za, invalidResult_eq]
  · have sa : (f.toExact a).sign = f.signBit a := by simp only [toExact]; split <;> rfl
    by_cases hx : (f.toExact a).toRat = 0
    · simp only [SqrtSpec, da, hx, ite_true, sqrt, na, za.1 hx, Bool.false_eq_true, ite_false,
        zeroBits_eq, flags_none]
      exact congrArg (·, _) (f.eq_zero_of_isZero ha (za.1 hx))
    · have za' : f.isZero a = false := by cases h : f.isZero a <;> simp_all
      have hsig := exact_sig_ne_zero hx
      have hneg := exact_sign_iff _ hsig
      rw [sa] at hneg
      simp only [SqrtSpec, da, hx, ite_false, sqrt, na, za', ia, Bool.false_eq_true]
      by_cases hl : (f.toExact a).toRat < 0
      · have : f.signBit a = true := hneg.2 (Rat.le_of_lt hl)
        simp [hl, this, invalidResult_eq]
      · have : f.signBit a = false := by
          cases h : f.signBit a
          · rfl
          · exact absurd (hneg.1 h) (fun h' => hx (Rat.le_antisymm h' (Rat.not_lt.mp hl)))
        simp only [hl, this, ite_false, Bool.false_eq_true]
        obtain ⟨hw, hag⟩ := Exact.sqrt_agree (f.fracBits + 1) _ hsig (by rw [sa]; exact this)
        exact f.roundEnv_spec hf e _ hw _ (Cut.sqrt_valid _) hag

/-! ## Results are `width`-bit patterns -/

theorem addCore_lt (hf : f.WF) (e : Env) {a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (f.addCore e a b).1 < 2 ^ f.width := by
  unfold addCore
  repeat' split
  all_goals first | exact ha | exact hb | exact f.defaultQNaN_lt hf | exact f.roundEnv_lt hf _ _

theorem add_lt (hf : f.WF) (e : Env) {a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (f.add e a b).1 < 2 ^ f.width := by
  unfold add; split
  · exact f.nanResult_lt hf _ (by simp; omega)
  · exact f.addCore_lt hf e ha hb

theorem sub_lt (hf : f.WF) (e : Env) {a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (f.sub e a b).1 < 2 ^ f.width := by
  unfold sub; split
  · exact f.nanResult_lt hf _ (by simp; omega)
  · exact f.addCore_lt hf e ha (f.negBits_fields hb).1

theorem mul_lt (hf : f.WF) (e : Env) {a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (f.mul e a b).1 < 2 ^ f.width := by
  unfold mul
  repeat' split
  all_goals first | exact f.nanResult_lt hf _ (by simp; omega) | exact f.defaultQNaN_lt hf |
    exact f.inf_lt _ | exact f.roundEnv_lt hf _ _

theorem div_lt (hf : f.WF) (e : Env) {a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (f.div e a b).1 < 2 ^ f.width := by
  unfold div
  repeat' split
  all_goals first | exact f.nanResult_lt hf _ (by simp; omega) | exact f.defaultQNaN_lt hf |
    exact f.inf_lt _ | exact f.zero_lt _ | exact f.roundEnv_lt hf _ _

theorem sqrt_lt (hf : f.WF) (e : Env) {a : Nat} (ha : a < 2 ^ f.width) :
    (f.sqrt e a).1 < 2 ^ f.width := by
  unfold sqrt
  repeat' split
  all_goals first | exact f.nanResult_lt hf _ (by simp; omega) | exact ha | exact f.defaultQNaN_lt hf |
    exact f.roundEnv_lt hf _ _

end Format

end Mips.Fp
