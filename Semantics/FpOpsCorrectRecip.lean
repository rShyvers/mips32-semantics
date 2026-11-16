import Semantics.FpOpsCorrectAcc

/-!
# FpOpsCorrectRecip — `1.0 / x` is within one ULP of the exact reciprocal

`recip_error`: for a finite nonzero `x` whose exact reciprocal is at most the largest finite number,
the correctly rounded `1.0 / x` (`Format.div`, no flushing) is finite and within one unit in the
last place of the binade of `1/x` (`binary32`/`binary64`: `f32Recip_error`, `f64Recip_error`).
-/

namespace Mips.Fp

section noov
variable (f : Format) (hf : f.WF)
include hf

/-- The largest finite number is a value of `Unbounded`. -/
theorem maxValue_unbounded : f.Unbounded f.maxValue := by
  refine ⟨((2 ^ f.prec - 1 : Nat) : Int), f.emax - f.fracBits, ?_, ?_, ?_⟩
  · have := Nat.two_pow_pos f.prec; simp only [Int.natAbs_natCast]; omega
  · show f.ulpMin ≤ _
    rw [f.emax_sub, f.ulpMin_eq]; simp only [Format.qMin, Format.qMax]; have := f.bias_pos hf; omega
  · simp only [Format.maxValue, Rat.intCast_natCast]

/-- **No overflow when the exact value is in the finite range.** -/
theorem cr_abs_le_max {rm : RoundingMode} {v r : Rat} (hv : v.abs ≤ f.maxValue)
    (hcr : CorrectlyRounded f.Unbounded f.UnboundedEven rm (Cut.ofRat v) r) : r.abs ≤ f.maxValue := by
  have hM := maxValue_unbounded f hf
  have h0 : f.Unbounded 0 := ⟨0, f.ulpMin, by simp; exact Nat.two_pow_pos _, Int.le_refl _, by simp⟩
  -- the positive case
  have pos : ∀ (rm : RoundingMode) (v r : Rat), 0 ≤ v → v ≤ f.maxValue →
      CorrectlyRounded f.Unbounded f.UnboundedEven rm (Cut.ofRat v) r → 0 ≤ r ∧ r ≤ f.maxValue := by
    intro rm v r h1 h2 hcr
    cases rm
    · obtain ⟨-, k2, k3, -⟩ := hcr
      simp only [Cut.ofRat] at k2 k3
      constructor
      · refine Rat.not_lt.mp fun hlt => ?_
        have := k3 0 h0 hlt; grind
      · refine Rat.not_lt.mp fun hlt => ?_
        have := k2 _ hM hlt; grind
    · obtain ⟨-, k1, k2⟩ := hcr.1 h1
      exact ⟨k2 0 h0 h1, Rat.le_trans k1 h2⟩
    · obtain ⟨-, k1, k2⟩ := hcr
      exact ⟨Rat.le_trans h1 k1, k2 _ hM h2⟩
    · obtain ⟨-, k1, k2⟩ := hcr
      exact ⟨k2 0 h0 h1, Rat.le_trans k1 h2⟩
  rcases rat_lt_or_le v 0 with hn | hp
  · have hva : v.abs = -v := by simp only [Rat.abs]; split <;> grind
    rw [hva] at hv
    have h2 := correctlyRounded_neg f.unbounded_neg f.unboundedEven_neg hcr
    rw [Cut.neg_ofRat] at h2
    have := pos rm.flip (-v) (-r) (by grind) hv h2
    simp only [Rat.abs]; split <;> grind
  · have hva : v.abs = v := Rat.abs_of_nonneg hp
    rw [hva] at hv
    have := pos rm v r hp hv hcr
    simp only [Rat.abs]; split <;> grind

/-- **`1.0 / x` is within one ULP of `1/x`** (no flushing; the exact reciprocal at most the largest
finite number). -/
theorem recip_error (e : Env) (he : e.flush = false) {one x : Nat} {y : Rat}
    (h1 : f.value one = some 1) (hx : f.value x = some y) (hy : y ≠ 0)
    (hrange : (1 / y).abs ≤ f.maxValue) :
    ∃ r, f.value (f.div e one x).1 = some r ∧ (f.div e one x).1 < 2 ^ f.width ∧
      ∃ a : Int, (2 : Rat) ^ a ≤ (1 / y).abs ∧ (1 / y).abs < (2 : Rat) ^ (a + 1) ∧
        (r - 1 / y).abs ≤ (2 : Rat) ^ (max f.ulpMin (a - f.fracBits)) := by
  obtain ⟨R, hR, hdiv⟩ := f.div_correct hf e he h1 hx (by decide) hy
  obtain ⟨r, hcr, hov, hval, -⟩ := hR
  have hrm := cr_abs_le_max f hf hrange hcr
  have hov' : R.overflow = false := by
    cases h : R.overflow
    · rfl
    · exact absurd (hov.1 h) (Rat.not_lt.mpr hrm)
  have hv := hval hov'
  rw [hdiv]
  have hy0 : (1 / y) ≠ 0 := by
    rw [Rat.div_def, Rat.one_mul]; intro h
    have := Rat.mul_inv_cancel y hy; rw [h] at this; simp at this
  have hpos : 0 < (1 / y).abs := by
    simp only [Rat.abs]; split <;> grind
  obtain ⟨a, ha1, ha2⟩ := binade_exists _ hpos
  refine ⟨r, hv, (value_some_lt f hv).1, a, ha1, ha2, cr_ofRat_error f hf hy0 a ?_ ha1 ha2 hcr⟩
  -- `|1/y| ≥ 1 / maxValue > 2^(-emax-1)`, so the binade is above the denormalized unit
  refine Classical.byContradiction fun hlt => ?_
  have hlt' : a + 1 ≤ f.ulpMin := by omega
  have hya := value_abs_le_max f hf hx
  have hmax : f.maxValue < (2 : Rat) ^ (f.emax + 1) := by
    simp only [Format.maxValue]
    rw [show (2 : Rat) ^ (f.emax + 1) = ((2 ^ f.prec : Nat) : Rat) * (2 : Rat) ^ (f.emax - f.fracBits) by
      rw [← two_zpow_nat, ← two_zpow_add]; congr 1; simp only [Format.prec]; omega]
    exact Rat.mul_lt_mul_of_pos_right (Rat.natCast_lt_natCast.2 (by have := Nat.two_pow_pos f.prec; omega))
      (rat_two_zpow_pos _)
  -- `|1/y| · |y| = 1`
  have hprod : (1 / y).abs * y.abs = 1 := by
    have hyy := Rat.mul_inv_cancel y hy
    have hiv : y⁻¹ ≠ 0 := fun h => by rw [h] at hyy; simp at hyy
    have hip := (Rat.inv_pos (a := y))
    rw [Rat.div_def, Rat.one_mul]
    rcases rat_lt_or_le 0 y with h | h
    · have h' := hip.2 h
      rw [Rat.abs_of_nonneg (Rat.le_of_lt h'), Rat.abs_of_nonneg (Rat.le_of_lt h)]; grind
    · have hy' : y < 0 := by grind
      have h' : y⁻¹ < 0 := by
        rcases rat_lt_or_le 0 y⁻¹ with k | k
        · exact absurd (hip.1 k) (by grind)
        · grind
      simp only [Rat.abs]
      rw [ite_neg' (by grind), ite_neg' (by grind)]; grind
  have hb := two_zpow_le hlt'
  have hq : (2 : Rat) ^ f.ulpMin * (2 : Rat) ^ (f.emax + 1) ≤ 1 := by
    rw [← two_zpow_add]
    exact Rat.le_trans (two_zpow_le (show f.ulpMin + (f.emax + 1) ≤ 0 by
      simp only [Format.ulpMin, Format.emin, Format.emax]; have := hf.2; omega)) (by simp)
  have hya0 : 0 ≤ y.abs := Rat.abs_nonneg
  have k1 := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt ha2) hya0
  have k2 := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans hya (Rat.le_of_lt hmax))
    (Rat.le_of_lt (rat_two_zpow_pos (a + 1)))
  have k3 := Rat.mul_le_mul_of_nonneg_right hb (Rat.le_of_lt (rat_two_zpow_pos (f.emax + 1)))
  have k4 : (1 / y).abs * y.abs < (2 : Rat) ^ (a + 1) * y.abs ∨ y.abs = 0 := by
    rcases rat_lt_or_le 0 y.abs with h | h
    · exact .inl (Rat.mul_lt_mul_of_pos_right ha2 h)
    · exact .inr (Rat.le_antisymm h hya0)
  rcases k4 with k4 | k4
  · grind
  · have : y = 0 := by simp only [Rat.abs] at k4; split at k4 <;> grind
    exact hy this

end noov

theorem value_one32 : binary32.value 0x3F800000 = some 1 := by
  rw [show (0x3F800000 : Nat) = binary32.pack false 127 0 by decide,
    binary32.value_pack false 127 0 (by decide) (by decide)]
  simp only [Bool.false_eq_true, ite_false, show (127 : Nat) = 0 ↔ False by decide, Nat.zero_add]
  rw [← two_zpow_nat, Rat.one_mul, ← two_zpow_add]
  congr 1

theorem value_one64 : binary64.value 0x3FF0000000000000 = some 1 := by
  rw [show (0x3FF0000000000000 : Nat) = binary64.pack false 1023 0 by decide,
    binary64.value_pack false 1023 0 (by decide) (by decide)]
  simp only [Bool.false_eq_true, ite_false, show (1023 : Nat) = 0 ↔ False by decide, Nat.zero_add]
  rw [← two_zpow_nat, Rat.one_mul, ← two_zpow_add]
  congr 1

/-- **`RECIP.S` as `1.0 / x` is within one ULP of the exact reciprocal.** -/
theorem f32Recip_error (e : Env) (he : e.flush = false) {x : BitVec 32} {y : Rat}
    (hx : binary32.value x.toNat = some y) (hy : y ≠ 0) (hrange : (1 / y).abs ≤ binary32.maxValue) :
    ∃ r, binary32.value (f32Div e 0x3F800000#32 x).1.toNat = some r ∧
      ∃ a : Int, (2 : Rat) ^ a ≤ (1 / y).abs ∧ (1 / y).abs < (2 : Rat) ^ (a + 1) ∧
        (r - 1 / y).abs ≤ (2 : Rat) ^ (max binary32.ulpMin (a - binary32.fracBits)) := by
  obtain ⟨r, h1, h2, h3⟩ := recip_error binary32 binary32_wf e he value_one32 hx hy hrange
  refine ⟨r, ?_, h3⟩
  simp only [f32Div, BitVec.toNat_ofNat, he, Format.flushIn_false, Format.withFlush_false]
  rw [show (1065353216 % 2 ^ 32 : Nat) = 1065353216 by decide]
  have h2' : (binary32.div e 1065353216 x.toNat).fst < 2 ^ 32 := h2
  rw [Nat.mod_eq_of_lt h2']; exact h1

/-- **`RECIP.D` as `1.0 / x` is within one ULP of the exact reciprocal.** -/
theorem f64Recip_error (e : Env) (he : e.flush = false) {x : BitVec 64} {y : Rat}
    (hx : binary64.value x.toNat = some y) (hy : y ≠ 0) (hrange : (1 / y).abs ≤ binary64.maxValue) :
    ∃ r, binary64.value (f64Div e 0x3FF0000000000000#64 x).1.toNat = some r ∧
      ∃ a : Int, (2 : Rat) ^ a ≤ (1 / y).abs ∧ (1 / y).abs < (2 : Rat) ^ (a + 1) ∧
        (r - 1 / y).abs ≤ (2 : Rat) ^ (max binary64.ulpMin (a - binary64.fracBits)) := by
  obtain ⟨r, h1, h2, h3⟩ := recip_error binary64 binary64_wf e he value_one64 hx hy hrange
  refine ⟨r, ?_, h3⟩
  simp only [f64Div, BitVec.toNat_ofNat, he, Format.flushIn_false, Format.withFlush_false]
  rw [show (4607182418800017408 % 2 ^ 64 : Nat) = 4607182418800017408 by decide]
  have h2' : (binary64.div e 4607182418800017408 x.toNat).fst < 2 ^ 64 := h2
  rw [Nat.mod_eq_of_lt h2']; exact h1

end Mips.Fp
