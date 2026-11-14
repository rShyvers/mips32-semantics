import Semantics.FpOpsCorrectRsqrtAux

/-!
# FpOpsCorrectRsqrt — `SQRT.fmt` then `DIV.fmt` is within two ULP of `1/√x`

`rsqrt_error`: for a finite positive `x`, the model's reciprocal square root (`1.0 / sqrt x`, two
correct roundings, no flushing) is finite and within two units in the last place (of the binade of
`1/√x`) of the exact `1/√x` (RSQRT.fmt, MD00086 Vol II-A Rev 6.06 p.343). Stated by squares:
`r - 2U ≤ 1/√x ≤ r + 2U`.
-/

namespace Mips.Fp

/-- Widening the error bound from `W` to `2U ≥ W`. -/
theorem rsqrt_widen {d W V y : Rat} (hWV : W ≤ V) (hy : 0 ≤ y)
    (h : (d - W ≤ 0 ∨ (d - W) * (d - W) * y ≤ 1) ∧ (0 ≤ d + W ∧ 1 ≤ (d + W) * (d + W) * y)) :
    (d - V ≤ 0 ∨ (d - V) * (d - V) * y ≤ 1) ∧ (0 ≤ d + V ∧ 1 ≤ (d + V) * (d + V) * y) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, by grind, ?_⟩
  · rcases rat_lt_or_le 0 (d - V) with hp | hp
    · right
      rcases h1 with k | k
      · grind
      · have k1 := Rat.mul_le_mul_of_nonneg_left (show d - V ≤ d - W by grind) (Rat.le_of_lt hp)
        have k2 := Rat.mul_le_mul_of_nonneg_right (show d - V ≤ d - W by grind) (show 0 ≤ d - W by grind)
        have k3 := Rat.mul_le_mul_of_nonneg_right (Rat.le_trans k1 k2) hy
        grind
    · exact .inl hp
  · have k1 := Rat.mul_le_mul_of_nonneg_left (show d + W ≤ d + V by grind) h2
    have k2 := Rat.mul_le_mul_of_nonneg_right (show d + W ≤ d + V by grind) (show 0 ≤ d + V by grind)
    have k3 := Rat.mul_le_mul_of_nonneg_right (Rat.le_trans k1 k2) hy
    grind

theorem near_swap {d t g : Rat} (h : d - g / 2 ≤ t ∧ t ≤ d + g / 2) : t - g / 2 ≤ d ∧ d ≤ t + g / 2 := by
  obtain ⟨h1, h2⟩ := h; constructor <;> grind

theorem down_swap {d t g : Rat} (h : d ≤ t ∧ ¬ d + g ≤ t) : d ≤ t ∧ t < d + g := by
  obtain ⟨h1, h2⟩ := h; exact ⟨h1, Rat.not_le.mp h2⟩

theorem up_swap {d t g : Rat} (h : t ≤ d ∧ ¬ t ≤ d - g) : d - g < t ∧ t ≤ d := by
  obtain ⟨h1, h2⟩ := h; exact ⟨Rat.not_le.mp h2, h1⟩

theorem one_div_pos {s : Rat} (hs : 0 < s) : 0 < 1 / s ∧ s * (1 / s) = 1 := by
  rw [Rat.div_def, Rat.one_mul]
  exact ⟨Rat.inv_pos.2 hs, Rat.mul_inv_cancel s (by grind)⟩

section rsq
variable (f : Format) (hf : f.WF) (hb : f.fracBits + 2 ≤ f.bias) (hb4 : 4 ≤ f.bias)
include hf hb hb4

/-- **The model's `RSQRT` is within two ULP of `1/√x`.** -/
theorem rsqrt_error (e : Env) (he : e.flush = false) {one x : Nat} {y : Rat}
    (h1 : f.value one = some 1) (hx : f.value x = some y) (hy : 0 < y) :
    ∃ r, f.value (f.div e one (f.sqrt e x).1).1 = some r ∧
      (f.div e one (f.sqrt e x).1).1 < 2 ^ f.width ∧ (f.sqrt e x).1 < 2 ^ f.width ∧
      ∃ ex : Int, (2 : Rat) ^ ex * (2 : Rat) ^ ex * y ≤ 1 ∧ 1 < (2 : Rat) ^ (ex + 1) * (2 : Rat) ^ (ex + 1) * y ∧
        (r - 2 * (2 : Rat) ^ (max f.ulpMin (ex - f.fracBits)) ≤ 0 ∨
          (r - 2 * (2 : Rat) ^ (max f.ulpMin (ex - f.fracBits))) *
            (r - 2 * (2 : Rat) ^ (max f.ulpMin (ex - f.fracBits))) * y ≤ 1) ∧
        (0 ≤ r + 2 * (2 : Rat) ^ (max f.ulpMin (ex - f.fracBits)) ∧
          1 ≤ (r + 2 * (2 : Rat) ^ (max f.ulpMin (ex - f.fracBits))) *
            (r + 2 * (2 : Rat) ^ (max f.ulpMin (ex - f.fracBits))) * y) := by
  have hqm := f.qMin_eq
  have hul := f.ulpMin_eq
  have hqM := f.qMax_eq
  have hem : f.emax = (f.bias : Int) := rfl
  -- the range of `y`
  have hymin := value_pos_ge f hx hy
  have hymax : y ≤ f.maxValue := by
    have := value_abs_le_max f hf hx; rwa [Rat.abs_of_nonneg (Rat.le_of_lt hy)] at this
  have hMlt := maxValue_lt f
  obtain ⟨b, hb1, hb2⟩ := binade_exists y hy
  have hbmin : f.qMin ≤ b := binade_le hymin hb2
  have hbmax : b ≤ f.emax := binade_le hb1 (by grind)
  generalize ha : b / 2 = a
  have hab : 2 * a ≤ b ∧ b ≤ 2 * a + 1 := by omega
  have hAA : (2 : Rat) ^ a * (2 : Rat) ^ a ≤ y := by
    rw [← two_zpow_add]; exact Rat.le_trans (two_zpow_le (by omega)) hb1
  have hyB : y < (2 : Rat) ^ (a + 1) * (2 : Rat) ^ (a + 1) := by
    rw [← two_zpow_add]; have := two_zpow_le (show b + 1 ≤ a + 1 + (a + 1) by omega); grind
  have hA := rat_two_zpow_pos a
  -- `SQRT`
  obtain ⟨R1, hR1, hsq⟩ := f.sqrt_correct hf e he hx hy
  obtain ⟨s, hcr1, hov1, hval1, -⟩ := hR1
  have hlo1 : (Cut.sqrt y).le ((2 : Rat) ^ a) := .inr hAA
  have hhi1 : ¬ (Cut.sqrt y).le ((2 : Rat) ^ (a + 1)) := by
    rintro (k | k)
    · have := rat_two_zpow_pos (a + 1); grind
    · grind
  have hua : f.ulpMin ≤ a := by omega
  obtain ⟨sA, sB, snext, sN, sD, sU⟩ := binade_bounds f hf (Cut.sqrt_valid y) a hua hlo1 hhi1 hcr1
  rw [show max f.ulpMin (a - f.fracBits) = a - f.fracBits by omega] at snext sN sD sU
  have hs : 0 < s := by grind
  have hsmax : s.abs ≤ f.maxValue := by
    rw [Rat.abs_of_nonneg (Rat.le_of_lt hs)]
    exact Rat.le_trans sB (Rat.le_trans (two_zpow_le (by omega)) (two_emax_le f))
  have hov1' : R1.overflow = false := by
    cases h : R1.overflow
    · rfl
    · exact absurd (hov1.1 h) (Rat.not_lt.mpr hsmax)
  have hv1 := hval1 hov1'
  -- `DIV`
  obtain ⟨R2, hR2, hdv⟩ := f.div_correct hf e he h1 hv1 (by decide) (by grind)
  obtain ⟨d, hcr2, hov2, hval2, -⟩ := hR2
  obtain ⟨ht0, hst⟩ := one_div_pos hs
  generalize htd : 1 / s = t at ht0 hst hcr2
  have htA : t ≤ (2 : Rat) ^ (-a) := by
    have e1 : (2 : Rat) ^ (-a) * (2 : Rat) ^ a = 1 := by
      rw [← two_zpow_add, show -a + a = (0 : Int) by omega, Rat.zpow_zero]
    have k := Rat.mul_le_mul_of_nonneg_left sA (Rat.le_of_lt ht0)
    have k1 : t * (2 : Rat) ^ a ≤ 1 := by grind
    have k2 := Rat.mul_le_mul_of_nonneg_left k1 (Rat.le_of_lt (rat_two_zpow_pos (-a)))
    have e2 : (2 : Rat) ^ (-a) * (t * (2 : Rat) ^ a) = t * ((2 : Rat) ^ (-a) * (2 : Rat) ^ a) := by grind
    rw [e2, e1] at k2; grind
  have htB : (2 : Rat) ^ (-a - 1) ≤ t := by
    have e1 : (2 : Rat) ^ (-a - 1) * (2 : Rat) ^ (a + 1) = 1 := by
      rw [← two_zpow_add, show -a - 1 + (a + 1) = (0 : Int) by omega, Rat.zpow_zero]
    have k := Rat.mul_le_mul_of_nonneg_left sB (Rat.le_of_lt ht0)
    have k1 : 1 ≤ t * (2 : Rat) ^ (a + 1) := by grind
    have k2 := Rat.mul_le_mul_of_nonneg_left k1 (Rat.le_of_lt (rat_two_zpow_pos (-a - 1)))
    have e2 : (2 : Rat) ^ (-a - 1) * (t * (2 : Rat) ^ (a + 1)) =
        t * ((2 : Rat) ^ (-a - 1) * (2 : Rat) ^ (a + 1)) := by grind
    rw [e2, e1] at k2; grind
  have htmax : t.abs ≤ f.maxValue := by
    rw [Rat.abs_of_nonneg (Rat.le_of_lt ht0)]
    exact Rat.le_trans htA (Rat.le_trans (two_zpow_le (by omega)) (two_emax_le f))
  have hdmax := cr_abs_le_max f hf htmax hcr2
  have hov2' : R2.overflow = false := by
    cases h : R2.overflow
    · rfl
    · exact absurd (hov2.1 h) (Rat.not_lt.mpr hdmax)
  have hv2 := hval2 hov2'
  obtain ⟨b', hb'1, hb'2⟩ := binade_exists t ht0
  have hb'max : b' ≤ -a := binade_le hb'1 (by have := two_zpow_lt (show -a < -a + 1 by omega); grind)
  have hb'min : -a - 1 ≤ b' := binade_le htB hb'2
  obtain ⟨-, -, -, dN, dD, dU⟩ := binade_bounds f hf (Cut.ofRat_valid t) b' (by omega) hb'1
    (Rat.not_le.mpr hb'2) hcr2
  rw [show max f.ulpMin (b' - f.fracBits) = b' - f.fracBits by omega] at dN dD dU
  simp only [Cut.ofRat] at dN dD dU
  -- the error
  have hg1 := rat_two_zpow_pos (a - f.fracBits)
  have hg2 := rat_two_zpow_pos (b' - f.fracBits)
  have hWAA : (2 : Rat) ^ (-a - f.fracBits) * (2 : Rat) ^ a * (2 : Rat) ^ a = (2 : Rat) ^ (a - f.fracBits) := by
    rw [← two_zpow_add, ← two_zpow_add]; congr 1; omega
  have hgW : (2 : Rat) ^ (b' - f.fracBits) ≤ (2 : Rat) ^ (-a - f.fracBits) := two_zpow_le (by omega)
  have core := rsqrt_core (dirOf e.rm false) hA sA snext hg1 hWAA hst hgW hg2 hAA
    ⟨fun h => by
        cases hr : e.rm <;> simp [dirOf, hr] at h
        exact sN hr,
      fun h => sD h, fun h => sU h⟩
    ⟨fun h => by
        cases hr : e.rm <;> simp [dirOf, hr] at h
        exact near_swap (dN hr),
      fun h => down_swap (dD h), fun h => up_swap (dU h)⟩
  -- the binade of `1/√y` and the widening to `2U`
  have hsq1 : (f.sqrt e x).1 = R1.bits := by rw [hsq]
  have hdv1 : (f.div e one (f.sqrt e x).1).1 = R2.bits := by rw [hsq1, hdv]
  rw [hdv1, hsq1]
  refine ⟨d, hv2, (value_some_lt f hv2).1, (value_some_lt f hv1).1, ?_⟩
  have hW2 : ∀ ex : Int, -a - 1 ≤ ex →
      (2 : Rat) ^ (-a - f.fracBits) ≤ 2 * (2 : Rat) ^ (max f.ulpMin (ex - f.fracBits)) := by
    intro ex hex
    have k := two_zpow_le (show -a - 1 - f.fracBits ≤ max f.ulpMin (ex - f.fracBits) by omega)
    have e1 : (2 : Rat) ^ (-a - f.fracBits) = 2 * (2 : Rat) ^ (-a - 1 - f.fracBits) := by
      rw [show -a - f.fracBits = (-a - 1 - f.fracBits) + 1 by omega, Rat.zpow_add_one (by decide)]; grind
    grind
  have hyy := Rat.le_of_lt hy
  have hneg : (2 : Rat) ^ (-a) * (2 : Rat) ^ (-a) * ((2 : Rat) ^ a * (2 : Rat) ^ a) = 1 := by
    rw [← two_zpow_add, ← two_zpow_add, ← two_zpow_add, show -a + -a + (a + a) = (0 : Int) by omega,
      Rat.zpow_zero]
  rcases rat_lt_or_le ((2 : Rat) ^ a * (2 : Rat) ^ a) y with hlt | hge
  · -- `1/√y` is strictly inside `(2^(-a-1), 2^(-a))`
    refine ⟨-a - 1, ?_, ?_, rsqrt_widen (hW2 _ (Int.le_refl _)) hyy core⟩
    · have e1 : (2 : Rat) ^ (-a - 1) * (2 : Rat) ^ (-a - 1) * ((2 : Rat) ^ (a + 1) * (2 : Rat) ^ (a + 1)) = 1 := by
        rw [← two_zpow_add, ← two_zpow_add, ← two_zpow_add,
          show -a - 1 + (-a - 1) + (a + 1 + (a + 1)) = (0 : Int) by omega, Rat.zpow_zero]
      have k := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hyB)
        (Rat.le_of_lt (Rat.mul_pos (rat_two_zpow_pos (-a - 1)) (rat_two_zpow_pos (-a - 1))))
      grind
    · rw [show -a - 1 + 1 = -a by omega]
      have k := Rat.mul_lt_mul_of_pos_left hlt
        (Rat.mul_pos (rat_two_zpow_pos (-a)) (rat_two_zpow_pos (-a)))
      grind
  · -- `y = 2^(2a)`: `1/√y = 2^(-a)`
    have hyA : y = (2 : Rat) ^ a * (2 : Rat) ^ a := Rat.le_antisymm hge hAA
    refine ⟨-a, ?_, ?_, rsqrt_widen (hW2 _ (by omega)) hyy core⟩
    · rw [hyA, hneg]; exact Rat.le_refl
    · rw [hyA]
      have e1 : (2 : Rat) ^ (-a + 1) * (2 : Rat) ^ (-a + 1) * ((2 : Rat) ^ a * (2 : Rat) ^ a) = 4 := by
        rw [← two_zpow_add, ← two_zpow_add, ← two_zpow_add,
          show -a + 1 + (-a + 1) + (a + a) = ((2 : Nat) : Int) by omega, two_zpow_nat]; rfl
      rw [e1]; decide

end rsq

end Mips.Fp
