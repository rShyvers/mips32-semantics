import Semantics.FpOpsCorrectRecip

/-!
# FpOpsCorrectRsqrtAux — lemmas for the `RSQRT` error bound

Comparisons with `1/√y` through squares (`rsqrt_lo`, `rsqrt_hi`), the range of a finite positive
value, and the exact representable values a correct rounding returns unchanged.
-/

namespace Mips.Fp

/-- `1/L ≤ d` and `L ≤ √y` give `1/√y ≤ d`, in the form of `Cut.rsqrt`. -/
theorem rsqrt_lo {L y d : Rat} (hL : 0 < L) (hy : L * L ≤ y) (h : 1 ≤ d * L) :
    0 ≤ d ∧ 1 ≤ d * d * y := by
  have hd : 0 < d := by
    rcases rat_lt_or_le 0 d with k | k
    · exact k
    · have := Rat.mul_le_mul_of_nonneg_right k (Rat.le_of_lt hL); grind
  refine ⟨Rat.le_of_lt hd, ?_⟩
  have k1 := Rat.mul_le_mul_of_nonneg_left hy (Rat.le_of_lt (Rat.mul_pos hd hd))
  have k2 := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt (Rat.mul_pos hd hL))
  grind

/-- `d ≤ 1/H` and `√y ≤ H` give `d ≤ 1/√y`, in the form of `Cut.rsqrt`. -/
theorem rsqrt_hi {H y d : Rat} (hH : 0 < H) (hy : y ≤ H * H) (h : d * H ≤ 1) :
    d ≤ 0 ∨ d * d * y ≤ 1 := by
  rcases rat_lt_or_le 0 d with hd | hd
  · right
    have k1 := Rat.mul_le_mul_of_nonneg_left hy (Rat.le_of_lt (Rat.mul_pos hd hd))
    have k2 := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt (Rat.mul_pos hd hH))
    have k3 : 0 ≤ d * H := Rat.le_of_lt (Rat.mul_pos hd hH)
    have k4 := Rat.mul_le_mul_of_nonneg_right h k3
    grind
  · exact .inl hd

/-- A positive finite value is at least the smallest denormalized number. -/
theorem value_pos_ge (f : Format) {n : Nat} {y : Rat} (h : f.value n = some y) (hy : 0 < y) :
    (2 : Rat) ^ f.qMin ≤ y := by
  have ht := value_toExact f h
  rw [Exact.toRat_signed] at ht
  have hsig : (f.toExact n).sig ≠ 0 := f.toExact_sig_ne_zero h (by grind)
  have hexp : f.qMin ≤ (f.toExact n).exp := by
    simp only [Format.toExact]; split
    · exact Int.le_refl _
    · simp only [Format.qMin]; omega
  cases hs : (f.toExact n).sign
  · rw [hs] at ht; simp only [Bool.false_eq_true, ite_false] at ht
    rw [← ht, show (2 : Rat) ^ f.qMin = ((1 : Nat) : Rat) * (2 : Rat) ^ f.qMin by simp, nat_zpow_le_iff,
      show min f.qMin (f.toExact n).exp = f.qMin by omega, show (f.qMin - f.qMin).toNat = 0 by omega]
    have : 1 ≤ 2 ^ ((f.toExact n).exp - f.qMin).toNat := Nat.one_le_two_pow
    have : 1 * 1 ≤ (f.toExact n).sig * 2 ^ ((f.toExact n).exp - f.qMin).toNat :=
      Nat.mul_le_mul (by omega) this
    simp only [Nat.pow_zero, Nat.one_mul] at *; omega
  · rw [hs] at ht; simp only [ite_true] at ht
    have : 0 ≤ ((f.toExact n).sig : Rat) * (2 : Rat) ^ (f.toExact n).exp :=
      Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (rat_two_zpow_pos _))
    grind

/-- The largest finite number is below `2^(E_max + 1)`. -/
theorem maxValue_lt (f : Format) : f.maxValue < (2 : Rat) ^ (f.emax + 1) := by
  simp only [Format.maxValue]
  rw [show (2 : Rat) ^ (f.emax + 1) = ((2 ^ f.prec : Nat) : Rat) * (2 : Rat) ^ (f.emax - f.fracBits) by
    rw [← two_zpow_nat, ← two_zpow_add]; congr 1; simp only [Format.prec]; omega]
  exact Rat.mul_lt_mul_of_pos_right (Rat.natCast_lt_natCast.2 (by have := Nat.two_pow_pos f.prec; omega))
    (rat_two_zpow_pos _)

/-- `2^E_max` is at most the largest finite number. -/
theorem two_emax_le (f : Format) : (2 : Rat) ^ f.emax ≤ f.maxValue := by
  simp only [Format.maxValue]
  rw [show (2 : Rat) ^ f.emax = ((2 ^ f.fracBits : Nat) : Rat) * (2 : Rat) ^ (f.emax - f.fracBits) by
    rw [← two_zpow_nat, ← two_zpow_add]; congr 1; omega]
  exact Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.2 (by
    simp only [Format.prec]; have : 2 ^ (f.fracBits + 1) = 2 * 2 ^ f.fracBits := Nat.pow_succ'
    have := Nat.two_pow_pos f.fracBits; omega)) (Rat.le_of_lt (rat_two_zpow_pos _))

/-- The binade exponent is determined by the value. -/
theorem binade_le {a b : Int} {v : Rat} (h1 : (2 : Rat) ^ a ≤ v) (h2 : v < (2 : Rat) ^ (b + 1)) : a ≤ b := by
  refine Classical.byContradiction fun h => ?_
  have := two_zpow_le (show b + 1 ≤ a by omega); grind

/-- **The arithmetic of `SQRT` then `DIV`.** `s` is `√y` correctly rounded in the binade
`[A, 2A)` with unit `g`, `t = 1/s`, `d` is `t` correctly rounded with unit `g2 ≤ W`, and
`W · A² = g`. Then `d - W ≤ 1/√y ≤ d + W`. -/
theorem rsqrt_core {y s t d A g W g2 : Rat} (dir : Dir) (hA : 0 < A) (hAs : A ≤ s)
    (hnext : A < s → A + g ≤ s) (hg : 0 < g) (hWAA : W * A * A = g) (hst : s * t = 1)
    (hg2 : g2 ≤ W) (hg20 : 0 < g2) (hAy : A * A ≤ y)
    (hsq : (dir = .nearest → (s - g / 2 ≤ 0 ∨ (s - g / 2) * (s - g / 2) ≤ y) ∧
              (0 ≤ s + g / 2 ∧ y ≤ (s + g / 2) * (s + g / 2))) ∧
           (dir = .down → (s ≤ 0 ∨ s * s ≤ y) ∧ ¬ (s + g ≤ 0 ∨ (s + g) * (s + g) ≤ y)) ∧
           (dir = .up → (0 ≤ s ∧ y ≤ s * s) ∧ ¬ (0 ≤ s - g ∧ y ≤ (s - g) * (s - g))))
    (hdv : (dir = .nearest → t - g2 / 2 ≤ d ∧ d ≤ t + g2 / 2) ∧
           (dir = .down → d ≤ t ∧ t < d + g2) ∧
           (dir = .up → d - g2 < t ∧ t ≤ d)) :
    (d - W ≤ 0 ∨ (d - W) * (d - W) * y ≤ 1) ∧ (0 ≤ d + W ∧ 1 ≤ (d + W) * (d + W) * y) := by
  have hs : 0 < s := by grind
  have ht : 0 < t := by
    rcases rat_lt_or_le 0 t with k | k
    · exact k
    · have := Rat.mul_le_mul_of_nonneg_left k (Rat.le_of_lt hs); grind
  have hW : 0 < W := by grind
  have hy : 0 < y := by have := Rat.mul_pos hA hA; grind
  have hAA : A * A ≤ s * s := by
    have k1 := Rat.mul_le_mul_of_nonneg_left hAs (Rat.le_of_lt hA)
    have k2 := Rat.mul_le_mul_of_nonneg_right hAs (Rat.le_of_lt hs)
    grind
  have htW : 0 ≤ t * W := Rat.le_of_lt (Rat.mul_pos ht hW)
  -- `t g ≤ W s`
  have e0 : t * g = t * W * (A * A) := by rw [← hWAA]; grind
  have ktg : t * g ≤ W * s := by
    have k := Rat.mul_le_mul_of_nonneg_left hAA htW
    have e1 : t * W * (s * s) = W * s * (s * t) := by grind
    rw [hst] at e1
    rw [e0]; grind
  obtain ⟨sN, sD, sU⟩ := hsq
  obtain ⟨dN, dD, dU⟩ := hdv
  cases dir
  · -- down
    obtain ⟨⟨h1 | h1, h2⟩, ⟨d1, d2⟩⟩ := And.intro (sD rfl) (dD rfl)
    · grind
    have hH : 0 < s + g := by grind
    have hyH : y ≤ (s + g) * (s + g) := by
      rcases rat_lt_or_le y ((s + g) * (s + g)) with k | k
      · exact Rat.le_of_lt k
      · exact absurd (.inr k) h2
    refine ⟨rsqrt_hi hH hyH ?_, rsqrt_lo hs h1 ?_⟩
    · have := Rat.mul_le_mul_of_nonneg_right (show d - W ≤ t - W by grind) (Rat.le_of_lt hH)
      have : W * g ≥ 0 := Rat.le_of_lt (Rat.mul_pos hW hg)
      grind
    · have := Rat.mul_le_mul_of_nonneg_right (show t ≤ d + W by grind) (Rat.le_of_lt hs)
      grind
  · -- up
    obtain ⟨⟨⟨-, h1⟩, h2⟩, ⟨d1, d2⟩⟩ := And.intro (sU rfl) (dU rfl)
    refine ⟨rsqrt_hi hs h1 ?_, ?_⟩
    · have := Rat.mul_le_mul_of_nonneg_right (show d - W ≤ t by grind) (Rat.le_of_lt hs)
      grind
    · rcases rat_lt_or_le A s with hlt | hge
      · have hsg := hnext hlt
        have hL : 0 < s - g := by grind
        have hLy : (s - g) * (s - g) ≤ y := by
          rcases rat_lt_or_le ((s - g) * (s - g)) y with k | k
          · exact Rat.le_of_lt k
          · exact absurd ⟨Rat.le_of_lt hL, k⟩ h2
        refine rsqrt_lo hL hLy ?_
        have k1 : A * A ≤ s * (s - g) := by
          have := Rat.mul_le_mul_of_nonneg_left (show A ≤ s - g by grind) (Rat.le_of_lt hA)
          have := Rat.mul_le_mul_of_nonneg_right hAs (Rat.le_of_lt hL)
          grind
        have k2 := Rat.mul_le_mul_of_nonneg_left k1 htW
        have e1 : t * W * (s * (s - g)) = W * (s - g) * (s * t) := by grind
        rw [hst] at e1
        have := Rat.mul_le_mul_of_nonneg_right (show t + W ≤ d + W by grind) (Rat.le_of_lt hL)
        grind
      · have hsA : s = A := Rat.le_antisymm hge hAs
        refine rsqrt_lo hA hAy ?_
        have := Rat.mul_le_mul_of_nonneg_right (show t ≤ d + W by grind) (Rat.le_of_lt hA)
        grind
  · -- nearest
    obtain ⟨⟨h1, ⟨-, h2⟩⟩, ⟨d1, d2⟩⟩ := And.intro (sN rfl) (dN rfl)
    have hH : 0 < s + g / 2 := by grind
    refine ⟨rsqrt_hi hH h2 ?_, ?_⟩
    · have := Rat.mul_le_mul_of_nonneg_right (show d - W ≤ t - W / 2 by grind) (Rat.le_of_lt hH)
      have : W * g ≥ 0 := Rat.le_of_lt (Rat.mul_pos hW hg)
      grind
    · rcases rat_lt_or_le A s with hlt | hge
      · have hsg := hnext hlt
        have hL : 0 < s - g / 2 := by grind
        have hLy : (s - g / 2) * (s - g / 2) ≤ y := by
          rcases h1 with k | k
          · grind
          · exact k
        refine rsqrt_lo hL hLy ?_
        have k1 : 2 * (A * A) ≤ s * (2 * s - g) := by
          have := Rat.mul_le_mul_of_nonneg_left (show 2 * A ≤ 2 * s - g by grind) (Rat.le_of_lt hA)
          have := Rat.mul_le_mul_of_nonneg_right hAs (show 0 ≤ 2 * s - g by grind)
          grind
        have k2 := Rat.mul_le_mul_of_nonneg_left k1 htW
        have e1 : t * W * (s * (2 * s - g)) = W * (2 * s - g) * (s * t) := by grind
        rw [hst] at e1
        have := Rat.mul_le_mul_of_nonneg_right (show t + W / 2 ≤ d + W by grind) (Rat.le_of_lt hL)
        grind
      · have hsA : s = A := Rat.le_antisymm hge hAs
        refine rsqrt_lo hA hAy ?_
        have := Rat.mul_le_mul_of_nonneg_right (show t ≤ d + W by grind) (Rat.le_of_lt hA)
        grind

end Mips.Fp
