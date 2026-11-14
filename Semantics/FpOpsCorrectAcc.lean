import Semantics.FpOpsCorrectApi

/-!
# FpOpsCorrectAcc — error bounds of correct rounding

`binade_bounds`: a correctly rounded value `s` of a positive exact value `v` in the binade
`[2^a, 2^(a+1))` lies in `[2^a, 2^(a+1)]`, and with `g = 2^max(qmin, a - p + 1)` (the unit in the
last place of the binade): RN gives `s - g/2 ≤ v ≤ s + g/2`, rounding down `s ≤ v < s + g`, rounding
up `s - g < v ≤ s`. `cr_ofRat_error`: `|r - v| ≤ g` for a rational `v` of either sign.
-/

namespace Mips.Fp

theorem rat_le_of_eq {a b : Rat} (h : a = b) : a ≤ b := h ▸ Rat.le_refl

section binade
variable (f : Format) (hf : f.WF)
include hf

theorem binade_gridHyp (a : Int) :
    GridHyp f.Unbounded f.UnboundedEven f.prec
      ((2 : Rat) ^ (max f.ulpMin (a - f.fracBits) - 1))
      (((2 * (if f.ulpMin ≤ a - f.fracBits then 2 ^ (f.prec - 1) else 0) : Int) : Rat) *
        (2 : Rat) ^ (max f.ulpMin (a - f.fracBits) - 1)) :=
  f.gridHyp_unbounded hf (by omega) _ (by
    split
    · exact .inl rfl
    · exact .inr ⟨rfl, by omega⟩)

/-- The grid point `L` of `binade_gridHyp` is at most `2^a`, and `2^b` (for `a ≤ b ≤ a + 1`) is a
grid point with index at most `2^p`. -/
theorem binade_facts (a : Int) (ha : f.ulpMin ≤ a) :
    (((2 * (if f.ulpMin ≤ a - f.fracBits then 2 ^ (f.prec - 1) else 0) : Int) : Rat) *
        (2 : Rat) ^ (max f.ulpMin (a - f.fracBits) - 1) ≤ (2 : Rat) ^ a) ∧
    (∀ b : Int, a ≤ b → b ≤ a + 1 →
      (2 : Rat) ^ b = ((2 * (2 ^ (b - max f.ulpMin (a - f.fracBits)).toNat : Nat) : Int) : Rat) *
        (2 : Rat) ^ (max f.ulpMin (a - f.fracBits) - 1) ∧
      2 ^ (b - max f.ulpMin (a - f.fracBits)).toNat ≤ 2 ^ f.prec) := by
  have hp := f.prec_ge hf
  refine ⟨?_, fun b hb1 hb2 => ⟨?_, ?_⟩⟩
  · split
    · rename_i h
      rw [← half_grid, show max f.ulpMin (a - f.fracBits) = a - f.fracBits by omega]
      rw [show ((2 ^ (f.prec - 1) : Int) : Rat) = ((2 ^ (f.prec - 1) : Nat) : Rat) by
        rw [← int_two_pow]; rfl, ← two_zpow_nat, ← two_zpow_add]
      apply rat_le_of_eq; congr 1; simp only [Format.prec]; omega
    · simp only [Int.mul_zero, Rat.intCast_zero, Rat.zero_mul]
      exact Rat.le_of_lt (rat_two_zpow_pos a)
  · rw [← half_grid, Rat.intCast_natCast, ← two_zpow_nat, ← two_zpow_add]; congr 1; omega
  · exact Nat.pow_le_pow_right (by omega) (by simp only [Format.prec]; omega)

/-- **Bounds of a correctly rounded value in its binade.** -/
theorem binade_bounds {c : Cut} (hc : c.Valid) (a : Int) (ha : f.ulpMin ≤ a)
    (hlo : c.le ((2 : Rat) ^ a)) (hhi : ¬ c.le ((2 : Rat) ^ (a + 1))) {rm : RoundingMode} {s : Rat}
    (hcr : CorrectlyRounded f.Unbounded f.UnboundedEven rm c s) :
    (2 : Rat) ^ a ≤ s ∧ s ≤ (2 : Rat) ^ (a + 1) ∧
    ((2 : Rat) ^ a < s → (2 : Rat) ^ a + (2 : Rat) ^ (max f.ulpMin (a - f.fracBits)) ≤ s) ∧
    (rm = .RN → c.le (s - (2 : Rat) ^ (max f.ulpMin (a - f.fracBits)) / 2) ∧
      c.ge (s + (2 : Rat) ^ (max f.ulpMin (a - f.fracBits)) / 2)) ∧
    (dirOf rm false = .down → c.le s ∧ ¬ c.le (s + (2 : Rat) ^ (max f.ulpMin (a - f.fracBits)))) ∧
    (dirOf rm false = .up → c.ge s ∧ ¬ c.ge (s - (2 : Rat) ^ (max f.ulpMin (a - f.fracBits)))) := by
  have G := binade_gridHyp f hf a
  obtain ⟨hL, hpt⟩ := binade_facts f hf a ha
  generalize hq : max f.ulpMin (a - f.fracBits) = q at G hL hpt
  generalize hL' : (((2 * (if f.ulpMin ≤ a - f.fracBits then 2 ^ (f.prec - 1) else 0) : Int) : Rat) *
      (2 : Rat) ^ (q - 1)) = L at G hL
  have hh := G.h_pos
  have hgq : (2 : Rat) ^ q = 2 * (2 : Rat) ^ (q - 1) := two_zpow_pred q
  obtain ⟨eA, jA⟩ := hpt a (Int.le_refl _) (by omega)
  obtain ⟨eB, jB⟩ := hpt (a + 1) (by omega) (Int.le_refl _)
  have hA : f.Unbounded ((2 : Rat) ^ a) := by
    rw [eA]; exact G.S_grid _ (Int.natCast_nonneg _) (by have := int_two_pow f.prec; omega)
  have hB : f.Unbounded ((2 : Rat) ^ (a + 1)) := by
    rw [eB]; exact G.S_grid _ (Int.natCast_nonneg _) (by have := int_two_pow f.prec; omega)
  have hAB : (2 : Rat) ^ a < (2 : Rat) ^ (a + 1) := two_zpow_lt (by omega)
  have hpos : ¬ c.ge 0 := fun h0 => by
    have := hc.le_ge _ _ hlo h0; have := rat_two_zpow_pos a; grind
  have hgeB : c.ge ((2 : Rat) ^ (a + 1)) := hc.ge_of_not_le hhi
  have hle0 : c.le 0 := hc.le_of_not_ge hpos
  -- step 1: `2^a ≤ s ≤ 2^(a+1)`
  have hs : (2 : Rat) ^ a ≤ s ∧ s ≤ (2 : Rat) ^ (a + 1) := by
    cases rm
    · obtain ⟨-, h2, h3, -⟩ := hcr
      constructor
      · refine Rat.not_lt.mp fun hlt => ?_
        have := hc.le_ge _ _ hlo (h3 _ hA hlt); grind
      · refine Rat.not_lt.mp fun hlt => ?_
        have := hc.le_ge _ _ (h2 _ hB hlt) hgeB; grind
    · obtain ⟨-, h1, h2⟩ := hcr.1 hle0
      exact ⟨h2 _ hA hlo, hc.le_ge _ _ h1 hgeB⟩
    · obtain ⟨-, h1, h2⟩ := hcr
      exact ⟨hc.le_ge _ _ hlo h1, h2 _ hB hgeB⟩
    · obtain ⟨-, h1, h2⟩ := hcr
      exact ⟨h2 _ hA hlo, hc.le_ge _ _ h1 hgeB⟩
  -- step 2: `s` is a grid point `i · 2^q`
  have hsS : f.Unbounded s := by
    cases rm
    · exact hcr.1
    · exact (hcr.1 hle0).1
    · exact hcr.1
    · exact hcr.1
  obtain ⟨i, hi⟩ : ∃ i : Int, s = ((2 * i : Int) : Rat) * (2 : Rat) ^ (q - 1) := by
    rcases G.S_off s hsS with h | h
    · exact h
    · have := Rat.le_trans hL hs.1; grind
  -- the index of `s`
  have hiA := (pt_le hh).1 (eA ▸ hi ▸ hs.1)
  have hiB := (pt_le hh).1 (hi ▸ eB ▸ hs.2)
  have hnA : (1 : Int) ≤ ((2 ^ (a - q).toNat : Nat) : Int) := by
    have := Nat.one_le_two_pow (n := (a - q).toNat); omega
  have hpI := int_two_pow f.prec
  have sp : s + (2 : Rat) ^ q = ((2 * (i + 1) : Int) : Rat) * (2 : Rat) ^ (q - 1) := by
    rw [hi, hgq]; push_cast; grind
  have sm : s - (2 : Rat) ^ q = ((2 * (i - 1) : Int) : Rat) * (2 : Rat) ^ (q - 1) := by
    rw [hi, hgq]; push_cast; grind
  have hSm : f.Unbounded (s - (2 : Rat) ^ q) := by
    rw [sm]; exact G.S_grid _ (by omega) (by omega)
  have hgpos := rat_two_zpow_pos q
  refine ⟨hs.1, hs.2, fun hlt => ?_, fun hrm => ?_, fun hd => ?_, fun hd => ?_⟩
  · have := (pt_lt hh).1 (eA ▸ hi ▸ hlt)
    rw [eA, hi, hgq]
    have : ((2 * ((2 ^ (a - q).toNat : Nat) : Int) : Int) : Rat) * (2 : Rat) ^ (q - 1) +
        2 * (2 : Rat) ^ (q - 1) = ((2 * (((2 ^ (a - q).toNat : Nat) : Int) + 1) : Int) : Rat) * (2 : Rat) ^ (q - 1) := by
      push_cast; grind
    rw [this]; exact (pt_le hh).2 (by omega)
  · subst hrm
    obtain ⟨-, h2, h3, -⟩ := hcr
    constructor
    · have := h2 _ hSm (by grind)
      rw [show (s - (2 : Rat) ^ q + s) / 2 = s - (2 : Rat) ^ q / 2 by grind] at this
      exact this
    · rcases Int.lt_or_le i (2 ^ f.prec) with hlt | hge
      · have hSp : f.Unbounded (s + (2 : Rat) ^ q) := by
          rw [sp]; exact G.S_grid _ (by omega) (by omega)
        have := h3 _ hSp (by grind)
        rw [show (s + (s + (2 : Rat) ^ q)) / 2 = s + (2 : Rat) ^ q / 2 by grind] at this
        exact this
      · have hsB : (2 : Rat) ^ (a + 1) ≤ s := by
          rw [eB, hi]; exact (pt_le hh).2 (by omega)
        exact hc.ge_of_le _ _ (by grind) hgeB
  · have hdown : RoundDown f.Unbounded c s := by
      cases rm
      · simp [dirOf] at hd
      · exact hcr.1 hle0
      · simp [dirOf] at hd
      · exact hcr
    refine ⟨hdown.2.1, fun hle => ?_⟩
    rcases Int.lt_or_le i (2 ^ f.prec) with hlt | hge
    · have hSp : f.Unbounded (s + (2 : Rat) ^ q) := by
        rw [sp]; exact G.S_grid _ (by omega) (by omega)
      have := hdown.2.2 _ hSp hle; grind
    · have hsB : (2 : Rat) ^ (a + 1) ≤ s := by
        rw [eB, hi]; exact (pt_le hh).2 (by omega)
      exact hhi (hc.le_of_le _ _ (by grind) hle)
  · have hup : RoundUp f.Unbounded c s := by
      cases rm
      · simp [dirOf] at hd
      · simp [dirOf] at hd
      · exact hcr
      · simp [dirOf] at hd
    refine ⟨hup.2.1, fun hge => ?_⟩
    have := hup.2.2 _ hSm hge; grind

end binade

/-! ## The binade of a positive rational -/

theorem binade_exists (v : Rat) (hv : 0 < v) : ∃ a : Int, (2 : Rat) ^ a ≤ v ∧ v < (2 : Rat) ^ (a + 1) := by
  -- scale `v` by `2^K` until it is at least 1
  have hden : 0 < v.den := v.den_pos
  have hvd : v = (v.num : Rat) / (v.den : Rat) := by
    have := Rat.num_divInt_den v
    rw [Rat.divInt_eq_div] at this
    exact this.symm
  have hnum : 0 < v.num := by
    have h0 : 0 ≤ v.num := Rat.num_nonneg.2 (Rat.le_of_lt hv)
    refine Classical.byContradiction fun h => ?_
    have : v.num = 0 := by omega
    rw [this] at hvd; simp at hvd; grind
  generalize hK : bitLen v.den = K
  have hdK : v.den < 2 ^ K := hK ▸ lt_two_pow_bitLen v.den
  have hKpos : (0 : Rat) < (2 : Rat) ^ (K : Int) := rat_two_zpow_pos _
  have h1 : (1 : Rat) ≤ v * (2 : Rat) ^ (K : Int) := by
    have hd' : (0 : Rat) < (v.den : Rat) := Rat.natCast_pos.2 hden
    have e : v * (2 : Rat) ^ (K : Int) = ((v.num : Rat) * ((2 ^ K : Nat) : Rat)) / (v.den : Rat) := by
      rw [hvd, two_zpow_nat, Rat.div_def, Rat.div_def]; grind
    rw [e, rat_le_div_iff hd', Rat.one_mul]
    have h2 : ((v.den : Nat) : Rat) ≤ ((2 ^ K : Nat) : Rat) := Rat.natCast_le_natCast.2 (Nat.le_of_lt hdK)
    have hn1 : (1 : Rat) ≤ (v.num : Rat) := by
      have : (1 : Int) ≤ v.num := hnum
      exact_mod_cast this
    have h3 := Rat.mul_le_mul_of_nonneg_right hn1 (Rat.natCast_nonneg (a := 2 ^ K))
    grind
  generalize hm : (v * (2 : Rat) ^ (K : Int)).floor = m
  have hm1 : 1 ≤ m := by rw [← hm]; exact Rat.le_floor_iff.2 (by simpa using h1)
  have hmle : (m : Rat) ≤ v * (2 : Rat) ^ (K : Int) := hm ▸ Rat.floor_le _
  have hmlt : v * (2 : Rat) ^ (K : Int) < ((m + 1 : Int) : Rat) := hm ▸ Rat.lt_floor_add_one _
  have hb1 := lt_two_pow_bitLen m.toNat
  have hb2 := two_pow_bitLen_le m.toNat (by omega)
  have hb3 := bitLen_pos m.toNat (by omega)
  refine ⟨(bitLen m.toNat : Int) - 1 - K, ?_, ?_⟩
  · -- `2^(b-1) ≤ m ≤ v 2^K`
    have : ((2 ^ (bitLen m.toNat - 1) : Nat) : Rat) ≤ (m : Rat) := by
      have : ((2 ^ (bitLen m.toNat - 1) : Nat) : Int) ≤ m := by omega
      exact_mod_cast this
    rw [← two_zpow_nat] at this
    have e : (2 : Rat) ^ ((bitLen m.toNat : Int) - 1 - K) * (2 : Rat) ^ (K : Int) =
        (2 : Rat) ^ (((bitLen m.toNat - 1 : Nat) : Int)) := by
      rw [← two_zpow_add]; congr 1; omega
    rw [← rat_mul_le_iff hKpos, e]; grind
  · have : ((m + 1 : Int) : Rat) ≤ ((2 ^ (bitLen m.toNat) : Nat) : Rat) := by
      have : (m + 1 : Int) ≤ ((2 ^ (bitLen m.toNat) : Nat) : Int) := by omega
      exact_mod_cast this
    rw [← two_zpow_nat] at this
    have e : (2 : Rat) ^ ((bitLen m.toNat : Int) - 1 - K + 1) * (2 : Rat) ^ (K : Int) =
        (2 : Rat) ^ ((bitLen m.toNat : Nat) : Int) := by
      rw [← two_zpow_add]; congr 1; omega
    rw [← rat_mul_lt_iff hKpos, e]; grind

/-! ## Error of a correctly rounded rational -/

theorem Cut.neg_ofRat (v : Rat) : (Cut.ofRat v).neg = Cut.ofRat (-v) := by
  simp only [Cut.neg, Cut.ofRat]
  congr 1 <;> funext y <;> apply propext <;> constructor <;> intro h <;> grind

theorem rat_abs_le_iff {x g : Rat} : x.abs ≤ g ↔ -g ≤ x ∧ x ≤ g := by
  simp only [Rat.abs]; split <;> constructor <;> intro h <;> grind

section err
variable (f : Format) (hf : f.WF)
include hf

/-- **A correctly rounded rational is within one unit in the last place of its binade.** -/
theorem cr_ofRat_error {rm : RoundingMode} {v r : Rat} (hv : v ≠ 0) (a : Int) (ha : f.ulpMin ≤ a)
    (hlo : (2 : Rat) ^ a ≤ v.abs) (hhi : v.abs < (2 : Rat) ^ (a + 1))
    (hcr : CorrectlyRounded f.Unbounded f.UnboundedEven rm (Cut.ofRat v) r) :
    (r - v).abs ≤ (2 : Rat) ^ (max f.ulpMin (a - f.fracBits)) := by
  have hg := rat_two_zpow_pos (max f.ulpMin (a - f.fracBits))
  -- the positive case
  have pos : ∀ (rm : RoundingMode) (v r : Rat), 0 < v → (2 : Rat) ^ a ≤ v → v < (2 : Rat) ^ (a + 1) →
      CorrectlyRounded f.Unbounded f.UnboundedEven rm (Cut.ofRat v) r →
      (r - v).abs ≤ (2 : Rat) ^ (max f.ulpMin (a - f.fracBits)) := by
    intro rm v r _ h1 h2 hcr
    obtain ⟨-, -, -, hN, hD, hU⟩ := binade_bounds f hf (Cut.ofRat_valid v) a ha h1 (Rat.not_le.mpr h2) hcr
    rw [rat_abs_le_iff]
    simp only [Cut.ofRat] at hN hD hU
    cases rm
    · have := hN rfl; constructor <;> grind
    · have := hD rfl; constructor <;> grind
    · have := hU rfl; constructor <;> grind
    · have := hD rfl; constructor <;> grind
  rcases rat_lt_or_le 0 v with hp | hn
  · have : v.abs = v := Rat.abs_of_nonneg (Rat.le_of_lt hp)
    rw [this] at hlo hhi
    exact pos rm v r hp hlo hhi hcr
  · have hneg : v < 0 := by grind
    have : v.abs = -v := by simp only [Rat.abs]; split <;> grind
    rw [this] at hlo hhi
    have h2 := correctlyRounded_neg f.unbounded_neg f.unboundedEven_neg hcr
    rw [Cut.neg_ofRat] at h2
    have := pos rm.flip (-v) (-r) (by grind) hlo hhi h2
    rw [show -r - -v = -(r - v) by grind] at this
    simp only [Rat.abs] at this ⊢; split <;> split at this <;> grind

/-- Finite values are at most the largest finite number in magnitude. -/
theorem value_abs_le_max {n : Nat} {y : Rat} (h : f.value n = some y) : y.abs ≤ f.maxValue := by
  obtain ⟨hn, he⟩ := value_some_lt f h
  have ht := value_toExact f h
  rw [Exact.toRat_signed] at ht
  rw [← ht, abs_signed _ (Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (rat_two_zpow_pos _)))]
  simp only [Format.maxValue, Format.emax_sub, Format.prec]
  rw [nat_zpow_le_iff]
  have hE : f.expField n < 2 ^ f.expBits := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hxM := f.expMax_eq hf
  have hb := f.bias_pos hf
  have hF : f.fracField n < 2 ^ f.fracBits := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h2p : 2 ^ (f.fracBits + 1) = 2 * 2 ^ f.fracBits := Nat.pow_succ'
  simp only [Format.toExact]
  split
  · rename_i h0
    rw [show min f.qMin f.qMax = f.qMin by simp only [Format.qMin, Format.qMax]; omega,
      show (f.qMin - f.qMin).toNat = 0 by omega]
    have : 1 ≤ 2 ^ (f.qMax - f.qMin).toNat := Nat.one_le_two_pow
    have : (2 ^ (f.fracBits + 1) - 1) * 1 ≤ (2 ^ (f.fracBits + 1) - 1) * 2 ^ (f.qMax - f.qMin).toNat :=
      Nat.mul_le_mul_left _ this
    simp only [Nat.pow_zero, Nat.mul_one] at *; omega
  · rename_i h0
    have hexp : (f.expField n : Int) - f.bias - f.fracBits ≤ f.qMax := by
      simp only [Format.qMax]; simp only [Format.expMax] at he hxM; omega
    rw [show min ((f.expField n : Int) - f.bias - f.fracBits) f.qMax =
        (f.expField n : Int) - f.bias - f.fracBits by omega,
      show ((f.expField n : Int) - f.bias - f.fracBits - ((f.expField n : Int) - f.bias - f.fracBits)).toNat = 0 by omega]
    have : 1 ≤ 2 ^ (f.qMax - ((f.expField n : Int) - f.bias - f.fracBits)).toNat := Nat.one_le_two_pow
    have : (2 ^ (f.fracBits + 1) - 1) * 1 ≤
        (2 ^ (f.fracBits + 1) - 1) * 2 ^ (f.qMax - ((f.expField n : Int) - f.bias - f.fracBits)).toNat :=
      Nat.mul_le_mul_left _ this
    simp only [Nat.pow_zero, Nat.mul_one] at *; omega

end err

end Mips.Fp
