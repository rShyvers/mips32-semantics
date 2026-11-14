import Semantics.FpOpsCorrectGrid

/-!
# FpOpsCorrectValue — encodings, their values, and the shape of the representable sets

* `value_eq_toExact`: `Format.value` (the manual's Table 6.2) agrees with the core's `toExact` on
  every finite encoding.
* `value_pack`: the value of an encoding assembled by `Format.pack`.
* `representable_unbounded`: every finite value is in `Format.Unbounded`.
* `gridHyp_*`: the representable sets have the grid shape of `FpOpsCorrectGrid.lean` at every
  exponent.
-/

namespace Mips.Fp

/-! ## Powers of two -/

theorem two_zpow_add (a b : Int) : (2 : Rat) ^ (a + b) = (2 : Rat) ^ a * (2 : Rat) ^ b :=
  Rat.zpow_add (by decide) a b

theorem two_zpow_nat (n : Nat) : (2 : Rat) ^ (n : Int) = ((2 ^ n : Nat) : Rat) := by
  rw [Rat.zpow_natCast]; simp

theorem two_pow_nat (n : Nat) : (2 : Rat) ^ n = ((2 ^ n : Nat) : Rat) := by simp

theorem two_zpow_toNat (a b : Int) (h : a ≤ b) :
    (2 : Rat) ^ b = ((2 ^ (b - a).toNat : Nat) : Rat) * (2 : Rat) ^ a := by
  rw [← two_zpow_nat, ← two_zpow_add]; congr 1; omega

theorem one_le_two_pow_nat (n : Nat) : (1 : Rat) ≤ ((2 ^ n : Nat) : Rat) := by
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  exact_mod_cast this

theorem two_zpow_le {a b : Int} (h : a ≤ b) : (2 : Rat) ^ a ≤ (2 : Rat) ^ b := by
  rw [two_zpow_toNat a b h]
  have h1 := one_le_two_pow_nat (b - a).toNat
  have h2 := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (rat_two_zpow_pos a))
  grind

theorem two_zpow_lt {a b : Int} (h : a < b) : (2 : Rat) ^ a < (2 : Rat) ^ b := by
  have e : (2 : Rat) ^ b = (2 : Rat) ^ (b - 1) * 2 := by
    rw [← Rat.zpow_add_one (by decide)]; congr 1; omega
  have := two_zpow_le (show a ≤ b - 1 by omega)
  have := rat_two_zpow_pos (b - 1)
  grind

/-- A value with exponent `e ≥ q` is an integer multiple of `2^q`. -/
theorem zpow_shift (m : Int) {e q : Int} (h : q ≤ e) :
    (m : Rat) * (2 : Rat) ^ e = ((m * 2 ^ (e - q).toNat : Int) : Rat) * (2 : Rat) ^ q := by
  rw [two_zpow_toNat q e h]; push_cast; grind

/-! ## Encodings -/

/-- The formats the theorems are stated for: at least two exponent bits and two fraction bits
(binary32 and binary64). -/
def Format.WF (f : Format) : Prop := 2 ≤ f.expBits ∧ 2 ≤ f.fracBits

theorem binary32_wf : binary32.WF := ⟨by decide, by decide⟩
theorem binary64_wf : binary64.WF := ⟨by decide, by decide⟩

theorem Format.ulpMin_eq (f : Format) : f.ulpMin = f.qMin := by
  simp only [ulpMin, emin, qMin, bias]; try omega

theorem Format.emax_sub (f : Format) : f.emax - f.fracBits = f.qMax := by
  simp only [emax, qMax, bias]

theorem Format.bias_pos (f : Format) (hf : f.WF) : 1 ≤ f.bias := by
  simp only [bias]
  have : 2 ≤ 2 ^ (f.expBits - 1) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show 1 ≤ f.expBits - 1 by have := hf.1; omega)
    simpa using this
  omega

theorem Format.expMax_eq (f : Format) (hf : f.WF) : f.expMax = 2 * f.bias + 1 := by
  simp only [expMax, bias]
  have : 2 ^ f.expBits = 2 * 2 ^ (f.expBits - 1) := by
    rw [← Nat.pow_succ']; congr 1; have := hf.1; omega
  have : 1 ≤ 2 ^ (f.expBits - 1) := Nat.one_le_two_pow
  omega

/-- Fields of an assembled pattern. -/
theorem Format.pack_fields (f : Format) (s : Bool) (e fr : Nat) (he : e < 2 ^ f.expBits)
    (hfr : fr < 2 ^ f.fracBits) :
    f.pack s e fr / 2 ^ f.fracBits % 2 ^ f.expBits = e ∧ f.pack s e fr % 2 ^ f.fracBits = fr ∧
      f.pack s e fr / 2 ^ (f.expBits + f.fracBits) = (if s then 1 else 0) ∧
      f.pack s e fr < 2 ^ f.width := by
  have hF : 0 < 2 ^ f.fracBits := Nat.two_pow_pos _
  have hE : 0 < 2 ^ f.expBits := Nat.two_pow_pos _
  have hp : f.pack s e fr = ((if s then 1 else 0) * 2 ^ f.expBits + e) * 2 ^ f.fracBits + fr := by
    simp only [pack, Nat.pow_add]; split <;> simp [Nat.add_mul]
  have hd : f.pack s e fr / 2 ^ f.fracBits = (if s then 1 else 0) * 2 ^ f.expBits + e := by
    rw [hp, Nat.mul_comm, Nat.mul_add_div hF, Nat.div_eq_of_lt hfr, Nat.add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]
  · rw [hp, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hfr]
  · rw [Nat.pow_add, Nat.mul_comm, ← Nat.div_div_eq_div_mul, hd, Nat.add_comm,
      Nat.add_mul_div_right _ _ hE, Nat.div_eq_of_lt he, Nat.zero_add]
  · rw [hp]
    have h1 : (if s then 1 else 0) * 2 ^ f.expBits + e + 1 ≤ 2 * 2 ^ f.expBits := by
      split <;> omega
    have h2 : (((if s then 1 else 0) * 2 ^ f.expBits + e) + 1) * 2 ^ f.fracBits ≤
        2 * 2 ^ f.expBits * 2 ^ f.fracBits := Nat.mul_le_mul_right _ h1
    have h3 : 2 ^ f.width = 2 * 2 ^ f.expBits * 2 ^ f.fracBits := by
      simp only [width, Nat.pow_add, Nat.pow_one]
    rw [Nat.succ_mul] at h2
    omega

/-- **`value` agrees with the core's `toExact`** on every finite `width`-bit pattern. -/
theorem value_eq_toExact (f : Format) (n : Nat) (hn : n < 2 ^ f.width)
    (he : f.expField n ≠ f.expMax) : f.value n = some (f.toExact n).toRat := by
  have hF := rat_two_zpow_pos (f.fracBits : Int)
  rw [two_zpow_nat] at hF
  have hne : ((2 ^ f.fracBits : Nat) : Rat) ≠ 0 := by grind
  have hE : (n / 2 ^ f.fracBits) % 2 ^ f.expBits = f.expField n := rfl
  have hFr : n % 2 ^ f.fracBits = f.fracField n := rfl
  have hS : ((n / 2 ^ (f.expBits + f.fracBits)) % 2 = 1) = (f.signBit n = true) := by
    simp [Format.signBit]
  have hM : 2 ^ f.expBits - 1 = f.expMax := rfl
  simp only [Format.value, hn, ite_true, hE, hFr, hS, hM, he, ite_false]
  unfold Format.toExact Exact.toRat
  generalize f.signBit n = sb
  generalize hFF : f.fracField n = F
  by_cases h0 : f.expField n = 0
  · simp only [h0, ite_true]
    have e1 : (2 : Rat) ^ f.emin = (2 : Rat) ^ f.qMin * ((2 ^ f.fracBits : Nat) : Rat) := by
      rw [← two_zpow_nat, ← two_zpow_add]; congr 1; simp only [Format.emin, Format.qMin, Format.bias]; omega
    rw [e1, two_pow_nat]
    congr 1
    generalize ((2 ^ f.fracBits : Nat) : Rat) = B at *
    generalize (2 : Rat) ^ f.qMin = A
    rw [Rat.div_def]
    have := Rat.mul_inv_cancel B hne
    grind
  · simp only [h0, ite_false]
    generalize f.expField n = E at *
    have e1 : (2 : Rat) ^ ((E : Int) - f.emax) =
        (2 : Rat) ^ ((E : Int) - (f.bias : Int) - f.fracBits) * ((2 ^ f.fracBits : Nat) : Rat) := by
      rw [← two_zpow_nat, ← two_zpow_add]; congr 1; simp only [Format.emax, Format.bias]; omega
    rw [e1, two_pow_nat]
    congr 1
    rw [Rat.natCast_add]
    generalize ((2 ^ f.fracBits : Nat) : Rat) = B at *
    generalize (2 : Rat) ^ ((E : Int) - (f.bias : Int) - f.fracBits : Int) = A
    rw [Rat.div_def]
    have := Rat.mul_inv_cancel B hne
    grind

theorem value_none_of_expMax (f : Format) (n : Nat) (he : f.expField n = f.expMax) :
    f.value n = none := by
  simp only [Format.expField, Format.expMax] at he
  simp only [Format.value]; split <;> simp_all

theorem value_some_lt (f : Format) {n : Nat} {x : Rat} (h : f.value n = some x) :
    n < 2 ^ f.width ∧ f.expField n ≠ f.expMax := by
  simp only [Format.value] at h
  split at h
  · refine ⟨by assumption, fun he => ?_⟩
    simp only [Format.expField, Format.expMax] at he
    simp_all
  · simp at h

/-- The value of an encoding is the value of its `toExact`. -/
theorem value_toExact (f : Format) {n : Nat} {x : Rat} (h : f.value n = some x) :
    (f.toExact n).toRat = x := by
  obtain ⟨h1, h2⟩ := value_some_lt f h
  rw [value_eq_toExact f n h1 h2] at h
  exact Option.some.inj h

end Mips.Fp
