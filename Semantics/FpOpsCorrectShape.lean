import Semantics.FpOpsCorrectValue

/-!
# FpOpsCorrectShape — the representable sets have the grid shape

`Grid p P` (precision `p`, exponents allowed by `P`) at an exponent `q` with `P q`: the multiples of
`2^q` up to `2^p · 2^q` are in it, and every other element is below `2^(p-1) · 2^q`, or there is no
other element when `q` is the least allowed exponent (`gridHyp_of`).
-/

namespace Mips.Fp

theorem int_two_pow (p : Nat) : ((2 ^ p : Nat) : Int) = (2 : Int) ^ p := by norm_cast

theorem rat_int_two_pow (p : Nat) : (((2 : Int) ^ p : Int) : Rat) = (2 : Rat) ^ p := by
  rw [Rat.intCast_pow]; rfl

theorem two_zpow_pred (q : Int) : (2 : Rat) ^ q = 2 * (2 : Rat) ^ (q - 1) := by
  rw [show q = (q - 1) + 1 by omega, Rat.zpow_add_one (by decide)]
  rw [show q - 1 + 1 - 1 = q - 1 by omega]; grind

/-- `i · 2^q` on the half grid of unit `2^(q-1)`. -/
theorem half_grid (i q : Int) :
    (i : Rat) * (2 : Rat) ^ q = ((2 * i : Int) : Rat) * (2 : Rat) ^ (q - 1) := by
  rw [two_zpow_pred q]; push_cast; grind

theorem grid_neg_iff (p : Nat) (P : Int → Prop) (y : Rat) : Grid p P (-y) ↔ Grid p P y := by
  constructor
  · rintro ⟨m, e, hm, hP, hy⟩
    exact ⟨-m, e, by simpa using hm, hP, by push_cast; grind⟩
  · rintro ⟨m, e, hm, hP, hy⟩
    exact ⟨-m, e, by simpa using hm, hP, by push_cast; grind⟩

/-- An element below the exponent `q` is below `2^(p-1) · 2^q` in absolute value. -/
theorem grid_small {p : Nat} {m e q : Int} (hm : m.natAbs < 2 ^ p) (he : e < q) :
    (m : Rat) * (2 : Rat) ^ e < ((2 * 2 ^ (p - 1) : Int) : Rat) * (2 : Rat) ^ (q - 1) ∨ p = 0 := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · exact .inr hp
  left
  have hp2 : (2 : Int) * 2 ^ (p - 1) = 2 ^ p := by
    rw [← Int.pow_succ']; congr 1; omega
  rw [hp2]
  have hmp : m < (2 : Int) ^ p := by have := int_two_pow p; omega
  have h1 : (m : Rat) < (((2 : Int) ^ p : Int) : Rat) := Rat.intCast_lt_intCast.2 hmp
  have h2 := two_zpow_le (show e ≤ q - 1 by omega)
  have h3 := rat_two_zpow_pos e
  have h4 : (0 : Rat) ≤ (((2 : Int) ^ p : Int) : Rat) := by
    rw [rat_int_two_pow]; exact Rat.pow_nonneg (by decide)
  have := Rat.mul_lt_mul_of_pos_right h1 h3
  have := Rat.mul_le_mul_of_nonneg_left h2 h4
  grind

/-- **The grid shape of `Grid p P` at exponent `q`.** `i0` is `2^(p-1)` (then `L = 2^(p-1) · 2^q`),
or `0` when no allowed exponent is below `q`. `P'` is the exponent condition of the even values:
`P' e ↔ P (e - 1)`. -/
theorem gridHyp_of {p : Nat} (hp : 2 ≤ p) {P P' : Int → Prop} (hPup : ∀ e, P e → P (e + 1))
    (hP' : ∀ e, P' e ↔ P (e - 1)) {q : Int} (hq : P q) (i0 : Int)
    (hi0 : i0 = 2 ^ (p - 1) ∨ (i0 = 0 ∧ ∀ e, P e → q ≤ e)) :
    GridHyp (Grid p P) (Grid (p - 1) P') p ((2 : Rat) ^ (q - 1))
      (((2 * i0 : Int) : Rat) * (2 : Rat) ^ (q - 1)) where
  h_pos := rat_two_zpow_pos _
  p_pos := by omega
  L_grid := ⟨i0, by
      rcases hi0 with h | h
      · rw [h]; exact Int.pow_nonneg (by omega)
      · omega, by
      have : 2 ^ (p - 1) ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
      have := int_two_pow p
      have := int_two_pow (p - 1)
      have := Int.pow_nonneg (m := p) (show (0 : Int) ≤ 2 by decide)
      rcases hi0 with h | h
      · omega
      · omega, rfl⟩
  S_grid := fun j hj0 hjp => by
    rw [← half_grid]
    rcases Int.lt_or_le j (2 ^ p) with hlt | hge
    · exact ⟨j, q, by have := int_two_pow p; omega, hq, rfl⟩
    · have hj : j = 2 ^ p := by omega
      refine ⟨2 ^ (p - 1), q + 1, ?_, hPup q hq, ?_⟩
      · have := int_two_pow (p - 1)
        have : 2 ^ (p - 1) < 2 ^ p := Nat.pow_lt_pow_right (by omega) (by omega)
        have : ((2 : Int) ^ (p - 1)).natAbs = 2 ^ (p - 1) := by
          rw [← int_two_pow]; rfl
        omega
      · rw [hj, Rat.zpow_add_one (by decide), rat_int_two_pow, rat_int_two_pow]
        rw [show p = (p - 1) + 1 by omega, Rat.pow_succ]
        rw [show p - 1 + 1 - 1 = p - 1 by omega]; grind
  S_off := fun y ⟨m, e, hm, hPe, hy⟩ => by
    subst hy
    rcases Int.lt_or_le e q with hlt | hge
    · right
      rcases hi0 with h | h
      · rw [h]; exact (grid_small hm hlt).resolve_right (by omega)
      · exact absurd (h.2 e hPe) (by omega)
    · left
      refine ⟨m * 2 ^ (e - q).toNat, ?_⟩
      rw [zpow_shift m hge, half_grid]
  E_grid := fun j hj0 hjp hj2 => by
    obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
    have e1 : (((2 * (2 * k)) : Int) : Rat) * (2 : Rat) ^ (q - 1) = (k : Rat) * (2 : Rat) ^ (q + 1) := by
      rw [half_grid k (q + 1), show q + 1 - 1 = q by omega, half_grid (2 * k) q]
    rw [e1]
    have hp1 : (2 : Int) ^ p = 2 * 2 ^ (p - 1) := by rw [← Int.pow_succ']; congr 1; omega
    rcases Int.lt_or_le k (2 ^ (p - 1)) with hlt | hge
    · exact ⟨k, q + 1, by have := int_two_pow (p - 1); omega,
        (hP' _).2 (by rw [show q + 1 - 1 = q by omega]; exact hq), rfl⟩
    · have hk : k = 2 ^ (p - 1) := by omega
      refine ⟨2 ^ (p - 2), q + 2, ?_, (hP' _).2 (by rw [show q + 2 - 1 = q + 1 by omega]; exact hPup q hq), ?_⟩
      · have := int_two_pow (p - 2)
        have : 2 ^ (p - 2) < 2 ^ (p - 1) := Nat.pow_lt_pow_right (by omega) (by omega)
        have : ((2 : Int) ^ (p - 2)).natAbs = 2 ^ (p - 2) := by rw [← int_two_pow]; rfl
        omega
      · have e2 : (2 : Rat) ^ (q + 2) = (2 : Rat) ^ q * 2 * 2 := by
          rw [show q + 2 = q + 1 + 1 by omega, Rat.zpow_add_one (by decide), Rat.zpow_add_one (by decide)]
        have e3 : (2 : Rat) ^ (q + 1) = (2 : Rat) ^ q * 2 := Rat.zpow_add_one (by decide) q
        rw [hk, e2, e3, rat_int_two_pow, rat_int_two_pow, show p - 1 = (p - 2) + 1 by omega, Rat.pow_succ]
        grind
  E_off := fun y ⟨m, e, hm, hPe, hy⟩ => by
    subst hy
    have hPe' := (hP' e).1 hPe
    rcases Int.lt_or_le e (q + 1) with hlt | hge
    · right
      rcases hi0 with h | h
      · rw [h]
        have := (grid_small (q := q + 1) hm hlt).resolve_right (by omega)
        rw [show q + 1 - 1 = q by omega] at this
        rw [show ((2 * 2 ^ (p - 1) : Int) : Rat) * (2 : Rat) ^ (q - 1) =
            ((2 * 2 ^ (p - 1 - 1) : Int) : Rat) * (2 : Rat) ^ q by
          rw [half_grid (2 * 2 ^ (p - 1 - 1)) q]
          congr 2
          have : (2 : Int) ^ (p - 1) = 2 * 2 ^ (p - 1 - 1) := by
            rw [← Int.pow_succ']; congr 1; omega
          omega]
        exact this
      · exact absurd (h.2 _ hPe') (by omega)
    · left
      refine ⟨m * 2 ^ (e - (q + 1)).toNat, ?_⟩
      rw [zpow_shift m hge, half_grid, show q + 1 - 1 = q by omega, half_grid]
      congr 2; push_cast; grind

end Mips.Fp
