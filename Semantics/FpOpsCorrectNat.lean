import Semantics.FpOps

/-!
# FpOpsCorrectNat — integer facts about the rounding core's helpers

`bitLen`, `roundShift` (integer rounding of `N / 2^k` in each direction) and `isqrt`. Used by
`FpOpsCorrectCore.lean` and `FpOpsCorrectOps.lean`.
-/

namespace Mips.Fp

/-! ## `bitLen` -/

theorem bitLenAux_zero (fuel : Nat) : bitLenAux fuel 0 = 0 := by
  cases fuel <;> simp [bitLenAux]

theorem bitLenAux_spec : ∀ fuel n, n ≤ fuel →
    n < 2 ^ bitLenAux fuel n ∧ (0 < n → 2 ^ (bitLenAux fuel n - 1) ≤ n)
  | 0, n, h => by
    have : n = 0 := by omega
    subst this; simp [bitLenAux]
  | fuel + 1, n, h => by
    by_cases hn : n = 0
    · subst hn; simp [bitLenAux]
    · have ih := bitLenAux_spec fuel (n / 2) (by omega)
      simp only [bitLenAux, hn, ite_false, Nat.add_sub_cancel]
      refine ⟨?_, fun _ => ?_⟩
      · rw [Nat.pow_succ]; omega
      · by_cases h2 : n / 2 = 0
        · rw [h2, bitLenAux_zero]; simp; omega
        · have := ih.2 (by omega)
          have hb : 1 ≤ bitLenAux fuel (n / 2) := by
            rcases Nat.eq_zero_or_pos (bitLenAux fuel (n / 2)) with h0 | h0
            · rw [h0] at ih; simp at ih; omega
            · exact h0
          have : 2 ^ bitLenAux fuel (n / 2) = 2 * 2 ^ (bitLenAux fuel (n / 2) - 1) := by
            rw [← Nat.pow_succ']; congr 1; omega
          omega

theorem lt_two_pow_bitLen (n : Nat) : n < 2 ^ bitLen n :=
  (bitLenAux_spec n n (Nat.le_refl _)).1

theorem two_pow_bitLen_le (n : Nat) (h : 0 < n) : 2 ^ (bitLen n - 1) ≤ n :=
  (bitLenAux_spec n n (Nat.le_refl _)).2 h

theorem bitLen_pos (n : Nat) (h : 0 < n) : 1 ≤ bitLen n := by
  rcases Nat.eq_zero_or_pos (bitLen n) with h0 | h0
  · have := lt_two_pow_bitLen n; rw [h0] at this; simp at this; omega
  · exact h0

/-- `bitLen n` is the `b` with `2^(b-1) ≤ n < 2^b`. -/
theorem bitLen_eq_of (n b : Nat) (h1 : 2 ^ b ≤ 2 * n) (h2 : n < 2 ^ b) : bitLen n = b := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; have := Nat.two_pow_pos b; omega
    · exact h
  have a1 := lt_two_pow_bitLen n
  have a2 := two_pow_bitLen_le n hn
  have a3 := bitLen_pos n hn
  rcases Nat.lt_trichotomy (bitLen n) b with h | h | h
  · have : 2 ^ bitLen n ≤ 2 ^ (b - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have e : 2 ^ b = 2 * 2 ^ (b - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    omega
  · exact h
  · have : 2 ^ b ≤ 2 ^ (bitLen n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-! ## `roundShift`: integer rounding of `N / 2^k` -/

/-- The direction in which `roundShift rm neg` rounds the magnitude. -/
inductive Dir where
  | down
  | up
  | nearest
  deriving DecidableEq

/-- The magnitude direction of a rounding mode for a value of sign `neg`. -/
def dirOf : RoundingMode → Bool → Dir
  | .RN, _ => .nearest
  | .RZ, _ => .down
  | .RP, false => .up
  | .RP, true => .down
  | .RM, false => .down
  | .RM, true => .up

/-- `j` is `N / P` rounded in direction `d` (`P > 0`): down = floor, up = ceiling, nearest =
nearest with ties to even. -/
def IntRound (d : Dir) (N P j : Nat) : Prop :=
  match d with
  | .down => j * P ≤ N ∧ N < j * P + P
  | .up => N ≤ j * P ∧ j * P < N + P
  | .nearest => 2 * (j * P) ≤ 2 * N + P ∧ 2 * N ≤ 2 * (j * P) + P ∧
      ((2 * (j * P) = 2 * N + P ∨ 2 * N = 2 * (j * P) + P) → j % 2 = 0)

theorem roundShift_spec (rm : RoundingMode) (neg : Bool) (N k : Nat) :
    IntRound (dirOf rm neg) N (2 ^ k) (roundShift rm neg N k) := by
  have hP : 0 < 2 ^ k := Nat.two_pow_pos k
  have hd := Nat.div_add_mod N (2 ^ k)
  have hm := Nat.mod_lt N hP
  unfold roundShift
  cases rm <;> cases neg <;> simp only [dirOf, IntRound] <;>
  generalize 2 ^ k = P at * <;>
  generalize N / P = q at * <;>
  generalize N % P = r at * <;>
  have e1 : (q + 1) * P = q * P + P := Nat.succ_mul q P <;>
  have e2 : P * q = q * P := Nat.mul_comm P q <;>
  subst hd <;> split <;> rename_i h <;> simp at h <;> omega

theorem IntRound.le_of_lt {d : Dir} {N P j A : Nat} (hP : 0 < P) (h : IntRound d N P j)
    (hA : N < A * P) : j ≤ A := by
  have key : j * P < A * P + P := by
    cases d <;> simp only [IntRound] at h <;> omega
  have : j * P < (A + 1) * P := by rw [Nat.succ_mul]; exact key
  have := Nat.lt_of_mul_lt_mul_right this
  omega

theorem IntRound.ge_of_le {d : Dir} {N P j A : Nat} (hP : 0 < P) (h : IntRound d N P j)
    (hA : A * P ≤ N) : A ≤ j := by
  have key : A * P < j * P + P := by
    cases d <;> simp only [IntRound] at h <;> omega
  have : A * P < (j + 1) * P := by rw [Nat.succ_mul]; exact key
  have := Nat.lt_of_mul_lt_mul_right this
  omega

theorem IntRound.exact {d : Dir} {N P j : Nat} (hP : 0 < P) (h : IntRound d N P j) :
    j * P = N ↔ N % P = 0 := by
  constructor
  · intro e; rw [← e]; exact Nat.mul_mod_left j P
  · intro e
    have hN : N = (N / P) * P := by
      have := Nat.div_add_mod N P; rw [e, Nat.add_zero, Nat.mul_comm] at this; exact this.symm
    have h1 := h.le_of_lt (A := N / P + 1) hP (by rw [Nat.succ_mul]; omega)
    have h2 := h.ge_of_le (A := N / P) hP (by omega)
    rcases Nat.lt_or_ge j (N / P + 1) with h3 | h3
    · have : j = N / P := by omega
      rw [this]; exact hN.symm
    · have hj : j = N / P + 1 := by omega
      subst hj
      have : (N / P + 1) * P = N / P * P + P := Nat.succ_mul _ _
      cases d <;> simp only [IntRound] at h <;> omega

/-! ## `isqrt` -/

theorem isqrtAux_spec (n : Nat) : ∀ i r, r * r ≤ n → n < (r + 2 ^ i) * (r + 2 ^ i) →
    isqrtAux n i r * isqrtAux n i r ≤ n ∧ n < (isqrtAux n i r + 1) * (isqrtAux n i r + 1)
  | 0, r, h1, h2 => by simpa [isqrtAux] using And.intro h1 h2
  | i + 1, r, h1, h2 => by
    simp only [isqrtAux]
    have e : r + 2 ^ (i + 1) = (r + 2 ^ i) + 2 ^ i := by rw [Nat.pow_succ]; omega
    split
    · exact isqrtAux_spec n i _ (by assumption) (by rw [← e]; exact h2)
    · exact isqrtAux_spec n i r h1 (by omega)

theorem isqrt_spec (n : Nat) : isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) := by
  apply isqrtAux_spec n _ 0 (by simp)
  simp only [Nat.zero_add]
  rw [← Nat.pow_add]
  calc n < 2 ^ bitLen n := lt_two_pow_bitLen n
    _ ≤ 2 ^ ((bitLen n + 1) / 2 + (bitLen n + 1) / 2) := Nat.pow_le_pow_right (by omega) (by omega)

end Mips.Fp
