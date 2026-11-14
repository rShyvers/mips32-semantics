import Semantics.FpOpsCorrectShape

/-!
# FpOpsCorrectScale — from the core's integers to the cut

The rounding core rounds the integer `N = sig · 2^(exp - q)` (shifted right by `k = q - exp`
bits) to the integer `j`. This file connects that integer rounding with the comparisons of the
exact value against the half grid of unit `2^(q-1)` (`cutRound_ofRat`), moves them to any cut
that agrees with the exact value on that grid (`CutAgree`), and bounds `N`.
-/

namespace Mips.Fp

/-- `c` agrees with the rational `v` at every point `a · 2^e` with `e ≥ e0`. -/
def CutAgree (c : Cut) (v : Rat) (e0 : Int) : Prop :=
  ∀ a e : Int, e0 ≤ e →
    (c.le ((a : Rat) * (2 : Rat) ^ e) ↔ (a : Rat) * (2 : Rat) ^ e ≤ v) ∧
    (c.ge ((a : Rat) * (2 : Rat) ^ e) ↔ v ≤ (a : Rat) * (2 : Rat) ^ e)

theorem CutAgree.ofRat (v : Rat) (e0 : Int) : CutAgree (Cut.ofRat v) v e0 :=
  fun _ _ _ => ⟨Iff.rfl, Iff.rfl⟩

theorem CutAgree.mono {c : Cut} {v : Rat} {e0 e1 : Int} (h : CutAgree c v e0) (he : e0 ≤ e1) :
    CutAgree c v e1 := fun a e he' => h a e (by omega)

theorem CutAgree.neg {c : Cut} {v : Rat} {e0 : Int} (h : CutAgree c v e0) : CutAgree c.neg (-v) e0 :=
  fun a e he => by
    have h1 := h (-a) e he
    simp only [Cut.neg]
    have e1 : -((a : Rat) * (2 : Rat) ^ e) = ((-a : Int) : Rat) * (2 : Rat) ^ e := by push_cast; grind
    rw [e1, h1.1, h1.2]
    constructor <;> constructor <;> intro hh <;> push_cast at * <;> grind

/-- `CutAgree` lets a `CutRound` statement move between the cut and the rational. -/
theorem cutRound_agree {c : Cut} {v : Rat} {e0 q : Int} (h : CutAgree c v e0) (hq : e0 ≤ q - 1)
    (d : Dir) (j : Int) : CutRound c ((2 : Rat) ^ (q - 1)) d j ↔ CutRound (Cut.ofRat v) ((2 : Rat) ^ (q - 1)) d j := by
  have hle := fun a => (h a (q - 1) hq).1
  have hge := fun a => (h a (q - 1) hq).2
  cases d <;> simp only [CutRound, hle, hge, Cut.ofRat]

/-! ## Half-grid comparisons of `M` with `M · 2^k = N · 2^q` -/

section scaled
variable {M : Rat} {N k : Nat} {q : Int}

theorem rat_pow_pos (k : Nat) : (0 : Rat) < (2 : Rat) ^ k := Rat.pow_pos (by decide)

theorem half_le_iff (hM : M * (2 : Rat) ^ k = (N : Rat) * (2 : Rat) ^ q) (a : Int) :
    (a : Rat) * (2 : Rat) ^ (q - 1) ≤ M ↔ a * 2 ^ k ≤ 2 * (N : Int) := by
  have hK := rat_pow_pos k
  have hq := two_zpow_pred q
  have hH := rat_two_zpow_pos (q - 1)
  rw [← rat_mul_le_iff hK, Rat.mul_assoc, Rat.mul_comm ((2 : Rat) ^ (q - 1)), ← Rat.mul_assoc, hM, hq,
    show (N : Rat) * (2 * (2 : Rat) ^ (q - 1)) = (2 * (N : Rat)) * (2 : Rat) ^ (q - 1) by grind,
    rat_mul_le_iff hH]
  rw [show (a : Rat) * (2 : Rat) ^ k = ((a * 2 ^ k : Int) : Rat) by push_cast; rfl,
    show (2 * (N : Rat)) = ((2 * (N : Int) : Int) : Rat) by push_cast; rfl]
  exact Rat.intCast_le_intCast

theorem half_ge_iff (hM : M * (2 : Rat) ^ k = (N : Rat) * (2 : Rat) ^ q) (a : Int) :
    M ≤ (a : Rat) * (2 : Rat) ^ (q - 1) ↔ 2 * (N : Int) ≤ a * 2 ^ k := by
  have hK := rat_pow_pos k
  have hq := two_zpow_pred q
  have hH := rat_two_zpow_pos (q - 1)
  rw [← rat_mul_le_iff hK, hM, Rat.mul_assoc, Rat.mul_comm ((2 : Rat) ^ (q - 1)), ← Rat.mul_assoc, hq,
    show (N : Rat) * (2 * (2 : Rat) ^ (q - 1)) = (2 * (N : Rat)) * (2 : Rat) ^ (q - 1) by grind,
    rat_mul_le_iff hH]
  rw [show (a : Rat) * (2 : Rat) ^ k = ((a * 2 ^ k : Int) : Rat) by push_cast; rfl,
    show (2 * (N : Rat)) = ((2 * (N : Int) : Int) : Rat) by push_cast; rfl]
  exact Rat.intCast_le_intCast

/-- **The integer rounding is the cut rounding.** -/
theorem cutRound_ofRat (hM : M * (2 : Rat) ^ k = (N : Rat) * (2 : Rat) ^ q) {d : Dir} {j : Nat}
    (hj : IntRound d N (2 ^ k) j) : CutRound (Cut.ofRat M) ((2 : Rat) ^ (q - 1)) d (j : Int) := by
  have hP : (0 : Int) < 2 ^ k := by have := Nat.two_pow_pos k; have := int_two_pow k; omega
  have e := int_two_pow k
  have mj : ((j * 2 ^ k : Nat) : Int) = (j : Int) * 2 ^ k := by rw [Int.natCast_mul, int_two_pow]
  cases d <;> simp only [CutRound, Cut.ofRat, half_le_iff hM, half_ge_iff hM] <;>
    simp only [IntRound] at hj
  · -- down
    have e2 : ((2 * (j : Int) + 2 : Int)) * 2 ^ k = 2 * ((j : Int) * 2 ^ k) + 2 * 2 ^ k := by
      rw [Int.add_mul, Int.mul_assoc]
    refine ⟨by rw [Int.mul_assoc]; omega, ?_⟩
    rw [Int.not_le, e2]; omega
  · -- up
    have e2 : ((2 * (j : Int) - 2 : Int)) * 2 ^ k = 2 * ((j : Int) * 2 ^ k) - 2 * 2 ^ k := by
      rw [Int.sub_mul, Int.mul_assoc]
    refine ⟨by rw [Int.mul_assoc]; omega, ?_⟩
    rw [Int.not_le, e2]; omega
  · -- nearest
    have e1 : ((2 * (j : Int) - 1 : Int)) * 2 ^ k = 2 * ((j : Int) * 2 ^ k) - 2 ^ k := by
      rw [Int.sub_mul, Int.mul_assoc, Int.one_mul]
    have e2 : ((2 * (j : Int) + 1 : Int)) * 2 ^ k = 2 * ((j : Int) * 2 ^ k) + 2 ^ k := by
      rw [Int.add_mul, Int.mul_assoc, Int.one_mul]
    obtain ⟨h1, h2, h3⟩ := hj
    refine ⟨by rw [e1]; omega, by rw [e2]; omega, fun hh => ?_, fun hh => ?_⟩
    · rw [e1] at hh
      have := h3 (Or.inl (by omega)); omega
    · rw [e2] at hh
      have := h3 (Or.inr (by omega)); omega

end scaled

/-! ## The scaled significand -/

theorem roundShift_zero (rm : RoundingMode) (s : Bool) (n : Nat) : roundShift rm s n 0 = n := by
  cases rm <;> cases s <;> simp [roundShift, Nat.mod_one]

/-- The core's scaling at an exponent `q` at least `q0 = exp + bitLen sig - p`. -/
theorem scaled_facts (sig : Nat) (hs : 0 < sig) (exp q : Int) (p : Nat) (hp : 1 ≤ p)
    (hq : exp + bitLen sig - p ≤ q) :
    let k := (q - exp).toNat
    let N := sig * 2 ^ (exp - q).toNat
    (sig : Rat) * (2 : Rat) ^ exp * (2 : Rat) ^ k = (N : Rat) * (2 : Rat) ^ q ∧
    N < 2 ^ p * 2 ^ k ∧
    (q = exp + bitLen sig - p → 2 ^ (p - 1) * 2 ^ k ≤ N) ∧
    (N = sig ∨ k = 0) := by
  intro k N
  have hb1 := lt_two_pow_bitLen sig
  have hb2 := two_pow_bitLen_le sig hs
  have hb3 := bitLen_pos sig hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [N, k]
    rw [Rat.natCast_mul, two_pow_nat, ← two_zpow_nat, ← two_zpow_nat]
    rw [Rat.mul_assoc, ← two_zpow_add, Rat.mul_assoc, ← two_zpow_add]
    congr 2; omega
  · rcases Int.le_total exp q with h | h
    · have : (exp - q).toNat = 0 := by omega
      simp only [N, k, this, Nat.pow_zero, Nat.mul_one]
      calc sig < 2 ^ bitLen sig := hb1
        _ ≤ 2 ^ (p + (q - exp).toNat) := Nat.pow_le_pow_right (by omega) (by omega)
        _ = 2 ^ p * 2 ^ (q - exp).toNat := Nat.pow_add _ _ _
    · have : (q - exp).toNat = 0 := by omega
      simp only [N, k, this, Nat.pow_zero, Nat.mul_one]
      calc sig * 2 ^ (exp - q).toNat < 2 ^ bitLen sig * 2 ^ (exp - q).toNat :=
            Nat.mul_lt_mul_of_pos_right hb1 (Nat.two_pow_pos _)
        _ = 2 ^ (bitLen sig + (exp - q).toNat) := (Nat.pow_add _ _ _).symm
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
  · intro hq0
    rcases Int.le_total exp q with h | h
    · have : (exp - q).toNat = 0 := by omega
      simp only [N, k, this, Nat.pow_zero, Nat.mul_one]
      rw [← Nat.pow_add]
      calc 2 ^ (p - 1 + (q - exp).toNat) = 2 ^ (bitLen sig - 1) := by congr 1; omega
        _ ≤ sig := hb2
    · have : (q - exp).toNat = 0 := by omega
      simp only [N, k, this, Nat.pow_zero, Nat.mul_one]
      calc 2 ^ (p - 1) = 2 ^ (bitLen sig - 1) * 2 ^ (exp - q).toNat := by
            rw [← Nat.pow_add]; congr 1; omega
        _ ≤ sig * 2 ^ (exp - q).toNat := Nat.mul_le_mul_right _ hb2
  · rcases Int.le_total exp q with h | h
    · left; simp [N, show (exp - q).toNat = 0 by omega]
    · right; simp only [k]; omega

end Mips.Fp
