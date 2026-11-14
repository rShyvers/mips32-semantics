import Semantics.FpOpsCorrectMain

/-!
# FpOpsCorrectExact — the exact results of the arithmetic

* `Exact.add_toRat`, `Exact.mul_toRat`: `Exact.add` and `Exact.mul` compute the exact sum and product.
* `cutAgree_sticky`: a quotient or root computed to extra bits with a sticky last bit agrees with
  the true result on every grid the rounding uses ("rounds identically").
* `Exact.div_agree`, `Exact.sqrt_agree`: `Exact.div` / `Exact.sqrt` are such sticky results for the
  true quotient `x / y` and the true square root `√x`.
-/

namespace Mips.Fp

/-! ## Sum and product -/

theorem Exact.toRat_eq (v : Exact) :
    v.toRat = (((if v.sign then -(v.sig : Int) else (v.sig : Int)) : Int) : Rat) * (2 : Rat) ^ v.exp := by
  simp only [Exact.toRat]; cases v.sign <;> simp <;> push_cast <;> grind

theorem Exact.add_toRat (rm : RoundingMode) (a b : Exact) :
    (Exact.add rm a b).toRat = a.toRat + b.toRat := by
  simp only [Exact.add]
  generalize he : (if a.exp ≤ b.exp then a.exp else b.exp) = e
  have hea : e ≤ a.exp := by subst he; split <;> omega
  have heb : e ≤ b.exp := by subst he; split <;> omega
  have ha : a.toRat = (((if a.sign then -((a.sig * 2 ^ (a.exp - e).toNat : Nat) : Int)
      else ((a.sig * 2 ^ (a.exp - e).toNat : Nat) : Int)) : Int) : Rat) * (2 : Rat) ^ e := by
    rw [Exact.toRat_eq, zpow_shift _ hea]; congr 2; cases a.sign <;> simp [Int.neg_mul]
  have hb : b.toRat = (((if b.sign then -((b.sig * 2 ^ (b.exp - e).toNat : Nat) : Int)
      else ((b.sig * 2 ^ (b.exp - e).toNat : Nat) : Int)) : Int) : Rat) * (2 : Rat) ^ e := by
    rw [Exact.toRat_eq, zpow_shift _ heb]; congr 2; cases b.sign <;> simp [Int.neg_mul]
  rw [ha, hb]
  generalize (if a.sign then -((a.sig * 2 ^ (a.exp - e).toNat : Nat) : Int)
      else ((a.sig * 2 ^ (a.exp - e).toNat : Nat) : Int)) = A
  generalize (if b.sign then -((b.sig * 2 ^ (b.exp - e).toNat : Nat) : Int)
      else ((b.sig * 2 ^ (b.exp - e).toNat : Nat) : Int)) = B
  split
  · rename_i h
    have : ((A + B : Int) : Rat) = 0 := by rw [h]; rfl
    push_cast at this
    simp only [Exact.toRat]
    have e2 : (A : Rat) * (2 : Rat) ^ e + (B : Rat) * (2 : Rat) ^ e = ((A : Rat) + B) * (2 : Rat) ^ e := by grind
    rw [e2, this]; simp
  · rename_i h
    rw [Exact.toRat_eq]
    simp only
    have : (if decide (A + B < 0) = true then -((A + B).natAbs : Int) else ((A + B).natAbs : Int)) = A + B := by
      by_cases hn : A + B < 0 <;> simp [hn] <;> omega
    rw [this]; push_cast; grind

theorem Exact.mul_toRat (a b : Exact) : (Exact.mul a b).toRat = a.toRat * b.toRat := by
  obtain ⟨sa, ma, ea⟩ := a
  obtain ⟨sb, mb, eb⟩ := b
  simp only [Exact.mul, Exact.toRat, two_zpow_add, Rat.natCast_mul]
  cases sa <;> cases sb <;> simp <;> grind

theorem Exact.toRat_mk (s : Bool) (m : Nat) (E : Int) :
    Exact.toRat ⟨s, m, E⟩ = (if s then -(((m : Int) : Rat) * (2 : Rat) ^ E) else ((m : Int) : Rat) * (2 : Rat) ^ E) := by
  simp only [Exact.toRat, Rat.intCast_natCast]; cases s <;> simp <;> grind

/-! ## Sticky results -/

/-- **The sticky-bit argument.** If, on the grid of unit `2^(E+1)`, the positive cut `c'` lies
between `Q` and `Q + 1` (strictly when `t`, at `Q` when not `t`), then `c` agrees with the exact
value `(2Q + t) · 2^E` (signed by `s`) at every point `a · 2^e` with `e ≥ E + 1`. -/
theorem cutAgree_sticky (c : Cut) (s : Bool) (Q : Nat) (t : Bool) (E : Int)
    (hle : ∀ a : Int, (if s then c.neg else c).le ((a : Rat) * (2 : Rat) ^ (E + 1)) ↔ a ≤ Q)
    (hge : ∀ a : Int, (if s then c.neg else c).ge ((a : Rat) * (2 : Rat) ^ (E + 1)) ↔
      (if t then (Q : Int) + 1 ≤ a else (Q : Int) ≤ a)) :
    CutAgree c (Exact.toRat ⟨s, 2 * Q + (if t then 1 else 0), E⟩) (E + 1) := by
  intro a e he
  rw [zpow_shift a he]
  generalize a * 2 ^ (e - (E + 1)).toNat = a'
  have hw := Exact.toRat_mk s (2 * Q + (if t then 1 else 0)) E
  have hE : (2 : Rat) ^ (E + 1) = 2 * (2 : Rat) ^ E := by
    rw [Rat.zpow_add_one (by decide)]; grind
  have hP := rat_two_zpow_pos E
  -- compare `a' · 2^(E+1)` with `(2Q + t) · 2^E` as integers
  have key : ∀ (x y : Int), (x : Rat) * (2 : Rat) ^ (E + 1) ≤ (y : Rat) * (2 : Rat) ^ E ↔ 2 * x ≤ y := by
    intro x y
    rw [hE, show (x : Rat) * (2 * (2 : Rat) ^ E) = ((2 * x : Int) : Rat) * (2 : Rat) ^ E by push_cast; grind]
    exact pt_le hP
  have key' : ∀ (x y : Int), (y : Rat) * (2 : Rat) ^ E ≤ (x : Rat) * (2 : Rat) ^ (E + 1) ↔ y ≤ 2 * x := by
    intro x y
    rw [hE, show (x : Rat) * (2 * (2 : Rat) ^ E) = ((2 * x : Int) : Rat) * (2 : Rat) ^ E by push_cast; grind]
    exact pt_le hP
  cases s
  · simp only [ite_false, Bool.false_eq_true] at hle hge hw ⊢
    rw [hw, hle, hge, key, key']
    cases t <;> simp <;> omega
  · simp only [ite_true] at hle hge hw ⊢
    have h1 := hle (-a')
    have h2 := hge (-a')
    simp only [Cut.neg] at h1 h2
    rw [show -(((-a' : Int) : Rat) * (2 : Rat) ^ (E + 1)) = (a' : Rat) * (2 : Rat) ^ (E + 1) by
      push_cast; grind] at h1 h2
    rw [hw, h1, h2]
    rw [show ((a' : Int) : Rat) * (2 : Rat) ^ (E + 1) ≤
        -((((2 * Q + (if t then 1 else 0) : Nat) : Int) : Rat) * (2 : Rat) ^ E) ↔
        (((2 * Q + (if t then 1 else 0) : Nat) : Int) : Rat) * (2 : Rat) ^ E ≤
          ((-a' : Int) : Rat) * (2 : Rat) ^ (E + 1) by push_cast; constructor <;> intro <;> grind,
      show -((((2 * Q + (if t then 1 else 0) : Nat) : Int) : Rat) * (2 : Rat) ^ E) ≤
        ((a' : Int) : Rat) * (2 : Rat) ^ (E + 1) ↔
        ((-a' : Int) : Rat) * (2 : Rat) ^ (E + 1) ≤
          (((2 * Q + (if t then 1 else 0) : Nat) : Int) : Rat) * (2 : Rat) ^ E by
        push_cast; constructor <;> intro <;> grind, key, key']
    cases t <;> simp <;> omega

end Mips.Fp
