import Semantics.FpOpsCorrectExact

/-!
# FpOpsCorrectDivSqrt — quotient and square root agree with their sticky results

`Exact.div_agree`: `Exact.div p a b` agrees with the true quotient `a / b` on every grid the rounding
to precision `p` uses. `Exact.sqrt_agree`: `Exact.sqrt p a` agrees with `√a` (`Cut.sqrt`) likewise.
-/

namespace Mips.Fp

theorem rat_le_div_iff {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  have := (Rat.div_lt_iff (a := b) (c := a) hc)
  constructor
  · intro h; exact Rat.not_lt.mp (fun h' => Rat.not_lt.mpr h (this.2 h'))
  · intro h; exact Rat.not_lt.mp (fun h' => Rat.not_lt.mpr h (this.1 h'))

theorem rat_div_le_iff {a b c : Rat} (hc : 0 < c) : b / c ≤ a ↔ b ≤ a * c := by
  have := (Rat.lt_div_iff (a := a) (b := b) hc)
  constructor
  · intro h; exact Rat.not_lt.mp (fun h' => Rat.not_lt.mpr h (this.2 h'))
  · intro h; exact Rat.not_lt.mp (fun h' => Rat.not_lt.mpr h (this.1 h'))

theorem bitLen_ge_of (n m : Nat) (h : 2 ^ m ≤ n) : m + 1 ≤ bitLen n := by
  have h1 := lt_two_pow_bitLen n
  have : 2 ^ m < 2 ^ bitLen n := Nat.lt_of_le_of_lt h h1
  have := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).1 this
  omega

/-- Comparisons of `(n / d) · 2^(E+1)` with the grid of unit `2^(E+1)`. -/
theorem quot_cmp (n d : Nat) (hd : 0 < d) (E : Int) :
    (∀ a : Int, (a : Rat) * (2 : Rat) ^ E ≤ (n : Rat) / d * (2 : Rat) ^ E ↔ a ≤ (n / d : Nat)) ∧
    (∀ a : Int, (n : Rat) / d * (2 : Rat) ^ E ≤ (a : Rat) * (2 : Rat) ^ E ↔
      (if n % d = 0 then ((n / d : Nat) : Int) ≤ a else ((n / d : Nat) : Int) + 1 ≤ a)) := by
  have hP := rat_two_zpow_pos E
  have hd' : (0 : Rat) < d := Rat.natCast_pos.2 hd
  have hn := Nat.div_add_mod n d
  have hr := Nat.mod_lt n hd
  generalize n / d = Q at *
  generalize n % d = r at *
  have hdi : (0 : Int) < d := by omega
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [rat_mul_le_iff hP, rat_le_div_iff hd',
      show (a : Rat) * (d : Rat) = ((a * (d : Int) : Int) : Rat) by push_cast; rfl,
      show (n : Rat) = (((n : Nat) : Int) : Rat) by rfl, Rat.intCast_le_intCast]
    constructor
    · intro h
      refine Classical.byContradiction fun h' => ?_
      have := Int.mul_le_mul_of_nonneg_right (show (Q : Int) + 1 ≤ a by omega) (Int.le_of_lt hdi)
      rw [Int.add_mul] at this
      have e : ((d * Q : Nat) : Int) = (Q : Int) * d := by push_cast; rw [Int.mul_comm]
      omega
    · intro h
      have := Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt hdi)
      have e : ((d * Q : Nat) : Int) = (Q : Int) * d := by push_cast; rw [Int.mul_comm]
      omega
  · rw [rat_mul_le_iff hP, rat_div_le_iff hd',
      show (a : Rat) * (d : Rat) = ((a * (d : Int) : Int) : Rat) by push_cast; rfl,
      show (n : Rat) = (((n : Nat) : Int) : Rat) by rfl, Rat.intCast_le_intCast]
    have e : ((d * Q : Nat) : Int) = (Q : Int) * d := by push_cast; rw [Int.mul_comm]
    split
    · constructor
      · intro h
        refine Classical.byContradiction fun h' => ?_
        have := Int.mul_le_mul_of_nonneg_right (show a ≤ (Q : Int) - 1 by omega) (Int.le_of_lt hdi)
        rw [Int.sub_mul] at this
        omega
      · intro h
        have := Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt hdi)
        omega
    · constructor
      · intro h
        refine Classical.byContradiction fun h' => ?_
        have := Int.mul_le_mul_of_nonneg_right (show a ≤ (Q : Int) by omega) (Int.le_of_lt hdi)
        omega
      · intro h
        have := Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt hdi)
        rw [Int.add_mul] at this
        omega

theorem quot_identity (as bs : Nat) (hbs : bs ≠ 0) (ea eb : Int) (k : Nat) :
    ((as : Rat) * (2 : Rat) ^ ea) / ((bs : Rat) * (2 : Rat) ^ eb) =
      ((as * 2 ^ k : Nat) : Rat) / bs * (2 : Rat) ^ (ea - eb - k) := by
  have e1 : (2 : Rat) ^ ea = (2 : Rat) ^ (ea - eb - k) * ((2 ^ k : Nat) : Rat) * (2 : Rat) ^ eb := by
    rw [← two_zpow_nat, ← two_zpow_add, ← two_zpow_add]; congr 1; omega
  have hR := rat_two_zpow_pos eb
  have hB : (bs : Rat) ≠ 0 := by
    have : (0 : Rat) < bs := Rat.natCast_pos.2 (Nat.pos_of_ne_zero hbs); grind
  rw [e1, Rat.natCast_mul]
  generalize (2 : Rat) ^ (ea - eb - k) = T
  generalize ((2 ^ k : Nat) : Rat) = K
  generalize (2 : Rat) ^ eb = R at *
  have hR' : R ≠ 0 := by grind
  rw [Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  have := Rat.mul_inv_cancel R hR'
  grind

theorem Exact.toRat_signed (v : Exact) :
    v.toRat = if v.sign then -((v.sig : Rat) * (2 : Rat) ^ v.exp) else (v.sig : Rat) * (2 : Rat) ^ v.exp := by
  simp only [Exact.toRat]; cases v.sign <;> simp <;> grind

theorem signed_div (sa sb : Bool) (X Y : Rat) :
    (if sa then -X else X) / (if sb then -Y else Y) = if (sa != sb) then -(X / Y) else X / Y := by
  cases sa <;> cases sb <;> simp [Rat.div_def] <;> grind

/-- `ofRat` of a signed value, seen from the positive side. -/
theorem signed_cut (s : Bool) (V : Rat) :
    (if s then (Cut.ofRat (if s then -V else V)).neg else Cut.ofRat (if s then -V else V)).le =
      (fun y => y ≤ V) ∧
    (if s then (Cut.ofRat (if s then -V else V)).neg else Cut.ofRat (if s then -V else V)).ge =
      (fun y => V ≤ y) := by
  cases s
  · exact ⟨rfl, rfl⟩
  · simp only [ite_true, Cut.neg, Cut.ofRat]
    constructor <;> funext y <;> apply propext <;> constructor <;> intro h <;> grind

/-- **`Exact.div` is a sticky quotient**: it agrees with the true quotient on the rounding grids. -/
theorem Exact.div_agree (p : Nat) (a b : Exact) (ha : a.sig ≠ 0) (hb : b.sig ≠ 0) :
    (Exact.div p a b).sig ≠ 0 ∧
    CutAgree (Cut.ofRat (a.toRat / b.toRat)) (Exact.div p a b).toRat
      ((Exact.div p a b).exp + bitLen (Exact.div p a b).sig - ((p : Nat) : Int) - 1) := by
  have hbpos : 0 < b.sig := Nat.pos_of_ne_zero hb
  -- the quotient is large
  have hQ : 2 ^ (p + 2) ≤ a.sig * 2 ^ (p + 2 + bitLen b.sig) / b.sig := by
    rw [Nat.le_div_iff_mul_le hbpos]
    have h1 := lt_two_pow_bitLen b.sig
    calc 2 ^ (p + 2) * b.sig ≤ 2 ^ (p + 2) * 2 ^ bitLen b.sig := Nat.mul_le_mul_left _ (Nat.le_of_lt h1)
      _ = 2 ^ (p + 2 + bitLen b.sig) := (Nat.pow_add _ _ _).symm
      _ ≤ a.sig * 2 ^ (p + 2 + bitLen b.sig) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero ha)
  simp only [Exact.div]
  generalize p + 2 + bitLen b.sig = k at *
  generalize hn : a.sig * 2 ^ k = n at *
  have ht : (if n % b.sig = 0 then 0 else 1) = (if decide (n % b.sig ≠ 0) = true then 1 else 0) := by
    by_cases h : n % b.sig = 0 <;> simp [h]
  rw [ht]
  have hbig : p + 4 ≤ bitLen (2 * (n / b.sig) + (if decide (n % b.sig ≠ 0) = true then 1 else 0)) := by
    have := bitLen_ge_of (2 * (n / b.sig) + (if decide (n % b.sig ≠ 0) = true then 1 else 0)) (p + 3)
      (by
        rw [Nat.pow_succ]
        have := Nat.le_add_right (2 * (n / b.sig)) (if decide (n % b.sig ≠ 0) = true then 1 else 0)
        omega)
    omega
  refine ⟨by have := Nat.two_pow_pos (p + 2); omega, CutAgree.mono (cutAgree_sticky _ _ _ _ _ ?_ ?_) (by omega)⟩
  all_goals
    have hx : a.toRat / b.toRat = if (a.sign != b.sign) then
        -((n : Rat) / b.sig * (2 : Rat) ^ (a.exp - b.exp - k)) else (n : Rat) / b.sig * (2 : Rat) ^ (a.exp - b.exp - k) := by
      rw [Exact.toRat_signed a, Exact.toRat_signed b, signed_div, ← hn, ← quot_identity _ _ hb]
    have e1 : a.exp - b.exp - (k : Int) - 1 + 1 = a.exp - b.exp - k := by omega
    intro a'
    rw [hx, e1]
  · rw [(signed_cut _ _).1]; exact (quot_cmp n b.sig hbpos _).1 a'
  · rw [(signed_cut _ _).2]; show _ ≤ _ ↔ _
    rw [(quot_cmp n b.sig hbpos _).2 a']
    by_cases h : n % b.sig = 0 <;> simp [h]

/-! ## Square root -/

theorem sq_cmp (n r : Nat) (h1 : r * r ≤ n) (h2 : n < (r + 1) * (r + 1)) (a : Int) :
    ((a ≤ 0 ∨ a * a ≤ (n : Int)) ↔ a ≤ r) ∧
    ((0 ≤ a ∧ (n : Int) ≤ a * a) ↔ (if decide (r * r ≠ n) = true then (r : Int) + 1 ≤ a else (r : Int) ≤ a)) := by
  have c1 : ((r * r : Nat) : Int) = (r : Int) * r := by push_cast; rfl
  have c2 : (((r + 1) * (r + 1) : Nat) : Int) = ((r : Int) + 1) * ((r : Int) + 1) := by push_cast; rfl
  have e1 : ((r : Int) + 1) * ((r : Int) + 1) = (r : Int) * r + 2 * r + 1 := by grind
  have e2 : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by grind
  constructor
  · constructor
    · rintro (h | h)
      · omega
      · refine Classical.byContradiction fun h' => ?_
        have := Int.mul_self_le_mul_self (show (0 : Int) ≤ r + 1 by omega) (show (r : Int) + 1 ≤ a by omega)
        omega
    · intro h
      by_cases h0 : a ≤ 0
      · exact .inl h0
      · right
        have := Int.mul_self_le_mul_self (show (0 : Int) ≤ a by omega) h
        omega
  · by_cases hr : r * r = n
    · simp only [hr, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
      constructor
      · rintro ⟨h0, h⟩
        refine Classical.byContradiction fun h' => ?_
        have := Int.mul_self_le_mul_self (show (0 : Int) ≤ a + 1 by omega) (show a + 1 ≤ (r : Int) by omega)
        omega
      · intro h
        have := Int.mul_self_le_mul_self (show (0 : Int) ≤ r by omega) h
        exact ⟨by omega, by omega⟩
    · simp only [ne_eq, hr, not_false_eq_true, decide_true, ite_true]
      constructor
      · rintro ⟨h0, h⟩
        refine Classical.byContradiction fun h' => ?_
        have := Int.mul_self_le_mul_self h0 (show a ≤ (r : Int) by omega)
        omega
      · intro h
        have := Int.mul_self_le_mul_self (show (0 : Int) ≤ r + 1 by omega) h
        exact ⟨by omega, by omega⟩

theorem Cut.sqrt_valid (x : Rat) : (Cut.sqrt x).Valid where
  le_of_le := fun a b hab hb => by
    simp only [Cut.sqrt] at *
    rcases hb with hb | hb
    · exact .inl (Rat.le_trans hab hb)
    · rcases rat_lt_or_le 0 a with ha | ha
      · right
        have h1 := Rat.mul_le_mul_of_nonneg_left hab (Rat.le_of_lt ha)
        have h2 := Rat.mul_le_mul_of_nonneg_right hab (Rat.le_trans (Rat.le_of_lt ha) hab)
        grind
      · exact .inl ha
  ge_of_le := fun a b hab ha => by
    simp only [Cut.sqrt] at *
    obtain ⟨h0, h⟩ := ha
    refine ⟨Rat.le_trans h0 hab, ?_⟩
    have := Rat.mul_le_mul_of_nonneg_left hab h0
    have := Rat.mul_le_mul_of_nonneg_right hab (Rat.le_trans h0 hab)
    grind
  le_ge := fun a b ha hb => by
    simp only [Cut.sqrt] at *
    obtain ⟨h0, h⟩ := hb
    rcases ha with ha | ha
    · exact Rat.le_trans ha h0
    · refine Rat.not_lt.mp fun hlt => ?_
      have ha0 : 0 < a := by grind
      have h1 := Rat.mul_lt_mul_of_pos_right hlt ha0
      have h2 := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt hlt) h0
      grind
  total := fun a => by
    simp only [Cut.sqrt]
    rcases rat_lt_or_le 0 a with ha | ha
    · rcases rat_lt_or_le (a * a) x with h | h
      · exact .inl (.inr (Rat.le_of_lt h))
      · exact .inr ⟨Rat.le_of_lt ha, h⟩
    · exact .inl (.inl ha)


/-- **`Exact.sqrt` is a sticky square root**: it agrees with `√x` on the rounding grids. -/
theorem Exact.sqrt_agree (p : Nat) (a : Exact) (ha : a.sig ≠ 0) (hs : a.sign = false) :
    (Exact.sqrt p a).sig ≠ 0 ∧
    CutAgree (Cut.sqrt a.toRat) (Exact.sqrt p a).toRat
      ((Exact.sqrt p a).exp + bitLen (Exact.sqrt p a).sig - ((p : Nat) : Int) - 1) := by
  simp only [Exact.sqrt]
  generalize hsh : 2 * (p + 2) + (if a.exp % 2 = 0 then 0 else 1) = sh
  have hpar : (a.exp - sh) % 2 = 0 := by subst hsh; split <;> omega
  have hsh2 : 2 * (p + 2) ≤ sh := by subst hsh; split <;> omega
  generalize hn : a.sig * 2 ^ sh = n
  have hspec := isqrt_spec n
  generalize isqrt n = r at hspec ⊢
  obtain ⟨h1, h2⟩ := hspec
  -- the root is large
  have hr : 2 ^ (p + 2) ≤ r := by
    refine Classical.byContradiction fun h' => ?_
    have h3 : r + 1 ≤ 2 ^ (p + 2) := by omega
    have h4 := Nat.mul_self_le_mul_self h3
    have h5 : 2 ^ (p + 2) * 2 ^ (p + 2) ≤ n := by
      rw [← Nat.pow_add, ← hn]
      calc 2 ^ (p + 2 + (p + 2)) ≤ 2 ^ sh := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ a.sig * 2 ^ sh := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero ha)
    omega
  have ht : (if r * r = n then 0 else 1) = (if decide (r * r ≠ n) = true then 1 else 0) := by
    by_cases h : r * r = n <;> simp [h]
  rw [ht]
  have hbig : p + 4 ≤ bitLen (2 * r + (if decide (r * r ≠ n) = true then 1 else 0)) := by
    have := bitLen_ge_of (2 * r + (if decide (r * r ≠ n) = true then 1 else 0)) (p + 3)
      (by
        rw [Nat.pow_succ]
        have := Nat.le_add_right (2 * r) (if decide (r * r ≠ n) = true then 1 else 0)
        omega)
    omega
  refine ⟨by have := Nat.two_pow_pos (p + 2); omega, CutAgree.mono (cutAgree_sticky _ _ _ _ _ ?_ ?_) (by omega)⟩
  all_goals
    generalize hh : (a.exp - sh) / 2 = h
    have e1 : h - 1 + 1 = h := by omega
    have e2 : a.exp = sh + 2 * h := by omega
    have hx : a.toRat = ((n : Int) : Rat) * ((2 : Rat) ^ h * (2 : Rat) ^ h) := by
      rw [Exact.toRat_signed, hs]
      simp only [Bool.false_eq_true, ite_false]
      rw [← hn, e2, two_zpow_add, show 2 * h = h + h by omega, two_zpow_add, two_zpow_nat]
      push_cast; grind
    have hH : (0 : Rat) < (2 : Rat) ^ h * (2 : Rat) ^ h := Rat.mul_pos (rat_two_zpow_pos h) (rat_two_zpow_pos h)
    have sq : ∀ a' : Int, ((a' : Rat) * (2 : Rat) ^ h) * ((a' : Rat) * (2 : Rat) ^ h) =
        ((a' * a' : Int) : Rat) * ((2 : Rat) ^ h * (2 : Rat) ^ h) := fun a' => by push_cast; grind
    have z : ∀ a' : Int, (a' : Rat) * (2 : Rat) ^ h ≤ 0 ↔ a' ≤ 0 := fun a' => by
      rw [show (0 : Rat) = ((0 : Int) : Rat) * (2 : Rat) ^ h by simp]; exact pt_le (rat_two_zpow_pos h)
    have z' : ∀ a' : Int, 0 ≤ (a' : Rat) * (2 : Rat) ^ h ↔ 0 ≤ a' := fun a' => by
      rw [show (0 : Rat) = ((0 : Int) : Rat) * (2 : Rat) ^ h by simp]; exact pt_le (rat_two_zpow_pos h)
    intro a'
    simp only [Bool.false_eq_true, ite_false, Cut.sqrt]
    rw [e1, hx]
    simp only [sq, z, z', rat_mul_le_iff hH, Rat.intCast_le_intCast]
  · exact (sq_cmp n r h1 h2 a').1
  · exact (sq_cmp n r h1 h2 a').2

end Mips.Fp
