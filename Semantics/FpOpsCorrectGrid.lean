import Semantics.FpOpsSpec
import Semantics.FpOpsCorrectNat

/-!
# FpOpsCorrectGrid — correct rounding on a uniform grid

The abstract part of the correctness proof of the rounding core. Near a positive exact value `v`,
the representable values are the multiples of a unit `g = 2h` (`GridHyp`: every element is such a
multiple or is below a grid point `L ≤ v`). Then the correctly rounded value of `v` is `j·g`, where
`j` is `v / g` rounded to an integer in the corresponding direction (`grid_correct`), and it is the
only one (`grid_unique`). `CorrectlyRounded` is symmetric under negation (`correctlyRounded_neg`).
-/

namespace Mips.Fp

/-! ## Rational helpers -/

theorem rat_two_zpow_pos (e : Int) : (0 : Rat) < (2 : Rat) ^ e := Rat.zpow_pos (by decide)

theorem rat_lt_or_le (a b : Rat) : a < b ∨ b ≤ a :=
  if h : a < b then .inl h else .inr (Rat.not_lt.mp h)

theorem rat_trichotomy (a b : Rat) : a < b ∨ a = b ∨ b < a := by
  rcases rat_lt_or_le a b with h | h
  · exact .inl h
  · rcases rat_lt_or_le b a with h' | h'
    · exact .inr (.inr h')
    · exact .inr (.inl (Rat.le_antisymm h' h))

theorem rat_mul_le_iff {a b g : Rat} (hg : 0 < g) : a * g ≤ b * g ↔ a ≤ b :=
  ⟨fun h => Rat.le_of_mul_le_mul_right h hg,
   fun h => Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hg)⟩

theorem rat_mul_lt_iff {a b g : Rat} (hg : 0 < g) : a * g < b * g ↔ a < b := Rat.mul_lt_mul_right hg

/-- Points `a·h`, `b·h` of the half grid compare as `a`, `b`. -/
theorem pt_le {a b : Int} {h : Rat} (hh : 0 < h) : (a : Rat) * h ≤ (b : Rat) * h ↔ a ≤ b := by
  rw [rat_mul_le_iff hh]; exact Rat.intCast_le_intCast

theorem pt_lt {a b : Int} {h : Rat} (hh : 0 < h) : (a : Rat) * h < (b : Rat) * h ↔ a < b := by
  rw [rat_mul_lt_iff hh]; exact Rat.intCast_lt_intCast

theorem pt_eq {a b : Int} {h : Rat} (hh : 0 < h) : (a : Rat) * h = (b : Rat) * h ↔ a = b := by
  constructor
  · intro e; exact Int.le_antisymm ((pt_le hh).1 (e ▸ Rat.le_refl)) ((pt_le hh).1 (e ▸ Rat.le_refl))
  · intro e; rw [e]

theorem pt_mid (a b : Int) (h : Rat) :
    (((2 * a : Int) : Rat) * h + ((2 * b : Int) : Rat) * h) / 2 = ((a + b : Int) : Rat) * h := by
  push_cast; grind

/-! ## Cuts -/

/-- A cut that describes a real number. -/
structure Cut.Valid (c : Cut) : Prop where
  le_of_le : ∀ a b, a ≤ b → c.le b → c.le a
  ge_of_le : ∀ a b, a ≤ b → c.ge a → c.ge b
  le_ge : ∀ a b, c.le a → c.ge b → a ≤ b
  total : ∀ a, c.le a ∨ c.ge a

theorem Cut.Valid.lt_of_le_not_le {c : Cut} (hc : c.Valid) {a b : Rat} (ha : c.le a) (hb : ¬ c.le b) :
    a < b := Rat.not_le.mp (fun h => hb (hc.le_of_le _ _ h ha))

theorem Cut.Valid.lt_of_not_ge_ge {c : Cut} (hc : c.Valid) {a b : Rat} (ha : ¬ c.ge a) (hb : c.ge b) :
    a < b := Rat.not_le.mp (fun h => ha (hc.ge_of_le _ _ h hb))

theorem Cut.Valid.ge_of_not_le {c : Cut} (hc : c.Valid) {a : Rat} (h : ¬ c.le a) : c.ge a :=
  (hc.total a).resolve_left h

theorem Cut.Valid.le_of_not_ge {c : Cut} (hc : c.Valid) {a : Rat} (h : ¬ c.ge a) : c.le a :=
  (hc.total a).resolve_right h

theorem Cut.ofRat_valid (v : Rat) : (Cut.ofRat v).Valid where
  le_of_le := fun _ _ h1 h2 => Rat.le_trans h1 h2
  ge_of_le := fun _ _ h1 h2 => Rat.le_trans h2 h1
  le_ge := fun _ _ h1 h2 => Rat.le_trans h1 h2
  total := fun _ => Rat.le_total

/-- The negated cut `-v`. -/
def Cut.neg (c : Cut) : Cut := ⟨fun y => c.ge (-y), fun y => c.le (-y)⟩

theorem Cut.neg_valid {c : Cut} (hc : c.Valid) : c.neg.Valid where
  le_of_le := fun _ _ h1 h2 => hc.ge_of_le _ _ (Rat.neg_le_neg h1) h2
  ge_of_le := fun _ _ h1 h2 => hc.le_of_le _ _ (Rat.neg_le_neg h1) h2
  le_ge := fun _ _ h1 h2 => Rat.neg_le_neg_iff.mp (hc.le_ge _ _ h2 h1)
  total := fun a => (hc.total (-a)).symm

theorem Cut.neg_neg (c : Cut) : c.neg.neg = c := by
  cases c; simp only [Cut.neg, Rat.neg_neg]

/-! ## The integer rounding seen through a cut

With half unit `h` (grid unit `2h`), `j·2h` is the result of rounding `v / 2h` to an integer in
direction `d`. -/

/-- `j` is `v / (2h)` rounded in direction `d`, stated with comparisons of `v` with the half grid. -/
def CutRound (c : Cut) (h : Rat) : Dir → Int → Prop
  | .down, j => c.le (((2 * j : Int) : Rat) * h) ∧ ¬ c.le (((2 * j + 2 : Int) : Rat) * h)
  | .up, j => c.ge (((2 * j : Int) : Rat) * h) ∧ ¬ c.ge (((2 * j - 2 : Int) : Rat) * h)
  | .nearest, j => c.le (((2 * j - 1 : Int) : Rat) * h) ∧ c.ge (((2 * j + 1 : Int) : Rat) * h) ∧
      (c.ge (((2 * j - 1 : Int) : Rat) * h) → j % 2 = 0) ∧
      (c.le (((2 * j + 1 : Int) : Rat) * h) → j % 2 = 0)

/-- **The shape of the representable values near `v`** with half unit `h` and precision `p`:
the multiples `0 … 2^p` of `2h` are representable; every representable value is a multiple of `2h`
or lies below the grid point `L`; the even multiples are even; every even value is a multiple of
`4h` or lies below `L`. -/
structure GridHyp (S E : Rat → Prop) (p : Nat) (h L : Rat) : Prop where
  h_pos : 0 < h
  p_pos : 1 ≤ p
  L_grid : ∃ i : Int, 0 ≤ i ∧ i ≤ 2 ^ p ∧ L = ((2 * i : Int) : Rat) * h
  S_grid : ∀ j : Int, 0 ≤ j → j ≤ 2 ^ p → S (((2 * j : Int) : Rat) * h)
  S_off : ∀ y, S y → (∃ i : Int, y = ((2 * i : Int) : Rat) * h) ∨ y < L
  E_grid : ∀ j : Int, 0 ≤ j → j ≤ 2 ^ p → j % 2 = 0 → E (((2 * j : Int) : Rat) * h)
  E_off : ∀ y, E y → (∃ i : Int, y = ((4 * i : Int) : Rat) * h) ∨ y < L

section grid

variable {S E : Rat → Prop} {p : Nat} {h L : Rat} {c : Cut}

theorem grid_down (G : GridHyp S E p h L) (hc : c.Valid) (hL : c.le L) {j : Int}
    (hj : CutRound c h .down j) (hj0 : 0 ≤ j) (hjp : j ≤ 2 ^ p) :
    RoundDown S c (((2 * j : Int) : Rat) * h) := by
  obtain ⟨i0, -, -, rfl⟩ := G.L_grid
  have hh := G.h_pos
  obtain ⟨h1, h2⟩ := hj
  -- `L ≤ 2jh`
  have hLj : 2 * i0 ≤ 2 * j := by
    have := hc.lt_of_le_not_le hL h2
    have := (pt_lt hh).1 this; omega
  refine ⟨G.S_grid j hj0 hjp, h1, fun y hy hyc => ?_⟩
  rcases G.S_off y hy with ⟨i, rfl⟩ | hy'
  · have := (pt_lt hh).1 (hc.lt_of_le_not_le hyc h2)
    exact (pt_le hh).2 (by omega)
  · have := (pt_le hh).2 hLj; grind

theorem grid_up (G : GridHyp S E p h L) (hc : c.Valid) (hL : c.le L) {j : Int}
    (hj : CutRound c h .up j) (hj0 : 0 ≤ j) (hjp : j ≤ 2 ^ p) :
    RoundUp S c (((2 * j : Int) : Rat) * h) := by
  have hh := G.h_pos
  obtain ⟨h1, h2⟩ := hj
  refine ⟨G.S_grid j hj0 hjp, h1, fun y hy hyc => ?_⟩
  rcases G.S_off y hy with ⟨i, rfl⟩ | hy'
  · have := (pt_lt hh).1 (hc.lt_of_not_ge_ge h2 hyc)
    exact (pt_le hh).2 (by omega)
  · exact absurd (hc.le_ge _ _ hL hyc) (Rat.not_le.mpr hy')

theorem grid_nearest (G : GridHyp S E p h L) (hc : c.Valid) (hL : c.le L) {j : Int}
    (hj : CutRound c h .nearest j) (hj0 : 0 ≤ j) (hjp : j ≤ 2 ^ p) :
    RoundNearestEven S E c (((2 * j : Int) : Rat) * h) := by
  obtain ⟨i0, -, -, rfl⟩ := G.L_grid
  have hh := G.h_pos
  obtain ⟨h1, h2, h3, h4⟩ := hj
  -- `L ≤ 2jh`
  have hLj : i0 ≤ j := by
    have := (pt_le hh).1 (hc.le_ge _ _ hL h2); omega
  have hL' : ((2 * i0 : Int) : Rat) * h ≤ ((2 * j : Int) : Rat) * h := (pt_le hh).2 (by omega)
  refine ⟨G.S_grid j hj0 hjp, fun y hy hlt => ?_, fun y hy hlt => ?_, fun y hy hne hle hge => ?_⟩
  · -- a smaller representable value is not nearer
    rcases G.S_off y hy with ⟨i, rfl⟩ | hy'
    · have hij := (pt_lt hh).1 hlt
      rw [pt_mid]
      exact hc.le_of_le _ _ ((pt_le hh).2 (by omega)) h1
    · rcases (show i0 < j ∨ j ≤ i0 by omega) with hi | hi
      · have e : ((2 * i0 : Int) : Rat) * h ≤ ((2 * j - 2 : Int) : Rat) * h := (pt_le hh).2 (by omega)
        apply hc.le_of_le _ _ _ h1
        push_cast at *; grind
      · have hi : i0 = j := by omega
        subst hi
        apply hc.le_of_le _ _ _ hL
        push_cast at *; grind
  · -- a larger representable value is not nearer
    rcases G.S_off y hy with ⟨i, rfl⟩ | hy'
    · have hij := (pt_lt hh).1 hlt
      rw [show (((2 * j : Int) : Rat) * h + ((2 * i : Int) : Rat) * h) / 2 = ((j + i : Int) : Rat) * h
        from pt_mid j i h]
      exact hc.ge_of_le _ _ ((pt_le hh).2 (by omega)) h2
    · grind
  · -- a tie: `v` is the midpoint of `2jh` and a neighbour, so `j` is even
    have hm := hc.le_ge _ _ hle hge
    rcases G.S_off y hy with ⟨i, rfl⟩ | hy'
    · rw [pt_mid] at hle hge
      have hij : i ≠ j := fun e => hne (by rw [e])
      rcases Int.lt_or_gt_of_ne hij with hij | hij
      · -- `y` below: the midpoint is at most `(2j - 1)h`, and `v` is at least that
        have a1 := (pt_le hh).1 (hc.le_ge _ _ h1 hge)
        have e : i + j = 2 * j - 1 := by omega
        rw [e] at hge
        exact G.E_grid j hj0 hjp (h3 hge)
      · have a1 := (pt_le hh).1 (hc.le_ge _ _ hle h2)
        have e : i + j = 2 * j + 1 := by omega
        rw [e] at hle
        exact G.E_grid j hj0 hjp (h4 hle)
    · exfalso
      rcases (show i0 < j ∨ j ≤ i0 by omega) with hi | hi
      · have e : ((2 * i0 : Int) : Rat) * h ≤ ((2 * j - 2 : Int) : Rat) * h := (pt_le hh).2 (by omega)
        have := hc.le_ge _ _ h1 hge
        push_cast at *; grind
      · have hi : i0 = j := by omega
        subst hi
        have := hc.le_ge _ _ hL hge
        push_cast at *; grind


/-- **Correct rounding on the grid**: if `j` is `v/(2h)` rounded to an integer in the direction of
`rm` (for a positive `v`), then `2jh` is `v` correctly rounded to `S`. -/
theorem grid_correct (G : GridHyp S E p h L) (hc : c.Valid) (hpos : ¬ c.ge 0) (hL : c.le L)
    {rm : RoundingMode} {j : Int} (hj : CutRound c h (dirOf rm false) j) (hj0 : 0 ≤ j)
    (hjp : j ≤ 2 ^ p) : CorrectlyRounded S E rm c (((2 * j : Int) : Rat) * h) := by
  cases rm
  · exact grid_nearest G hc hL hj hj0 hjp
  · exact ⟨fun _ => grid_down G hc hL hj hj0 hjp, fun h0 => absurd h0 hpos⟩
  · exact grid_up G hc hL hj hj0 hjp
  · exact grid_down G hc hL hj hj0 hjp

theorem roundDown_unique {S : Rat → Prop} {c : Cut} {r1 r2 : Rat} (h1 : RoundDown S c r1)
    (h2 : RoundDown S c r2) : r1 = r2 :=
  Rat.le_antisymm (h2.2.2 r1 h1.1 h1.2.1) (h1.2.2 r2 h2.1 h2.2.1)

theorem roundUp_unique {S : Rat → Prop} {c : Cut} {r1 r2 : Rat} (h1 : RoundUp S c r1)
    (h2 : RoundUp S c r2) : r1 = r2 :=
  Rat.le_antisymm (h1.2.2 r2 h2.1 h2.2.1) (h2.2.2 r1 h1.1 h1.2.1)

theorem nearest_not_lt (G : GridHyp S E p h L) (hc : c.Valid) (hL : c.le L)
    (hT : ¬ c.le (((2 * 2 ^ p : Int) : Rat) * h)) {r1 r2 : Rat}
    (h1 : RoundNearestEven S E c r1) (h2 : RoundNearestEven S E c r2) : ¬ r1 < r2 := by
  intro hlt
  obtain ⟨i0, hi0, hi0p, rfl⟩ := G.L_grid
  have hh := G.h_pos
  have m_ge := h1.2.2.1 r2 h2.1 hlt
  have m_le := h2.2.1 r1 h1.1 hlt
  have between : ∀ y, S y → r1 < y → r2 ≤ y := fun y hy hy1 => by
    have := hc.le_ge _ _ m_le (h1.2.2.1 y hy hy1); grind
  have hLm := hc.le_ge _ _ hL m_ge
  have hL0 : (0 : Rat) ≤ ((2 * i0 : Int) : Rat) * h := by
    have := (pt_le hh (a := 0) (b := 2 * i0)).2 (by omega); simpa using this
  have E2 := h2.2.2.2 r1 h1.1 (fun e => by rw [e] at hlt; exact Rat.lt_irrefl hlt) m_le m_ge
  rcases G.E_off r2 E2 with ⟨i2, rfl⟩ | hr2
  · rcases rat_lt_or_le r1 0 with hneg | hnn
    · have := between 0 (by simpa using G.S_grid 0 (by omega) (Int.pow_nonneg (by omega)))
        hneg
      grind
    · have E1 := h1.2.2.2 _ h2.1 (fun e => by rw [e] at hlt; exact Rat.lt_irrefl hlt)
        (by rw [show (((4 * i2 : Int) : Rat) * h + r1) / 2 = (r1 + ((4 * i2 : Int) : Rat) * h) / 2
              by grind]; exact m_le)
        (by rw [show (((4 * i2 : Int) : Rat) * h + r1) / 2 = (r1 + ((4 * i2 : Int) : Rat) * h) / 2
              by grind]; exact m_ge)
      rcases G.E_off r1 E1 with ⟨i1, rfl⟩ | hr1
      · have hlt' := (pt_lt hh).1 hlt
        have hr1v : c.le (((4 * i1 : Int) : Rat) * h) := hc.le_of_le _ _ (by grind) m_le
        have hTp := (pt_lt hh).1 (hc.lt_of_le_not_le hr1v hT)
        have hp2 : (2 : Int) ^ p = 2 * 2 ^ (p - 1) := by
          rw [← Int.pow_succ']; congr 1; have := G.p_pos; omega
        have hi1 : 0 ≤ i1 := by
          have := (pt_le hh (a := 0) (b := 4 * i1)).1 (by simpa using hnn); omega
        have hy := G.S_grid (2 * i1 + 1) (by omega) (by omega)
        have := (pt_le hh).1 (between _ hy ((pt_lt hh).2 (by omega)))
        omega
      · have := between _ (G.S_grid i0 hi0 hi0p) hr1
        grind
  · grind

/-- **Uniqueness**: under the same hypotheses (and `v < 2^p · 2h`) the correctly rounded value is
unique. -/
theorem grid_unique (G : GridHyp S E p h L) (hc : c.Valid) (hpos : ¬ c.ge 0) (hL : c.le L)
    (hT : ¬ c.le (((2 * 2 ^ p : Int) : Rat) * h)) {rm : RoundingMode} {r1 r2 : Rat}
    (h1 : CorrectlyRounded S E rm c r1) (h2 : CorrectlyRounded S E rm c r2) : r1 = r2 := by
  cases rm
  · exact Rat.le_antisymm (Rat.not_lt.mp (nearest_not_lt G hc hL hT h2 h1))
      (Rat.not_lt.mp (nearest_not_lt G hc hL hT h1 h2))
  · have h0 := hc.le_of_not_ge hpos
    exact roundDown_unique (h1.1 h0) (h2.1 h0)
  · exact roundUp_unique h1 h2
  · exact roundDown_unique h1 h2

/-! ## Negation -/

/-- The rounding mode for the negated value: RP and RM swap. -/
def RoundingMode.flip : RoundingMode → RoundingMode
  | .RN => .RN
  | .RZ => .RZ
  | .RP => .RM
  | .RM => .RP

theorem RoundingMode.flip_flip (rm : RoundingMode) : rm.flip.flip = rm := by cases rm <;> rfl

theorem dirOf_true (rm : RoundingMode) : dirOf rm true = dirOf rm.flip false := by cases rm <;> rfl

section neg
variable {S E : Rat → Prop} (hS : ∀ y, S (-y) ↔ S y) (hE : ∀ y, E (-y) ↔ E y)
include hS

theorem roundDown_neg {c : Cut} {r : Rat} (h : RoundDown S c r) : RoundUp S c.neg (-r) :=
  ⟨(hS r).2 h.1, by simp only [Cut.neg, Rat.neg_neg]; exact h.2.1,
   fun y hy hyc => Rat.neg_le_iff.mp (h.2.2 (-y) ((hS y).2 hy) hyc)⟩

theorem roundUp_neg {c : Cut} {r : Rat} (h : RoundUp S c r) : RoundDown S c.neg (-r) :=
  ⟨(hS r).2 h.1, by simp only [Cut.neg, Rat.neg_neg]; exact h.2.1,
   fun y hy hyc => Rat.le_neg_iff.mp (h.2.2 (-y) ((hS y).2 hy) hyc)⟩

include hE in
theorem nearest_neg {c : Cut} {r : Rat} (h : RoundNearestEven S E c r) :
    RoundNearestEven S E c.neg (-r) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨(hS r).2 h1, fun y hy hlt => ?_, fun y hy hlt => ?_, fun y hy hne hle hge => ?_⟩
  · have := h3 (-y) ((hS y).2 hy) (by grind)
    simp only [Cut.neg]; rw [show -((y + -r) / 2) = (r + -y) / 2 by grind]; exact this
  · have := h2 (-y) ((hS y).2 hy) (by grind)
    simp only [Cut.neg]; rw [show -((-r + y) / 2) = (-y + r) / 2 by grind]; exact this
  · simp only [Cut.neg] at hle hge
    rw [show -((y + -r) / 2) = (-y + r) / 2 by grind] at hle hge
    exact (hE r).2 (h4 (-y) ((hS y).2 hy) (by grind) hge hle)

include hE in
/-- Correct rounding commutes with negation (RP and RM swap). -/
theorem correctlyRounded_neg {rm : RoundingMode} {c : Cut} {r : Rat}
    (h : CorrectlyRounded S E rm c r) : CorrectlyRounded S E rm.flip c.neg (-r) := by
  cases rm
  · exact nearest_neg hS hE h
  · refine ⟨fun h0 => roundUp_neg hS (h.2 ?_), fun h0 => roundDown_neg hS (h.1 ?_)⟩
    · simpa [Cut.neg] using h0
    · simpa [Cut.neg] using h0
  · exact roundUp_neg hS h
  · exact roundDown_neg hS h

end neg

/-! ## Two readings of the definitions -/

/-- "Nearest" with midpoints is "nearest" with distances, for a rational `v`. -/
theorem nearest_ofRat_iff {S E : Rat → Prop} {v r : Rat} :
    RoundNearestEven S E (Cut.ofRat v) r ↔
      S r ∧ (∀ y, S y → (r - v).abs ≤ (y - v).abs) ∧
        (∀ y, S y → y ≠ r → (y - v).abs = (r - v).abs → E r) := by
  simp only [RoundNearestEven, Cut.ofRat, Rat.abs]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, fun y hy => ?_, fun y hy hne he => ?_⟩
    · rcases rat_trichotomy y r with hl | he | hg
      · have := h2 y hy hl; split <;> split <;> grind
      · subst he; exact Rat.le_refl
      · have := h3 y hy hg; split <;> split <;> grind
    · rcases rat_trichotomy y r with hl | he' | hg
      · have := h2 y hy hl; exact h4 y hy hne this (by split at he <;> split at he <;> grind)
      · exact absurd he' hne
      · have := h3 y hy hg; exact h4 y hy hne (by split at he <;> split at he <;> grind)
          (by rw [show (y + r) / 2 = (r + y) / 2 by grind]; exact this)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun y hy hl => ?_, fun y hy hg => ?_, fun y hy hne hle hge => ?_⟩
    · have := h2 y hy; split at this <;> split at this <;> grind
    · have := h2 y hy; split at this <;> split at this <;> grind
    · exact h3 y hy hne (by split <;> split <;> grind)

/-- A correctly rounded value that lies in a smaller set is correctly rounded to that set. -/
theorem correctlyRounded_mono {S S' E : Rat → Prop} {rm : RoundingMode} {c : Cut} {r : Rat}
    (h : CorrectlyRounded S E rm c r) (hr : S' r) (hS : ∀ y, S' y → S y) :
    CorrectlyRounded S' E rm c r := by
  cases rm
  · obtain ⟨-, h2, h3, h4⟩ := h
    exact ⟨hr, fun y hy => h2 y (hS y hy), fun y hy => h3 y (hS y hy), fun y hy => h4 y (hS y hy)⟩
  · exact ⟨fun h0 => ⟨hr, (h.1 h0).2.1, fun y hy => (h.1 h0).2.2 y (hS y hy)⟩,
      fun h0 => ⟨hr, (h.2 h0).2.1, fun y hy => (h.2 h0).2.2 y (hS y hy)⟩⟩
  · exact ⟨hr, h.2.1, fun y hy => h.2.2 y (hS y hy)⟩
  · exact ⟨hr, h.2.1, fun y hy => h.2.2 y (hS y hy)⟩

end grid

end Mips.Fp
