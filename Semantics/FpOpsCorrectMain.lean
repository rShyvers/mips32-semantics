import Semantics.FpOpsCorrectCore

/-!
# FpOpsCorrectMain — `roundCore_correct`

For every nonzero exact value `w` and every cut `c` that agrees with it on the grids the core uses
(in particular `Cut.ofRat w.toRat`), `Format.roundCore f rm false w` meets `Format.RoundSpec`:
correct rounding (with the exponent range unbounded above), overflow and its delivered encoding,
the encoding's value and sign, inexact, and tininess after rounding.
-/

namespace Mips.Fp

theorem signed_mul (s : Bool) (y : Rat) : (if s then (-1 : Rat) else 1) * y = if s then -y else y := by
  cases s <;> simp; grind

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem Format.qMin_eq (f : Format) : f.qMin = 1 - (f.bias : Int) - f.fracBits := rfl
theorem Format.qMax_eq (f : Format) : f.qMax = (f.bias : Int) - f.fracBits := rfl

/-- The record the core builds, given the integer `j` at exponent `q`. -/
theorem assemble (f : Format) (hf : f.WF) (rm : RoundingMode) (s : Bool) (c : Cut) (j : Nat) (q : Int)
    (ovb : Nat) (inex tinyB : Bool) (T : Prop)
    (hcr : CorrectlyRounded f.Unbounded f.UnboundedEven rm c
      (if s then -((j : Rat) * (2 : Rat) ^ q) else (j : Rat) * (2 : Rat) ^ q))
    (hsign : c.ge 0 ↔ s = true)
    (hinex : inex = true ↔ ¬ (c.le (if s then -((j : Rat) * (2 : Rat) ^ q) else (j : Rat) * (2 : Rat) ^ q) ∧
      c.ge (if s then -((j : Rat) * (2 : Rat) ^ q) else (j : Rat) * (2 : Rat) ^ q)))
    (htiny : tinyB = true ↔ T)
    (hovT : f.qMax ≤ q → ¬ T)
    (hovb : ovb = f.overflowResult rm s)
    (hjp : j ≤ 2 ^ (f.fracBits + 1)) (hq : f.qMin ≤ q) (hjq : f.qMin < q → 2 ^ f.fracBits ≤ j)
    (hT : T ↔ ∃ u : Rat, CorrectlyRounded f.UnboundedRange f.UnboundedRangeEven rm c u ∧
      u.abs < (2 : Rat) ^ f.emin) :
    f.RoundSpec rm c
      (if f.qMax < (if (j == 2 ^ (f.fracBits + 1)) = true then q + 1 else q) then
        { bits := ovb, overflow := true, tiny := false, inexact := inex }
      else
        { bits := if (if (j == 2 ^ (f.fracBits + 1)) = true then 2 ^ f.fracBits else j) < 2 ^ f.fracBits then
              f.pack s 0 (if (j == 2 ^ (f.fracBits + 1)) = true then 2 ^ f.fracBits else j)
            else f.pack s ((if (j == 2 ^ (f.fracBits + 1)) = true then q + 1 else q) - f.qMin + 1).toNat
              ((if (j == 2 ^ (f.fracBits + 1)) = true then 2 ^ f.fracBits else j) - 2 ^ f.fracBits),
          overflow := false, tiny := tinyB, inexact := inex }) := by
  have hb := f.bias_pos hf
  have hfb := hf.2
  have hqm := f.qMin_eq
  have hqM := f.qMax_eq
  have hxM := f.expMax_eq hf
  have hF : 0 < 2 ^ f.fracBits := Nat.two_pow_pos _
  have h2p : 2 ^ (f.fracBits + 1) = 2 * 2 ^ f.fracBits := Nat.pow_succ'
  have hmaxv : f.maxValue = ((2 ^ (f.fracBits + 1) - 1 : Nat) : Rat) * (2 : Rat) ^ f.qMax := by
    simp only [Format.maxValue, Format.prec, Format.emax_sub]
  have hx0 : (0 : Rat) ≤ (j : Rat) * (2 : Rat) ^ q :=
    Rat.mul_nonneg (Rat.natCast_nonneg) (Rat.le_of_lt (rat_two_zpow_pos _))
  have habs := abs_signed s hx0
  generalize hr : (if s then -((j : Rat) * (2 : Rat) ^ q) else (j : Rat) * (2 : Rat) ^ q) = r at *
  have hsg : ∀ (E fr : Nat), E < f.expMax → fr < 2 ^ f.fracBits →
      (f.pack s E fr / 2 ^ (f.expBits + f.fracBits) % 2 = 1 ↔ c.ge 0) := fun E fr hE hfr => by
    rw [f.signBit_pack s E fr (Nat.lt_trans hE f.expMax_lt) hfr, hsign]
  by_cases hc1 : j = 2 ^ (f.fracBits + 1)
  · have hbq : (j == 2 ^ (f.fracBits + 1)) = true := beq_iff_eq.2 hc1
    simp only [hbq, ite_true, Nat.lt_irrefl, ite_false, Nat.sub_self]
    split
    · rename_i hov
      refine ⟨r, hcr, ⟨fun _ => ?_, fun _ => rfl⟩, (fun h => by cases h),
        fun _ => ⟨s, hsign.symm, hovb⟩, ?_, hinex, ⟨(fun h => by cases h), fun h => absurd (hT.2 h) (hovT (by omega))⟩⟩
      · rw [habs, hmaxv, hc1, nat_zpow_lt_iff, show min f.qMax q = f.qMax by omega,
          show (f.qMax - f.qMax).toNat = 0 by omega]
        have : 1 ≤ 2 ^ (q - f.qMax).toNat := Nat.one_le_two_pow
        have : 2 ^ (f.fracBits + 1) * 1 ≤ 2 ^ (f.fracBits + 1) * 2 ^ (q - f.qMax).toNat :=
          Nat.mul_le_mul_left _ this
        simp only [Nat.pow_zero, Nat.mul_one] at *; omega
      · rw [hovb, f.overflowResult_sign, hsign]
    · rename_i hov
      have hE : (q + 1 - f.qMin + 1).toNat < f.expMax := by omega
      refine ⟨r, hcr, ⟨(fun h => by cases h), (fun h => absurd h ?_)⟩, fun _ => ?_,
        (fun h => by cases h), hsg _ _ hE hF, hinex, ?_⟩
      · rw [habs, hmaxv, hc1, nat_zpow_lt_iff, show min f.qMax q = q by omega,
          show (q - q).toNat = 0 by omega]
        have : 2 ^ 1 ≤ 2 ^ (f.qMax - q).toNat := Nat.pow_le_pow_right (by omega) (by omega)
        have : (2 ^ (f.fracBits + 1) - 1) * 2 ^ 1 ≤ (2 ^ (f.fracBits + 1) - 1) * 2 ^ (f.qMax - q).toNat :=
          Nat.mul_le_mul_left _ this
        simp only [Nat.pow_zero, Nat.mul_one, Nat.pow_one] at *; omega
      · have hE0 : ¬ (q + 1 - f.qMin + 1).toNat = 0 := by omega
        rw [f.value_pack s _ 0 hE hF, ← hr, signed_mul, ite_neg' hE0, ite_neg' hE0, Nat.zero_add, hc1]
        congr 1
        have e1 : ((q + 1 - f.qMin + 1).toNat : Int) - (f.bias : Int) - f.fracBits = q + 1 := by omega
        rw [e1, Rat.zpow_add_one (by decide), h2p]
        cases s <;> simp <;> grind
      · exact htiny.trans hT
  · have hbq : (j == 2 ^ (f.fracBits + 1)) = false := by simpa using hc1
    simp only [hbq, Bool.false_eq_true, ite_false]
    have hjlt : j < 2 ^ (f.fracBits + 1) := by omega
    split
    · rename_i hov
      refine ⟨r, hcr, ⟨fun _ => ?_, fun _ => rfl⟩, (fun h => by cases h),
        fun _ => ⟨s, hsign.symm, hovb⟩, ?_, hinex, ⟨(fun h => by cases h), fun h => absurd (hT.2 h) (hovT (by omega))⟩⟩
      · have hjq' := hjq (by omega)
        rw [habs, hmaxv, nat_zpow_lt_iff, show min f.qMax q = f.qMax by omega,
          show (f.qMax - f.qMax).toNat = 0 by omega]
        have : 2 ^ 1 ≤ 2 ^ (q - f.qMax).toNat := Nat.pow_le_pow_right (by omega) (by omega)
        have : 2 ^ f.fracBits * 2 ^ 1 ≤ j * 2 ^ (q - f.qMax).toNat := Nat.mul_le_mul hjq' this
        simp only [Nat.pow_zero, Nat.mul_one, Nat.pow_one] at *; omega
      · rw [hovb, f.overflowResult_sign, hsign]
    · rename_i hov
      split
      · rename_i hsub
        have hqq : q = f.qMin := Classical.byContradiction fun h => by have := hjq (by omega); omega
        have hE : 0 < f.expMax := by omega
        refine ⟨r, hcr, ⟨(fun h => by cases h), (fun h => absurd h ?_)⟩, fun _ => ?_,
          (fun h => by cases h), hsg _ _ hE hsub, hinex, htiny.trans hT⟩
        · rw [habs, hmaxv, nat_zpow_lt_iff, show min f.qMax q = q by omega,
            show (q - q).toNat = 0 by omega]
          have : 1 ≤ 2 ^ (f.qMax - q).toNat := Nat.one_le_two_pow
          have : (2 ^ (f.fracBits + 1) - 1) * 1 ≤ (2 ^ (f.fracBits + 1) - 1) * 2 ^ (f.qMax - q).toNat :=
            Nat.mul_le_mul_left _ this
          simp only [Nat.pow_zero, Nat.mul_one] at *; omega
        · rw [f.value_pack s 0 j hE hsub, ← hr, signed_mul, ite_pos' rfl, ite_pos' rfl, hqq]
          congr 1; cases s <;> simp; grind
      · rename_i hsub
        have hE : (q - f.qMin + 1).toNat < f.expMax := by omega
        have hfr : j - 2 ^ f.fracBits < 2 ^ f.fracBits := by omega
        refine ⟨r, hcr, ⟨(fun h => by cases h), (fun h => absurd h ?_)⟩, fun _ => ?_,
          (fun h => by cases h), hsg _ _ hE hfr, hinex, htiny.trans hT⟩
        · rw [habs, hmaxv, nat_zpow_lt_iff, show min f.qMax q = q by omega,
            show (q - q).toNat = 0 by omega]
          have : 1 ≤ 2 ^ (f.qMax - q).toNat := Nat.one_le_two_pow
          have : (2 ^ (f.fracBits + 1) - 1) * 1 ≤ (2 ^ (f.fracBits + 1) - 1) * 2 ^ (f.qMax - q).toNat :=
            Nat.mul_le_mul_left _ this
          simp only [Nat.pow_zero, Nat.mul_one] at *; omega
        · have hE0 : ¬ (q - f.qMin + 1).toNat = 0 := by omega
          rw [f.value_pack s _ _ hE hfr, ← hr, signed_mul, ite_neg' hE0, ite_neg' hE0,
            Nat.sub_add_cancel (by omega)]
          have e1 : ((q - f.qMin + 1).toNat : Int) - (f.bias : Int) - f.fracBits = q := by omega
          rw [e1]; congr 1; cases s <;> simp; grind

theorem signed_half (s : Bool) (j : Nat) (q : Int) :
    (if s then -((j : Rat) * (2 : Rat) ^ q) else (j : Rat) * (2 : Rat) ^ q) =
      (((if s then -(2 * (j : Int)) else 2 * (j : Int)) : Int) : Rat) * (2 : Rat) ^ (q - 1) := by
  rw [two_zpow_pred q]; cases s <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> push_cast <;> grind

theorem tinyB_iff (a b : Prop) [Decidable a] [Decidable b] (x y : Nat) :
    (decide a && !(decide b && x == y)) = true ↔ (a ∧ ¬ (b ∧ x = y)) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hxy : x = y <;> simp_all

theorem rat_mul_eq_iff {a b c : Rat} (hc : 0 < c) : a * c = b * c ↔ a = b := by
  constructor
  · intro h
    exact Rat.le_antisymm ((rat_mul_le_iff hc).1 (h ▸ Rat.le_refl)) ((rat_mul_le_iff hc).1 (h ▸ Rat.le_refl))
  · intro h; rw [h]

theorem CutAgree.point {c : Cut} {v : Rat} {e0 : Int} (h : CutAgree c v e0) (a e : Int) (he : e0 ≤ e) :
    (c.le ((a : Rat) * (2 : Rat) ^ e) ∧ c.ge ((a : Rat) * (2 : Rat) ^ e)) ↔ (a : Rat) * (2 : Rat) ^ e = v := by
  rw [(h a e he).1, (h a e he).2]
  exact ⟨fun h => Rat.le_antisymm h.1 h.2, fun h => ⟨h ▸ Rat.le_refl, h ▸ Rat.le_refl⟩⟩

/-- **The rounding core is correct** (no flushing): for a nonzero exact value `w` and any cut `c`
that agrees with it on the grids from `2^(q0 - 1)` up (`q0 = exp + bitLen sig - p`, the exponent
at which the significand has `p` bits), `roundCore f rm false w` meets `RoundSpec f rm c`. -/
theorem roundCore_correct (f : Format) (hf : f.WF) (rm : RoundingMode) (w : Exact) (hw : w.sig ≠ 0)
    (c : Cut) (hc : c.Valid)
    (hag : CutAgree c w.toRat (w.exp + bitLen w.sig - ((f.fracBits + 1 : Nat) : Int) - 1)) :
    f.RoundSpec rm c (f.roundCore rm false w) := by
  have hs : 0 < w.sig := Nat.pos_of_ne_zero hw
  have hp := f.prec_ge hf
  simp only [Format.prec] at hp
  have hqq : f.qMin + 1 ≤ f.qMax := by
    have := f.bias_pos hf; simp only [Format.qMin, Format.qMax]; omega
  generalize hq0 : w.exp + (bitLen w.sig : Int) - ((f.fracBits + 1 : Nat) : Int) = q0 at hag
  have htiny := tiny_iff f hf rm w hs c hc q0 hq0.symm hag
  obtain ⟨hMpos, hc', hag', hv⟩ := pos_setup w hs hc hag
  simp only [Format.roundCore, hw, ite_false, Bool.false_and, Bool.false_eq_true]
  rw [hq0]
  obtain ⟨q, hqd, hq1, hq2, hq3, hq4⟩ : ∃ q, (if q0 < f.qMin then f.qMin else q0) = q ∧ q0 ≤ q ∧
      f.qMin ≤ q ∧ (q0 < f.qMin → q = f.qMin) ∧ (¬ q0 < f.qMin → q = q0) :=
    ⟨_, rfl, by split <;> omega, by split <;> omega, fun h => by simp [h], fun h => by simp [h]⟩
  rw [hqd]
  obtain ⟨hM, hNlt, hNge, hNsig⟩ :=
    scaled_facts w.sig hs w.exp q (f.fracBits + 1) (by omega) (by omega)
  have hj := roundShift_spec rm w.sign (w.sig * 2 ^ (w.exp - q).toNat) (q - w.exp).toNat
  generalize (q - w.exp).toNat = k at *
  generalize w.sig * 2 ^ (w.exp - q).toNat = N at *
  generalize hjd : roundShift rm w.sign N k = j at hj ⊢
  have hP : 0 < 2 ^ k := Nat.two_pow_pos k
  have hjp : j ≤ 2 ^ (f.fracBits + 1) := hj.le_of_lt hP hNlt
  have hjq : f.qMin < q → 2 ^ f.fracBits ≤ j := fun h => by
    have hqe : q = q0 := hq4 (fun h' => by have := hq3 h'; omega)
    have := hj.ge_of_le hP (hNge (by rw [hq0]; exact hqe))
    simpa using this
  have hex := hj.exact hP
  rw [dirOf_sign] at hj
  -- the grid at `q`, with `L = 0` when `q` is clamped to the denormalized exponent
  have hi0 : (if q0 < f.qMin then (0 : Int) else 2 ^ (f.prec - 1)) = 2 ^ (f.prec - 1) ∨
      ((if q0 < f.qMin then (0 : Int) else 2 ^ (f.prec - 1)) = 0 ∧ q = f.ulpMin) := by
    rw [f.ulpMin_eq]; split
    · rename_i h; exact .inr ⟨rfl, hq3 h⟩
    · exact .inl rfl
  have G := f.gridHyp_unbounded hf (q := q) (by rw [f.ulpMin_eq]; omega) _ hi0
  have hL : (if w.sign then c.neg else c).le
      (((2 * (if q0 < f.qMin then (0 : Int) else 2 ^ (f.prec - 1)) : Int) : Rat) * (2 : Rat) ^ (q - 1)) := by
    by_cases h : q0 < f.qMin
    · rw [ite_pos' h]; simpa using (hag'.zero hMpos).2
    · rw [ite_neg' h]
      have hqe : q = q0 := hq4 h
      rw [(hag' _ (q - 1) (by omega)).1, half_le_iff hM]
      have := hNge (by rw [hq0]; exact hqe)
      have : ((2 ^ (f.fracBits + 1 - 1) * 2 ^ k : Nat) : Int) = (2 : Int) ^ (f.prec - 1) * 2 ^ k := by
        rw [Int.natCast_mul, int_two_pow, int_two_pow]; rfl
      rw [Int.mul_assoc]; omega
  have hcr := pos_correct G hc' hag' hq1 hM hMpos hL hj hjp
  have hsym := signed_cr f.unbounded_neg f.unboundedEven_neg w.sign hcr
  rw [← half_grid, Rat.intCast_natCast] at hsym
  have hsign : c.ge 0 ↔ w.sign = true := by
    have h0 := (hag 0 (q0 - 1) (Int.le_refl _)).2
    simp only [Rat.intCast_zero, Rat.zero_mul] at h0
    rw [h0, hv]
    cases w.sign <;> simp <;> grind
  refine assemble f hf rm w.sign c j q _ _ _
    (q0 < f.qMin ∧ ¬ (q0 + 1 = f.qMin ∧ roundShift rm w.sign w.sig (q0 - w.exp).toNat = 2 ^ (f.fracBits + 1)))
    hsym hsign ?_ (tinyB_iff _ _ _ _) ?_ ?_ hjp hq2 hjq htiny.symm
  · -- inexact
    have hr : (if w.sign then -((j : Rat) * (2 : Rat) ^ q) else (j : Rat) * (2 : Rat) ^ q) =
        (((if w.sign then -(2 * (j : Int)) else 2 * (j : Int)) : Int) : Rat) * (2 : Rat) ^ (q - 1) :=
      signed_half _ _ _
    rw [hr, hag.point _ _ (by omega), ← hr, hv]
    have e1 : ((j : Rat) * (2 : Rat) ^ q = (w.sig : Rat) * (2 : Rat) ^ w.exp) ↔ j * 2 ^ k = N := by
      rw [← rat_mul_eq_iff (rat_pow_pos k), hM, Rat.mul_assoc, Rat.mul_comm ((2 : Rat) ^ q),
        ← Rat.mul_assoc, rat_mul_eq_iff (rat_two_zpow_pos q), two_pow_nat, ← Rat.natCast_mul]
      exact Rat.natCast_inj
    have e2 : (if w.sign then -((j : Rat) * (2 : Rat) ^ q) else (j : Rat) * (2 : Rat) ^ q) =
        (if w.sign then -((w.sig : Rat) * (2 : Rat) ^ w.exp) else (w.sig : Rat) * (2 : Rat) ^ w.exp) ↔
        (j : Rat) * (2 : Rat) ^ q = (w.sig : Rat) * (2 : Rat) ^ w.exp := by
      cases w.sign <;> simp <;> grind
    rw [e2, e1, hex]
    rcases hNsig with h | h
    · subst h; simp
    · subst h; simp [Nat.mod_one]
  · -- no tininess with overflow
    intro hov hT
    exact absurd hT.1 (fun h => by have := hq3 h; omega)
  · cases rm
    · exact f.overflow_bits .RN w.sign
    · exact f.overflow_bits .RZ w.sign
    · exact f.overflow_bits .RP w.sign
    · exact f.overflow_bits .RM w.sign

end Mips.Fp
