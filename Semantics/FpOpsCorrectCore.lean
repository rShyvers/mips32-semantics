import Semantics.FpOpsCorrectScale
import Semantics.FpOpsCorrectPack

/-!
# FpOpsCorrectCore — the rounding core is correct

The lemmas `roundCore_correct` (`FpOpsCorrectMain.lean`) is assembled from: the grid shape of the
format's sets, the positive-side rounding and its uniqueness, the sign symmetry, and the tininess
test (`tiny_iff`).
-/

namespace Mips.Fp

namespace Format

theorem prec_ge (f : Format) (hf : f.WF) : 2 ≤ f.prec := by simp only [prec]; have := hf.2; omega

theorem gridHyp_unbounded (f : Format) (hf : f.WF) {q : Int} (hq : f.ulpMin ≤ q) (i0 : Int)
    (hi0 : i0 = 2 ^ (f.prec - 1) ∨ (i0 = 0 ∧ q = f.ulpMin)) :
    GridHyp f.Unbounded f.UnboundedEven f.prec ((2 : Rat) ^ (q - 1))
      (((2 * i0 : Int) : Rat) * (2 : Rat) ^ (q - 1)) :=
  gridHyp_of (f.prec_ge hf) (fun e (h : f.ulpMin ≤ e) => show f.ulpMin ≤ e + 1 by omega)
    (fun e => show f.ulpMin + 1 ≤ e ↔ f.ulpMin ≤ e - 1 by omega) hq i0
    (hi0.imp id (fun h => ⟨h.1, fun e (he : f.ulpMin ≤ e) => by omega⟩))

theorem gridHyp_range (f : Format) (hf : f.WF) (q : Int) :
    GridHyp f.UnboundedRange f.UnboundedRangeEven f.prec ((2 : Rat) ^ (q - 1))
      (((2 * 2 ^ (f.prec - 1) : Int) : Rat) * (2 : Rat) ^ (q - 1)) :=
  gridHyp_of (P := fun _ => True) (P' := fun _ => True) (f.prec_ge hf) (fun _ _ => trivial)
    (fun _ => Iff.rfl) trivial _ (.inl rfl)

theorem unbounded_neg (f : Format) (y : Rat) : f.Unbounded (-y) ↔ f.Unbounded y := grid_neg_iff _ _ y
theorem unboundedEven_neg (f : Format) (y : Rat) : f.UnboundedEven (-y) ↔ f.UnboundedEven y :=
  grid_neg_iff _ _ y
theorem unboundedRange_neg (f : Format) (y : Rat) : f.UnboundedRange (-y) ↔ f.UnboundedRange y :=
  grid_neg_iff _ _ y
theorem unboundedRangeEven_neg (f : Format) (y : Rat) :
    f.UnboundedRangeEven (-y) ↔ f.UnboundedRangeEven y := grid_neg_iff _ _ y

end Format

/-! ## Comparing `a · 2^e1` with `b · 2^e2` -/

theorem nat_zpow_le_iff (a b : Nat) (e1 e2 : Int) :
    (a : Rat) * (2 : Rat) ^ e1 ≤ (b : Rat) * (2 : Rat) ^ e2 ↔
      a * 2 ^ (e1 - min e1 e2).toNat ≤ b * 2 ^ (e2 - min e1 e2).toNat := by
  rw [two_zpow_toNat (min e1 e2) e1 (by omega), two_zpow_toNat (min e1 e2) e2 (by omega),
    ← Rat.mul_assoc, ← Rat.mul_assoc, rat_mul_le_iff (rat_two_zpow_pos _), ← Rat.natCast_mul,
    ← Rat.natCast_mul]
  exact Rat.natCast_le_natCast

theorem nat_zpow_lt_iff (a b : Nat) (e1 e2 : Int) :
    (a : Rat) * (2 : Rat) ^ e1 < (b : Rat) * (2 : Rat) ^ e2 ↔
      a * 2 ^ (e1 - min e1 e2).toNat < b * 2 ^ (e2 - min e1 e2).toNat := by
  rw [two_zpow_toNat (min e1 e2) e1 (by omega), two_zpow_toNat (min e1 e2) e2 (by omega),
    ← Rat.mul_assoc, ← Rat.mul_assoc, rat_mul_lt_iff (rat_two_zpow_pos _), ← Rat.natCast_mul,
    ← Rat.natCast_mul]
  exact Rat.natCast_lt_natCast

/-! ## Assembly lemmas -/

theorem CutAgree.zero {c : Cut} {M : Rat} {e0 : Int} (h : CutAgree c M e0) (hM : 0 < M) :
    ¬ c.ge 0 ∧ c.le 0 := by
  have h0 := h 0 e0 (Int.le_refl _)
  simp only [Rat.intCast_zero, Rat.zero_mul] at h0
  exact ⟨fun hh => absurd (h0.2.1 hh) (Rat.not_le.mpr hM), h0.1.2 (Rat.le_of_lt hM)⟩

/-- The positive side: the core's integer `j` gives the correctly rounded value `j · 2^q`. -/
theorem pos_correct {S E : Rat → Prop} {p : Nat} {q q0 : Int} {L : Rat} {c : Cut} {M : Rat}
    {N k j : Nat} {rm : RoundingMode} (G : GridHyp S E p ((2 : Rat) ^ (q - 1)) L) (hc : c.Valid)
    (hag : CutAgree c M (q0 - 1)) (hq : q0 ≤ q) (hM : M * (2 : Rat) ^ k = (N : Rat) * (2 : Rat) ^ q)
    (hpos : 0 < M) (hL : c.le L) (hj : IntRound (dirOf rm false) N (2 ^ k) j) (hjp : j ≤ 2 ^ p) :
    CorrectlyRounded S E rm c (((2 * (j : Int) : Int) : Rat) * (2 : Rat) ^ (q - 1)) :=
  grid_correct G hc (hag.zero hpos).1 hL
    ((cutRound_agree hag (by omega) _ _).2 (cutRound_ofRat hM hj)) (by omega)
    (by have := int_two_pow p; omega)

/-- ... and it is the only one. -/
theorem pos_unique {S E : Rat → Prop} {p : Nat} {q q0 : Int} {L : Rat} {c : Cut} {M : Rat}
    {N k : Nat} {rm : RoundingMode} (G : GridHyp S E p ((2 : Rat) ^ (q - 1)) L) (hc : c.Valid)
    (hag : CutAgree c M (q0 - 1)) (hq : q0 ≤ q) (hM : M * (2 : Rat) ^ k = (N : Rat) * (2 : Rat) ^ q)
    (hpos : 0 < M) (hL : c.le L) (hN : N < 2 ^ p * 2 ^ k) {u1 u2 : Rat}
    (h1 : CorrectlyRounded S E rm c u1) (h2 : CorrectlyRounded S E rm c u2) : u1 = u2 := by
  refine grid_unique G hc (hag.zero hpos).1 hL ?_ h1 h2
  rw [(hag _ (q - 1) (by omega)).1, half_le_iff hM]
  have : ((2 ^ p * 2 ^ k : Nat) : Int) = (2 : Int) ^ p * 2 ^ k := by
    rw [Int.natCast_mul, int_two_pow, int_two_pow]
  rw [Int.mul_assoc]; omega

theorem signed_cr {S E : Rat → Prop} (hS : ∀ y, S (-y) ↔ S y) (hE : ∀ y, E (-y) ↔ E y) (s : Bool)
    {rm : RoundingMode} {c : Cut} {x : Rat}
    (h : CorrectlyRounded S E (if s then rm.flip else rm) (if s then c.neg else c) x) :
    CorrectlyRounded S E rm c (if s then -x else x) := by
  cases s
  · exact h
  · have := correctlyRounded_neg hS hE h
    simpa [RoundingMode.flip_flip, Cut.neg_neg] using this

theorem signed_cr_inv {S E : Rat → Prop} (hS : ∀ y, S (-y) ↔ S y) (hE : ∀ y, E (-y) ↔ E y) (s : Bool)
    {rm : RoundingMode} {c : Cut} {u : Rat} (h : CorrectlyRounded S E rm c u) :
    CorrectlyRounded S E (if s then rm.flip else rm) (if s then c.neg else c) (if s then -u else u) := by
  cases s
  · exact h
  · exact correctlyRounded_neg hS hE h

theorem abs_signed (s : Bool) {x : Rat} (hx : 0 ≤ x) : (if s then -x else x).abs = x := by
  cases s <;> simp only [Rat.abs] <;> split <;> grind

theorem signed_abs_eq {s : Bool} {x u : Rat} (hx : 0 ≤ x) (h : (if s then -u else u) = x) : u.abs = x := by
  cases s <;> simp only [Rat.abs] at h ⊢ <;> split <;> grind

theorem dirOf_sign (rm : RoundingMode) (s : Bool) :
    dirOf rm s = dirOf (if s then rm.flip else rm) false := by
  cases s
  · rfl
  · exact dirOf_true rm

theorem Format.emin_eq (f : Format) : f.emin = f.qMin + f.fracBits := by
  simp only [Format.emin, Format.qMin, Format.bias]; omega

/-- The positive side of a nonzero exact value: its magnitude `M`, and the cut of `|v|`. -/
theorem pos_setup (w : Exact) (hs : 0 < w.sig) {c : Cut} (hc : c.Valid) {e0 : Int}
    (hag : CutAgree c w.toRat e0) :
    0 < (w.sig : Rat) * (2 : Rat) ^ w.exp ∧ (if w.sign then c.neg else c).Valid ∧
      CutAgree (if w.sign then c.neg else c) ((w.sig : Rat) * (2 : Rat) ^ w.exp) e0 ∧
      w.toRat = (if w.sign then -((w.sig : Rat) * (2 : Rat) ^ w.exp) else (w.sig : Rat) * (2 : Rat) ^ w.exp) := by
  have hMpos : 0 < (w.sig : Rat) * (2 : Rat) ^ w.exp :=
    Rat.mul_pos (Rat.natCast_pos.2 hs) (rat_two_zpow_pos _)
  have hv : w.toRat = (if w.sign then -((w.sig : Rat) * (2 : Rat) ^ w.exp)
      else (w.sig : Rat) * (2 : Rat) ^ w.exp) := by
    simp only [Exact.toRat]; split <;> grind
  refine ⟨hMpos, ?_, ?_, hv⟩
  · split
    · exact Cut.neg_valid hc
    · exact hc
  · rw [hv] at hag
    cases hsg : w.sign <;> simp only [hsg] at hag ⊢
    · simpa using hag
    · have := hag.neg; simpa using this

/-- **Tininess after rounding** (MD00082 Vol I-A Rev 6.01 §6.7.2.3, p.101) is the core's test. -/
theorem tiny_iff (f : Format) (hf : f.WF) (rm : RoundingMode) (w : Exact) (hs : 0 < w.sig)
    (c : Cut) (hc : c.Valid) (q0 : Int) (hq0 : q0 = w.exp + bitLen w.sig - ((f.fracBits + 1 : Nat) : Int))
    (hag : CutAgree c w.toRat (q0 - 1)) :
    (∃ u : Rat, CorrectlyRounded f.UnboundedRange f.UnboundedRangeEven rm c u ∧
        u.abs < (2 : Rat) ^ f.emin) ↔
      (q0 < f.qMin ∧ ¬ (q0 + 1 = f.qMin ∧
        roundShift rm w.sign w.sig (q0 - w.exp).toNat = 2 ^ (f.fracBits + 1))) := by
  have hp := f.prec_ge hf
  simp only [Format.prec] at hp
  obtain ⟨hMpos, hc', hag', hv⟩ := pos_setup w hs hc hag
  obtain ⟨hM, hNlt, hNge, hNsig⟩ :=
    scaled_facts w.sig hs w.exp q0 (f.fracBits + 1) (by omega) (by omega)
  have hNge := hNge hq0
  have hj := roundShift_spec rm w.sign (w.sig * 2 ^ (w.exp - q0).toNat) (q0 - w.exp).toNat
  have hsN : w.sig ≤ w.sig * 2 ^ (w.exp - q0).toNat := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  generalize (q0 - w.exp).toNat = k at *
  generalize w.sig * 2 ^ (w.exp - q0).toNat = N at *
  generalize hjd : roundShift rm w.sign N k = j at hj
  have hP : 0 < 2 ^ k := Nat.two_pow_pos k
  have hjp : j ≤ 2 ^ (f.fracBits + 1) := hj.le_of_lt hP hNlt
  have hjq : 2 ^ (f.fracBits + 1 - 1) ≤ j := hj.ge_of_le hP hNge
  rw [dirOf_sign] at hj
  have G := f.gridHyp_range hf q0
  have hL : (if w.sign then c.neg else c).le
      (((2 * 2 ^ (f.prec - 1) : Int) : Rat) * (2 : Rat) ^ (q0 - 1)) := by
    rw [(hag' _ (q0 - 1) (Int.le_refl _)).1, half_le_iff hM]
    have : ((2 ^ (f.fracBits + 1 - 1) * 2 ^ k : Nat) : Int) = (2 : Int) ^ (f.prec - 1) * 2 ^ k := by
      rw [Int.natCast_mul, int_two_pow, int_two_pow]; rfl
    rw [Int.mul_assoc]; omega
  have hjp' : j ≤ 2 ^ f.prec := hjp
  have hNlt' : N < 2 ^ f.prec * 2 ^ k := hNlt
  have hcr := pos_correct G hc' hag' (Int.le_refl _) hM hMpos hL hj hjp'
  have hsym := signed_cr f.unboundedRange_neg f.unboundedRangeEven_neg w.sign hcr
  have hu0 : (0 : Rat) ≤ ((2 * (j : Int) : Int) : Rat) * (2 : Rat) ^ (q0 - 1) :=
    Rat.mul_nonneg (by push_cast; exact Rat.mul_nonneg (by decide) (Rat.natCast_nonneg))
      (Rat.le_of_lt (rat_two_zpow_pos _))
  have key : (∃ u : Rat, CorrectlyRounded f.UnboundedRange f.UnboundedRangeEven rm c u ∧
      u.abs < (2 : Rat) ^ f.emin) ↔ ((2 * (j : Int) : Int) : Rat) * (2 : Rat) ^ (q0 - 1) < (2 : Rat) ^ f.emin := by
    constructor
    · rintro ⟨u, hu, hlt⟩
      have h2 := signed_cr_inv f.unboundedRange_neg f.unboundedRangeEven_neg w.sign hu
      have := pos_unique G hc' hag' (Int.le_refl _) hM hMpos hL hNlt' h2 hcr
      rw [signed_abs_eq hu0 this] at hlt; exact hlt
    · intro h; exact ⟨_, hsym, by rw [abs_signed _ hu0]; exact h⟩
  have hrs : roundShift rm w.sign w.sig k = 2 ^ (f.fracBits + 1) ↔ j = 2 ^ (f.fracBits + 1) := by
    rcases hNsig with h | h
    · rw [← h, hjd]
    · subst h
      rw [roundShift_zero] at hjd ⊢
      have : 2 ^ (f.fracBits + 1) * 2 ^ 0 = 2 ^ (f.fracBits + 1) := by simp
      omega
  rw [key, ← half_grid, Rat.intCast_natCast, hrs,
    show (2 : Rat) ^ f.emin = ((1 : Nat) : Rat) * (2 : Rat) ^ f.emin by simp, nat_zpow_lt_iff,
    Format.emin_eq]
  have h2p : 2 ^ (f.fracBits + 1) = 2 * 2 ^ f.fracBits := Nat.pow_succ'
  have hj1 : 2 ^ (f.fracBits + 1 - 1) = 2 ^ f.fracBits := by simp
  rw [hj1] at hjq
  by_cases hA : q0 < f.qMin
  · rw [show min q0 (f.qMin + f.fracBits) = q0 by omega, show (q0 - q0).toNat = 0 by omega]
    simp only [Nat.pow_zero, Nat.mul_one, Nat.one_mul]
    by_cases hB : q0 + 1 = f.qMin
    · rw [show (f.qMin + f.fracBits - q0).toNat = f.fracBits + 1 by omega]
      constructor
      · intro h; exact ⟨hA, fun h' => by omega⟩
      · intro h; have := h.2; omega
    · have : 2 ^ (f.fracBits + 2) ≤ 2 ^ (f.qMin + f.fracBits - q0).toNat :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have : 2 ^ (f.fracBits + 2) = 2 * 2 ^ (f.fracBits + 1) := Nat.pow_succ'
      constructor
      · intro _; exact ⟨hA, fun h' => hB h'.1⟩
      · intro _; have := Nat.two_pow_pos (f.fracBits + 1); omega
  · refine ⟨fun h => absurd h ?_, fun h => absurd h.1 hA⟩
    rcases Int.le_total (f.qMin + f.fracBits) q0 with h | h
    · rw [show min q0 (f.qMin + f.fracBits) = f.qMin + f.fracBits by omega,
        show (f.qMin + f.fracBits - (f.qMin + f.fracBits)).toNat = 0 by omega]
      have : 1 ≤ 2 ^ (q0 - (f.qMin + f.fracBits)).toNat := Nat.one_le_two_pow
      have : 1 ≤ 2 ^ f.fracBits := Nat.one_le_two_pow
      have : 1 * 1 ≤ j * 2 ^ (q0 - (f.qMin + f.fracBits)).toNat := Nat.mul_le_mul (by omega) (by omega)
      simp only [Nat.pow_zero]; omega
    · rw [show min q0 (f.qMin + f.fracBits) = q0 by omega, show (q0 - q0).toNat = 0 by omega]
      have : 2 ^ (f.qMin + f.fracBits - q0).toNat ≤ 2 ^ f.fracBits :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simp only [Nat.pow_zero, Nat.mul_one, Nat.one_mul]; omega

end Mips.Fp
