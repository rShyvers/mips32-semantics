import Semantics.FpOpsCorrectArith

/-!
# FpOpsCorrectWord — float to fixed point: `CVT`/`ROUND`/`TRUNC`/`CEIL`/`FLOOR` `.W.fmt` and `.L.fmt`

`roundToInt rm v` is `v` correctly rounded to the integers in direction `rm` (ties to even), and
`Exact.isIntegral` says exactly whether that is exact. Hence `Format.toFixed w` meets
`Format.ToFixedSpec w` for every positive width (`toFixed_spec`), in particular `toW32` meets
`ToWordSpec` and `toW64` meets `ToLongSpec` (the definitions' citations are in `FpOpsSpec.lean`),
for every operand and direction.
-/

namespace Mips.Fp

/-! ## Correct rounding of a value that is in the set -/

/-- A member of `S` rounds to itself. -/
theorem cr_of_mem {S E : Rat → Prop} {rm : RoundingMode} {x : Rat} (hx : S x) :
    CorrectlyRounded S E rm (Cut.ofRat x) x := by
  have rd : RoundDown S (Cut.ofRat x) x := ⟨hx, Rat.le_refl, fun _ _ h => h⟩
  have ru : RoundUp S (Cut.ofRat x) x := ⟨hx, Rat.le_refl, fun _ _ h => h⟩
  cases rm
  · refine ⟨hx, fun y _ hy => ?_, fun y _ hy => ?_, fun y _ hne h1 h2 => ?_⟩
    · show (y + x) / 2 ≤ x; grind
    · show x ≤ (x + y) / 2; grind
    · exact absurd (by simp only [Cut.ofRat] at h1 h2; grind : y = x) hne
  · exact ⟨fun _ => rd, fun _ => ru⟩
  · exact ru
  · exact rd

/-- The correctly rounded value of a member of `S` is that member. -/
theorem cr_self {S E : Rat → Prop} {rm : RoundingMode} {x r : Rat} (hx : S x)
    (h : CorrectlyRounded S E rm (Cut.ofRat x) r) : r = x := by
  cases rm
  · obtain ⟨-, h2, h3, -⟩ := h
    rcases rat_trichotomy x r with hl | he | hg
    · have := h2 x hx hl; simp only [Cut.ofRat] at this; grind
    · exact he.symm
    · have := h3 x hx hg; simp only [Cut.ofRat] at this; grind
  · rcases (Rat.le_total : (0 : Rat) ≤ x ∨ x ≤ 0) with h0 | h0
    · obtain ⟨-, h2, h3⟩ := h.1 h0; exact Rat.le_antisymm h2 (h3 x hx Rat.le_refl)
    · obtain ⟨-, h2, h3⟩ := h.2 h0; exact Rat.le_antisymm (h3 x hx Rat.le_refl) h2
  · obtain ⟨-, h2, h3⟩ := h; exact Rat.le_antisymm (h3 x hx Rat.le_refl) h2
  · obtain ⟨-, h2, h3⟩ := h; exact Rat.le_antisymm h2 (h3 x hx Rat.le_refl)

/-! ## The integers as a grid of half unit `1/2` -/

theorem half_eq : ((2 : Rat) ^ ((0 : Int) - 1)) * 2 = 1 := by
  rw [show ((0 : Int) - 1) = -1 by rfl, Rat.zpow_neg, Rat.zpow_one]
  exact Rat.inv_mul_cancel 2 (by decide)

theorem two_mul_half (j : Int) : ((2 * j : Int) : Rat) * (2 : Rat) ^ ((0 : Int) - 1) = j := by
  have := half_eq; push_cast; grind

theorem isInt_neg (y : Rat) : IsInt (-y) ↔ IsInt y := by
  constructor <;> rintro ⟨i, hi⟩ <;> exact ⟨-i, by push_cast; grind⟩

theorem isEvenInt_neg (y : Rat) : IsEvenInt (-y) ↔ IsEvenInt y := by
  constructor <;> rintro ⟨i, hi⟩ <;> exact ⟨-i, by push_cast; grind⟩

theorem gridHyp_int (p : Nat) (hp : 1 ≤ p) :
    GridHyp IsInt IsEvenInt p ((2 : Rat) ^ ((0 : Int) - 1)) 0 where
  h_pos := rat_two_zpow_pos _
  p_pos := hp
  L_grid := ⟨0, Int.le_refl _, by have := Nat.two_pow_pos p; have := int_two_pow p; omega, by simp⟩
  S_grid := fun j _ _ => ⟨j, two_mul_half j⟩
  S_off := fun y ⟨i, hi⟩ => .inl ⟨i, by rw [two_mul_half]; exact hi⟩
  E_grid := fun j _ _ hj => ⟨j / 2, by
    have h2 : (j : Rat) = ((2 * (j / 2) : Int) : Rat) := by congr 1; omega
    rw [two_mul_half, h2]; push_cast; rfl⟩
  E_off := fun y ⟨i, hi⟩ => .inl ⟨i, by
    rw [show (4 * i : Int) = 2 * (2 * i) by omega, two_mul_half]; push_cast; exact hi⟩

/-- **Positive rational `N / 2^k` rounded to an integer in direction `rm`** by `roundShift`. -/
theorem roundShift_cr (rm : RoundingMode) (N k : Nat) (hN : 0 < N) :
    CorrectlyRounded IsInt IsEvenInt rm (Cut.ofRat ((N : Rat) / (2 : Rat) ^ k))
      ((roundShift rm false N k : Nat) : Rat) := by
  have hj := roundShift_spec rm false N k
  generalize roundShift rm false N k = j at hj
  have hM : ((N : Rat) / (2 : Rat) ^ k) * (2 : Rat) ^ k = (N : Rat) * (2 : Rat) ^ (0 : Int) := by
    have : (0 : Rat) < (2 : Rat) ^ k := Rat.pow_pos (by decide)
    rw [Rat.zpow_zero, Rat.mul_one, Rat.div_mul_cancel (by grind)]
  have hc := cutRound_ofRat hM hj
  have hpos : (0 : Rat) < (N : Rat) / (2 : Rat) ^ k := by
    rw [Rat.lt_div_iff (Rat.pow_pos (by decide)), Rat.zero_mul]; exact_mod_cast hN
  have := grid_correct (gridHyp_int (j + 1) (by omega)) (Cut.ofRat_valid _)
    (by simp only [Cut.ofRat]; grind) (by simp only [Cut.ofRat]; grind) (rm := rm) hc
    (by omega) (by have := Nat.lt_two_pow_self (n := j + 1); have := int_two_pow (j + 1); omega)
  rwa [two_mul_half] at this

theorem toRat_neg_exp (v : Exact) (k : Nat) (hk : v.exp = Int.negSucc k) :
    v.toRat = (if v.sign then -1 else 1) * ((v.sig : Rat) / (2 : Rat) ^ (k + 1)) := by
  simp only [Exact.toRat, hk, Int.negSucc_eq]
  rw [show -((k : Int) + 1) = -((k + 1 : Nat) : Int) by push_cast; rfl, Rat.zpow_neg, Rat.zpow_natCast,
    Rat.div_def]
  grind

theorem toRat_pos_exp (v : Exact) (e : Nat) (hv : v.exp = Int.ofNat e) :
    v.toRat = (((if v.sign = true then -((v.sig * 2 ^ e : Nat) : Int) else ((v.sig * 2 ^ e : Nat) : Int)) : Int) : Rat) := by
  have h2 : (2 : Rat) ^ v.exp = ((2 ^ e : Nat) : Rat) := by
    rw [hv, Int.ofNat_eq_natCast, Rat.zpow_natCast]; push_cast; rfl
  cases hs : v.sign <;> simp only [Exact.toRat, hs, h2, Bool.false_eq_true, ite_false, ite_true] <;>
    push_cast [Rat.intCast_natCast] <;> grind

/-- **`roundToInt` is correct rounding to the integers** (Table 6.10, MD00082 p.95, over the
integers; ties to even). -/
theorem roundToInt_cr (rm : RoundingMode) (v : Exact) :
    CorrectlyRounded IsInt IsEvenInt rm (Cut.ofRat v.toRat) (roundToInt rm v : Rat) := by
  unfold roundToInt
  rcases hv : v.exp with e | k
  · dsimp only
    rw [toRat_pos_exp v e hv]; exact cr_of_mem ⟨_, rfl⟩
  · dsimp only
    rw [toRat_neg_exp v k hv]
    by_cases hN : v.sig = 0
    · have : roundShift rm v.sign 0 (k + 1) = 0 := by
        simp [roundShift]; cases rm <;> simp
      simp only [hN, this]
      rw [show (if v.sign = true then (-1 : Rat) else 1) * (((0 : Nat) : Rat) / (2 : Rat) ^ (k + 1)) = ((0 : Int) : Rat) by
        rw [Rat.div_def]; simp]
      rw [show (((if v.sign = true then -((0 : Nat) : Int) else ((0 : Nat) : Int)) : Int) : Rat) = ((0 : Int) : Rat) by
        split <;> rfl]
      exact cr_of_mem ⟨0, rfl⟩
    · cases hs : v.sign
      · simp only [Bool.false_eq_true, ite_false, Rat.one_mul]
        push_cast; exact roundShift_cr rm _ _ (Nat.pos_of_ne_zero hN)
      · simp only [ite_true]
        have h := roundShift_cr rm.flip v.sig (k + 1) (Nat.pos_of_ne_zero hN)
        have h' := correctlyRounded_neg isInt_neg isEvenInt_neg h
        have hn : (Cut.ofRat ((v.sig : Rat) / (2 : Rat) ^ (k + 1))).neg = Cut.ofRat (-((v.sig : Rat) / (2 : Rat) ^ (k + 1))) := by
          simp only [Cut.neg, Cut.ofRat]
          congr 1 <;> funext y <;> apply propext <;> constructor <;> intro h <;> grind
        rw [RoundingMode.flip_flip, hn] at h'
        have e1 : roundShift rm true v.sig (k + 1) = roundShift rm.flip false v.sig (k + 1) := by
          cases rm <;> rfl
        rw [e1]; push_cast; rw [show (-1 : Rat) * ((v.sig : Rat) / (2 : Rat) ^ (k + 1)) =
          -((v.sig : Rat) / (2 : Rat) ^ (k + 1)) by grind]; exact h'

/-- `isIntegral` says exactly whether the rounding to an integer is exact. -/
theorem isIntegral_iff (rm : RoundingMode) (v : Exact) :
    v.isIntegral = true ↔ (roundToInt rm v : Rat) = v.toRat := by
  unfold roundToInt Exact.isIntegral
  rcases hv : v.exp with e | k
  · simp only [true_iff]; rw [toRat_pos_exp v e hv]
  · rw [toRat_neg_exp v k hv]
    simp only [beq_iff_eq]
    have hj := roundShift_spec rm v.sign v.sig (k + 1)
    have hP : 0 < 2 ^ (k + 1) := Nat.two_pow_pos _
    rw [← hj.exact hP]
    generalize roundShift rm v.sign v.sig (k + 1) = j
    have hp : (0 : Rat) < (2 : Rat) ^ (k + 1) := Rat.pow_pos (by decide)
    have key : ((j : Rat) = (v.sig : Rat) / (2 : Rat) ^ (k + 1)) ↔ j * 2 ^ (k + 1) = v.sig := by
      have hne : (2 : Rat) ^ (k + 1) ≠ 0 := by grind
      constructor
      · intro h
        have : (j : Rat) * (2 : Rat) ^ (k + 1) = v.sig := by rw [h, Rat.div_mul_cancel hne]
        exact_mod_cast (show ((j * 2 ^ (k + 1) : Nat) : Rat) = v.sig by push_cast; exact this)
      · intro h; rw [← h]; push_cast; rw [Rat.mul_div_cancel hne]
    cases v.sign <;> simp only [Bool.false_eq_true, ite_false, ite_true, Rat.one_mul] <;> push_cast
    · exact key.symm
    · rw [show (-1 : Rat) * ((v.sig : Rat) / (2 : Rat) ^ (k + 1)) = -((v.sig : Rat) / (2 : Rat) ^ (k + 1)) by grind,
        show ∀ a b : Rat, (-a = -b ↔ a = b) from fun a b => by constructor <;> intro h <;> grind]
      exact key.symm

namespace Format

variable (f : Format)

theorem fixedMin_eq {w : Nat} (hw : 0 < w) : fixedMin w = BitVec.ofInt w (-2 ^ (w - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  apply BitVec.eq_of_toNat_eq
  simp only [fixedMin, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Nat.add_sub_cancel]
  have h2 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  rw [Nat.mod_eq_of_lt h2]
  have hp : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  have e : ((2 ^ (k + 1) : Nat) : Int) = 2 * (2 : Int) ^ k := by
    push_cast; rw [Int.pow_succ]; omega
  have key : (-(2 : Int) ^ k) % (2 * 2 ^ k) = 2 ^ k := by
    rw [show (-(2 : Int) ^ k) = 2 ^ k + (-1) * (2 * 2 ^ k) by omega, Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt (by omega) (by omega)]
  have hc : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by push_cast; rfl
  rw [e, key, ← hc, Int.toNat_natCast]

theorem fixedMax_eq (w : Nat) : fixedMax w = BitVec.ofInt w (2 ^ (w - 1) - 1) := by
  have h1 : 1 ≤ 2 ^ (w - 1) := Nat.one_le_two_pow
  have : ((2 : Int) ^ (w - 1) - 1) = ((2 ^ (w - 1) - 1 : Nat) : Int) := by push_cast [h1]; rfl
  rw [this, BitVec.ofInt_natCast]; rfl

/-- **Float to fixed point meets `ToFixedSpec`** for every `width`-bit operand, every direction and
every positive width `w` (32: `ToWordSpec`, 64: `ToLongSpec`). -/
theorem toFixed_spec (hf : f.WF) {w : Nat} (hw : 0 < w) (rm : RoundingMode) {a : Nat}
    (ha : a < 2 ^ f.width) : f.ToFixedSpec w rm a (f.toFixed w rm a) := by
  have hP : ((2 ^ (w - 1) : Nat) : Int) = (2 : Int) ^ (w - 1) := by push_cast; rfl
  have h1 : 1 ≤ 2 ^ (w - 1) := Nat.one_le_two_pow
  have hP1 : ((2 ^ (w - 1) - 1 : Nat) : Int) = (2 : Int) ^ (w - 1) - 1 := by push_cast [h1]; rfl
  rcases f.classify hf a ha with ⟨na, -, da⟩ | ⟨na, ia, -, da⟩ | ⟨na, ia, -, da, -, -⟩
  · simp [ToFixedSpec, da, toFixed, na, flags_invalidOnly]
  · simp [ToFixedSpec, da, toFixed, na, ia, flags_invalidOnly, fixedMin_eq hw, fixedMax_eq w]
  · simp only [ToFixedSpec, da, toFixed, na, ia, Bool.false_eq_true, ite_false, hP, hP1]
    refine ⟨_, roundToInt_cr rm (f.toExact a), fun hr => ?_, fun hr => ?_, fun hr => ?_⟩
    · have hn1 : ¬ roundToInt rm (f.toExact a) < -2 ^ (w - 1) := by omega
      have hn2 : ¬ 2 ^ (w - 1) - 1 < roundToInt rm (f.toExact a) := by omega
      simp only [hn1, hn2, ite_false]
      refine ⟨BitVec.toInt_ofInt_eq_self hw (by omega) (by omega), ?_⟩
      by_cases hi : (f.toExact a).isIntegral = true
      · simp [hi, (isIntegral_iff rm _).1 hi, flags_none]
      · have : ¬ ((roundToInt rm (f.toExact a) : Rat) = (f.toExact a).toRat) :=
          fun h => hi ((isIntegral_iff rm _).2 h)
        simp [hi, this, Flags.inexactOnly]
    · simp [hr, flags_invalidOnly, fixedMin_eq hw]
    · have hn1 : ¬ roundToInt rm (f.toExact a) < -2 ^ (w - 1) := by
        have : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide)
        omega
      simp [hn1, hr, flags_invalidOnly, fixedMax_eq w]

/-- **Float to word meets `ToWordSpec`** for every `width`-bit operand and every direction. -/
theorem toW32_spec (hf : f.WF) (rm : RoundingMode) {a : Nat} (ha : a < 2 ^ f.width) :
    f.ToWordSpec rm a (f.toW32 rm a) :=
  f.toFixed_spec hf (by decide) rm ha

/-- **Float to longword meets `ToLongSpec`** for every `width`-bit operand and every direction. -/
theorem toW64_spec (hf : f.WF) (rm : RoundingMode) {a : Nat} (ha : a < 2 ^ f.width) :
    f.ToLongSpec rm a (f.toW64 rm a) :=
  f.toFixed_spec hf (by decide) rm ha

end Format

end Mips.Fp
