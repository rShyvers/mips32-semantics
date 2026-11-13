import Semantics.FpOps

/-!
# FpCompareFacts — what the FP comparison relation and the `C.cond.fmt` predicates mean

`Semantics/Specs/FpuCompare.lean` says `c.cond.s`/`c.cond.d` write
`(f32Compare cond fs ft).1` / `(f64Compare …).1` to a condition code. This file pins down what
that Boolean is, for **all** operands (no sample points):

(definitions in `Semantics/FpOps.lean` §8)

* `F32Unordered a b` — at least one operand is a NaN;
* `F32Eq a b` — neither is a NaN, and the bit patterns are equal or both are zeros (`−0 = +0`);
* `F32Lt a b` — neither is a NaN, and `a` is below `b` in the IEEE order, written out on the
  sign / biased-exponent / fraction fields: a negative is below a non-negative unless both are
  zeros; two non-negatives compare by `(exponent, fraction)` lexicographically; two negatives the
  other way round. (±∞ are covered: their exponent field is the largest.)

and likewise `F64Unordered`/`F64Eq`/`F64Lt`. Then `f32Relation_*_iff` identify the three
components of `f32Relation` with these, and `f32Compare_*` give each named predicate
(`Cond.eq`, `Cond.olt`, `Cond.lt`, …) in those terms; the signaling predicates return the same
bit as their quiet twins (they differ only in raising Invalid Operation on a quiet NaN:
`fpCompareInvalid`).

Not proved here: that the field order above coincides with the order of the *rational values*
`(-1)^sign × sig × 2^exp` of `toExact32`/`toExact64` (true for IEEE encodings; the model's
comparison is defined on the fields via `Format.orderKey`, and is tested against the host's
floating point in `Semantics/Tests/FpOpsTests.lean`).
-/

namespace Mips.Fp

/-! ## Generic: the three components of `Format.relation` -/

theorem Format.relation_unordered (f : Format) (a b : Nat) :
    (f.relation a b).unordered = (f.isNaN a || f.isNaN b) := by
  unfold Format.relation
  by_cases h : (f.isNaN a || f.isNaN b) = true
  · simp [h]
  · simp [h]

theorem Format.relation_less (f : Format) (a b : Nat) :
    (f.relation a b).less =
      (!(f.isNaN a || f.isNaN b) && decide (f.orderKey a < f.orderKey b)) := by
  unfold Format.relation
  by_cases h : (f.isNaN a || f.isNaN b) = true
  · simp [h]
  · simp [h]

theorem Format.relation_equal (f : Format) (a b : Nat) :
    (f.relation a b).equal =
      (!(f.isNaN a || f.isNaN b) && decide (f.orderKey a = f.orderKey b)) := by
  unfold Format.relation
  by_cases h : (f.isNaN a || f.isNaN b) = true
  · simp [h]
  · simp [h]

/-! ## Single precision -/

/-- The sign-magnitude key order is the field order (arithmetic core, binary32). -/
theorem orderKey32_lt_iff (a b : BitVec 32) :
    binary32.orderKey a.toNat < binary32.orderKey b.toNat ↔
      ((sign32 a = true ∧ sign32 b = false ∧ ¬(isZero32 a = true ∧ isZero32 b = true)) ∨
       (sign32 a = false ∧ sign32 b = false ∧ F32MagLt a b) ∨
       (sign32 a = true ∧ sign32 b = true ∧ F32MagLt b a)) := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [Format.orderKey, sign32, isZero32, F32MagLt, expField32, fracField32, Format.signBit,
    Format.isZero, Format.expField, Format.fracField, binary32, Nat.reduceAdd, Nat.reducePow,
    beq_iff_eq, Bool.and_eq_true, beq_eq_false_iff_ne, ne_eq]
  generalize a.toNat = x at *
  generalize b.toNat = y at *
  split <;> split <;> omega

/-- Equal keys: same bit pattern or two zeros (arithmetic core, binary32). -/
theorem orderKey32_eq_iff (a b : BitVec 32) :
    binary32.orderKey a.toNat = binary32.orderKey b.toNat ↔
      (a = b ∨ (isZero32 a = true ∧ isZero32 b = true)) := by
  have ha := a.isLt
  have hb := b.isLt
  rw [← BitVec.toNat_inj]
  simp only [Format.orderKey, isZero32, Format.signBit,
    Format.isZero, Format.expField, Format.fracField, binary32, Nat.reduceAdd, Nat.reducePow,
    beq_iff_eq, Bool.and_eq_true]
  generalize a.toNat = x at *
  generalize b.toNat = y at *
  split <;> split <;> omega

theorem f32Relation_unordered_iff (a b : BitVec 32) :
    (f32Relation a b).unordered = true ↔ F32Unordered a b := by
  simp [f32Relation, Format.relation_unordered, F32Unordered, isNaN32]

/-- **`less` of two singles is IEEE "less than"**, for all operands. -/
theorem f32Relation_less_iff (a b : BitVec 32) :
    (f32Relation a b).less = true ↔ F32Lt a b := by
  unfold F32Lt
  rw [← orderKey32_lt_iff]
  simp [f32Relation, Format.relation_less, isNaN32, and_assoc]

/-- **`equal` of two singles is IEEE "equal"** (same pattern, or `±0` with `±0`), for all
operands. -/
theorem f32Relation_equal_iff (a b : BitVec 32) :
    (f32Relation a b).equal = true ↔ F32Eq a b := by
  unfold F32Eq
  rw [← orderKey32_eq_iff]
  simp [f32Relation, Format.relation_equal, isNaN32, and_assoc]

/-- With no NaN operand the relation is ordered. -/
theorem f32Relation_ordered (a b : BitVec 32) (ha : isNaN32 a = false) (hb : isNaN32 b = false) :
    (f32Relation a b).unordered = false := by
  simp only [isNaN32] at ha hb
  simp [f32Relation, Format.relation_unordered, ha, hb]

/-! ## Double precision -/

/-- The sign-magnitude key order is the field order (arithmetic core, binary64). -/
theorem orderKey64_lt_iff (a b : BitVec 64) :
    binary64.orderKey a.toNat < binary64.orderKey b.toNat ↔
      ((sign64 a = true ∧ sign64 b = false ∧ ¬(isZero64 a = true ∧ isZero64 b = true)) ∨
       (sign64 a = false ∧ sign64 b = false ∧ F64MagLt a b) ∨
       (sign64 a = true ∧ sign64 b = true ∧ F64MagLt b a)) := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [Format.orderKey, sign64, isZero64, F64MagLt, expField64, fracField64, Format.signBit,
    Format.isZero, Format.expField, Format.fracField, binary64, Nat.reduceAdd, Nat.reducePow,
    beq_iff_eq, Bool.and_eq_true, beq_eq_false_iff_ne, ne_eq]
  generalize a.toNat = x at *
  generalize b.toNat = y at *
  split <;> split <;> omega

/-- Equal keys: same bit pattern or two zeros (arithmetic core, binary64). -/
theorem orderKey64_eq_iff (a b : BitVec 64) :
    binary64.orderKey a.toNat = binary64.orderKey b.toNat ↔
      (a = b ∨ (isZero64 a = true ∧ isZero64 b = true)) := by
  have ha := a.isLt
  have hb := b.isLt
  rw [← BitVec.toNat_inj]
  simp only [Format.orderKey, isZero64, Format.signBit,
    Format.isZero, Format.expField, Format.fracField, binary64, Nat.reduceAdd, Nat.reducePow,
    beq_iff_eq, Bool.and_eq_true]
  generalize a.toNat = x at *
  generalize b.toNat = y at *
  split <;> split <;> omega

theorem f64Relation_unordered_iff (a b : BitVec 64) :
    (f64Relation a b).unordered = true ↔ F64Unordered a b := by
  simp [f64Relation, Format.relation_unordered, F64Unordered, isNaN64]

/-- **`less` of two doubles is IEEE "less than"**, for all operands. -/
theorem f64Relation_less_iff (a b : BitVec 64) :
    (f64Relation a b).less = true ↔ F64Lt a b := by
  unfold F64Lt
  rw [← orderKey64_lt_iff]
  simp [f64Relation, Format.relation_less, isNaN64, and_assoc]

/-- **`equal` of two doubles is IEEE "equal"**, for all operands. -/
theorem f64Relation_equal_iff (a b : BitVec 64) :
    (f64Relation a b).equal = true ↔ F64Eq a b := by
  unfold F64Eq
  rw [← orderKey64_eq_iff]
  simp [f64Relation, Format.relation_equal, isNaN64, and_assoc]

/-- With no NaN operand the relation is ordered. -/
theorem f64Relation_ordered (a b : BitVec 64) (ha : isNaN64 a = false) (hb : isNaN64 b = false) :
    (f64Relation a b).unordered = false := by
  simp only [isNaN64] at ha hb
  simp [f64Relation, Format.relation_unordered, ha, hb]

/-! ## The sixteen predicates

`fpCompare cond unordered less equal` for each named `cond`. The signaling predicates
(`sf ngle seq ngl lt nge le ngt`) give the same bit as `f un eq ueq olt ult ole ule`. -/

/-- The predicate table of `C.cond.fmt`, one line per name. -/
theorem fpCompare_named (u l e : Bool) :
    fpCompare Cond.f u l e = false ∧ fpCompare Cond.sf u l e = false ∧
    fpCompare Cond.un u l e = u ∧ fpCompare Cond.ngle u l e = u ∧
    fpCompare Cond.eq u l e = e ∧ fpCompare Cond.seq u l e = e ∧
    fpCompare Cond.ueq u l e = (u || e) ∧ fpCompare Cond.ngl u l e = (u || e) ∧
    fpCompare Cond.olt u l e = l ∧ fpCompare Cond.lt u l e = l ∧
    fpCompare Cond.ult u l e = (u || l) ∧ fpCompare Cond.nge u l e = (u || l) ∧
    fpCompare Cond.ole u l e = (e || l) ∧ fpCompare Cond.le u l e = (e || l) ∧
    fpCompare Cond.ule u l e = (u || e || l) ∧ fpCompare Cond.ngt u l e = (u || e || l) := by
  cases u <;> cases l <;> cases e <;> decide

/-- A signaling predicate (`cond + 8`) returns the same bit as its quiet twin. -/
theorem fpCompare_signaling_twin (c : BitVec 4) (u l e : Bool) :
    fpCompare (c ||| 8#4) u l e = fpCompare c u l e := by
  revert c u l e; decide

/-- The result bit of `C.cond.S` is the predicate applied to the relation. -/
theorem f32Compare_fst (cond : BitVec 4) (a b : BitVec 32) :
    (f32Compare cond a b).1 =
      fpCompare cond (f32Relation a b).unordered (f32Relation a b).less (f32Relation a b).equal := rfl

/-- The result bit of `C.cond.D` is the predicate applied to the relation. -/
theorem f64Compare_fst (cond : BitVec 4) (a b : BitVec 64) :
    (f64Compare cond a b).1 =
      fpCompare cond (f64Relation a b).unordered (f64Relation a b).less (f64Relation a b).equal := rfl

/-! ### Single precision, by name -/

/-- **`c.eq.s` / `c.seq.s`: true iff the operands are equal and neither is a NaN.** -/
theorem f32Compare_eq (a b : BitVec 32) :
    ((f32Compare Cond.eq a b).1 = true ↔ F32Eq a b) ∧
    ((f32Compare Cond.seq a b).1 = true ↔ F32Eq a b) := by
  rw [f32Compare_fst, f32Compare_fst, (fpCompare_named _ _ _).2.2.2.2.1,
    (fpCompare_named _ _ _).2.2.2.2.2.1]
  exact ⟨f32Relation_equal_iff a b, f32Relation_equal_iff a b⟩

/-- **`c.olt.s` / `c.lt.s`: true iff `a < b` and neither is a NaN.** -/
theorem f32Compare_lt (a b : BitVec 32) :
    ((f32Compare Cond.olt a b).1 = true ↔ F32Lt a b) ∧
    ((f32Compare Cond.lt a b).1 = true ↔ F32Lt a b) := by
  rw [f32Compare_fst, f32Compare_fst, (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.1,
    (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.2.1]
  exact ⟨f32Relation_less_iff a b, f32Relation_less_iff a b⟩

/-- **`c.ole.s` / `c.le.s`: true iff `a ≤ b` and neither is a NaN.** -/
theorem f32Compare_le (a b : BitVec 32) :
    ((f32Compare Cond.ole a b).1 = true ↔ (F32Eq a b ∨ F32Lt a b)) ∧
    ((f32Compare Cond.le a b).1 = true ↔ (F32Eq a b ∨ F32Lt a b)) := by
  rw [f32Compare_fst, f32Compare_fst, (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.2.2.2.2.1,
    (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.2.2.2.2.2.1, Bool.or_eq_true,
    f32Relation_equal_iff, f32Relation_less_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **`c.un.s` / `c.ngle.s`: true iff an operand is a NaN.** -/
theorem f32Compare_un (a b : BitVec 32) :
    ((f32Compare Cond.un a b).1 = true ↔ F32Unordered a b) ∧
    ((f32Compare Cond.ngle a b).1 = true ↔ F32Unordered a b) := by
  rw [f32Compare_fst, f32Compare_fst, (fpCompare_named _ _ _).2.2.1,
    (fpCompare_named _ _ _).2.2.2.1]
  exact ⟨f32Relation_unordered_iff a b, f32Relation_unordered_iff a b⟩

/-- **`c.ueq.s` / `c.ngl.s`: true iff unordered or equal.** -/
theorem f32Compare_ueq (a b : BitVec 32) :
    ((f32Compare Cond.ueq a b).1 = true ↔ (F32Unordered a b ∨ F32Eq a b)) ∧
    ((f32Compare Cond.ngl a b).1 = true ↔ (F32Unordered a b ∨ F32Eq a b)) := by
  rw [f32Compare_fst, f32Compare_fst, (fpCompare_named _ _ _).2.2.2.2.2.2.1,
    (fpCompare_named _ _ _).2.2.2.2.2.2.2.1, Bool.or_eq_true,
    f32Relation_unordered_iff, f32Relation_equal_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **`c.ult.s` / `c.nge.s`: true iff unordered or `a < b`.** -/
theorem f32Compare_ult (a b : BitVec 32) :
    ((f32Compare Cond.ult a b).1 = true ↔ (F32Unordered a b ∨ F32Lt a b)) ∧
    ((f32Compare Cond.nge a b).1 = true ↔ (F32Unordered a b ∨ F32Lt a b)) := by
  rw [f32Compare_fst, f32Compare_fst, (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.2.2.1,
    (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.2.2.2.1, Bool.or_eq_true,
    f32Relation_unordered_iff, f32Relation_less_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **`c.ule.s` / `c.ngt.s`: true iff unordered or `a ≤ b`.** -/
theorem f32Compare_ule (a b : BitVec 32) :
    ((f32Compare Cond.ule a b).1 = true ↔ ((F32Unordered a b ∨ F32Eq a b) ∨ F32Lt a b)) ∧
    ((f32Compare Cond.ngt a b).1 = true ↔ ((F32Unordered a b ∨ F32Eq a b) ∨ F32Lt a b)) := by
  rw [f32Compare_fst, f32Compare_fst, (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, Bool.or_eq_true, Bool.or_eq_true,
    f32Relation_unordered_iff, f32Relation_equal_iff, f32Relation_less_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **`c.f.s` / `c.sf.s`: always false.** -/
theorem f32Compare_f (a b : BitVec 32) :
    (f32Compare Cond.f a b).1 = false ∧ (f32Compare Cond.sf a b).1 = false := by
  rw [f32Compare_fst, f32Compare_fst]
  exact ⟨(fpCompare_named _ _ _).1, (fpCompare_named _ _ _).2.1⟩

/-! ### Double precision, by name -/

/-- **`c.eq.d` / `c.seq.d`: true iff the operands are equal and neither is a NaN.** -/
theorem f64Compare_eq (a b : BitVec 64) :
    ((f64Compare Cond.eq a b).1 = true ↔ F64Eq a b) ∧
    ((f64Compare Cond.seq a b).1 = true ↔ F64Eq a b) := by
  rw [f64Compare_fst, f64Compare_fst, (fpCompare_named _ _ _).2.2.2.2.1,
    (fpCompare_named _ _ _).2.2.2.2.2.1]
  exact ⟨f64Relation_equal_iff a b, f64Relation_equal_iff a b⟩

/-- **`c.olt.d` / `c.lt.d`: true iff `a < b` and neither is a NaN.** -/
theorem f64Compare_lt (a b : BitVec 64) :
    ((f64Compare Cond.olt a b).1 = true ↔ F64Lt a b) ∧
    ((f64Compare Cond.lt a b).1 = true ↔ F64Lt a b) := by
  rw [f64Compare_fst, f64Compare_fst, (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.1,
    (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.2.1]
  exact ⟨f64Relation_less_iff a b, f64Relation_less_iff a b⟩

/-- **`c.ole.d` / `c.le.d`: true iff `a ≤ b` and neither is a NaN.** -/
theorem f64Compare_le (a b : BitVec 64) :
    ((f64Compare Cond.ole a b).1 = true ↔ (F64Eq a b ∨ F64Lt a b)) ∧
    ((f64Compare Cond.le a b).1 = true ↔ (F64Eq a b ∨ F64Lt a b)) := by
  rw [f64Compare_fst, f64Compare_fst, (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.2.2.2.2.1,
    (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.2.2.2.2.2.1, Bool.or_eq_true,
    f64Relation_equal_iff, f64Relation_less_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **`c.un.d` / `c.ngle.d`: true iff an operand is a NaN.** -/
theorem f64Compare_un (a b : BitVec 64) :
    ((f64Compare Cond.un a b).1 = true ↔ F64Unordered a b) ∧
    ((f64Compare Cond.ngle a b).1 = true ↔ F64Unordered a b) := by
  rw [f64Compare_fst, f64Compare_fst, (fpCompare_named _ _ _).2.2.1,
    (fpCompare_named _ _ _).2.2.2.1]
  exact ⟨f64Relation_unordered_iff a b, f64Relation_unordered_iff a b⟩

/-- **`c.ueq.d` / `c.ngl.d`: true iff unordered or equal.** -/
theorem f64Compare_ueq (a b : BitVec 64) :
    ((f64Compare Cond.ueq a b).1 = true ↔ (F64Unordered a b ∨ F64Eq a b)) ∧
    ((f64Compare Cond.ngl a b).1 = true ↔ (F64Unordered a b ∨ F64Eq a b)) := by
  rw [f64Compare_fst, f64Compare_fst, (fpCompare_named _ _ _).2.2.2.2.2.2.1,
    (fpCompare_named _ _ _).2.2.2.2.2.2.2.1, Bool.or_eq_true,
    f64Relation_unordered_iff, f64Relation_equal_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **`c.ult.d` / `c.nge.d`: true iff unordered or `a < b`.** -/
theorem f64Compare_ult (a b : BitVec 64) :
    ((f64Compare Cond.ult a b).1 = true ↔ (F64Unordered a b ∨ F64Lt a b)) ∧
    ((f64Compare Cond.nge a b).1 = true ↔ (F64Unordered a b ∨ F64Lt a b)) := by
  rw [f64Compare_fst, f64Compare_fst, (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.2.2.1,
    (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.2.2.2.1, Bool.or_eq_true,
    f64Relation_unordered_iff, f64Relation_less_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **`c.ule.d` / `c.ngt.d`: true iff unordered or `a ≤ b`.** -/
theorem f64Compare_ule (a b : BitVec 64) :
    ((f64Compare Cond.ule a b).1 = true ↔ ((F64Unordered a b ∨ F64Eq a b) ∨ F64Lt a b)) ∧
    ((f64Compare Cond.ngt a b).1 = true ↔ ((F64Unordered a b ∨ F64Eq a b) ∨ F64Lt a b)) := by
  rw [f64Compare_fst, f64Compare_fst, (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (fpCompare_named _ _ _).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, Bool.or_eq_true, Bool.or_eq_true,
    f64Relation_unordered_iff, f64Relation_equal_iff, f64Relation_less_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **`c.f.d` / `c.sf.d`: always false.** -/
theorem f64Compare_f (a b : BitVec 64) :
    (f64Compare Cond.f a b).1 = false ∧ (f64Compare Cond.sf a b).1 = false := by
  rw [f64Compare_fst, f64Compare_fst]
  exact ⟨(fpCompare_named _ _ _).1, (fpCompare_named _ _ _).2.1⟩

end Mips.Fp
