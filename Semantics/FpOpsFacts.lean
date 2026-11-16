import Semantics.FpOps

/-!
# FpOpsFacts — kernel-checked facts about `Semantics/FpOps.lean`

Formerly §10 of `Semantics/FpOps.lean`; moved verbatim so that the definition file holds
definitions only. General lemmas (NaN canonicalisation, `fpUpdate`, FCSR views) used by
`Semantics/Specs/Fpu*.lean`, plus concrete-case theorems proved by `decide`/`rfl`.
-/

namespace Mips.Fp

/-! ## §10  Kernel-checked facts -/

section Theorems

/-! ### General theorems -/

/-- `canonNaN32` is the identity on non-NaNs. -/
theorem canonNaN32_of_not_nan (x : BitVec 32) (h : isNaN32 x = false) : canonNaN32 x = x := by
  simp [canonNaN32, h]

/-- `canonNaN32` sends every NaN to the default QNaN. -/
theorem canonNaN32_of_nan (x : BitVec 32) (h : isNaN32 x = true) :
    canonNaN32 x = defaultQNaN32 := by
  simp [canonNaN32, h]

/-- `canonNaN64` is the identity on non-NaNs. -/
theorem canonNaN64_of_not_nan (x : BitVec 64) (h : isNaN64 x = false) : canonNaN64 x = x := by
  simp [canonNaN64, h]

/-- `canonNaN64` sends every NaN to the default QNaN. -/
theorem canonNaN64_of_nan (x : BitVec 64) (h : isNaN64 x = true) :
    canonNaN64 x = defaultQNaN64 := by
  simp [canonNaN64, h]

/-- The default QNaNs are quiet NaNs in the IEEE 754-2008 encoding (`FCSR.NAN2008 = 1`), and fixed
points of canonicalisation. -/
theorem defaultQNaN_facts :
    isQNaN32 defaultQNaN32 = true ∧ isSNaN32 defaultQNaN32 = false ∧
    isQNaN64 defaultQNaN64 = true ∧ isSNaN64 defaultQNaN64 = false ∧
    canonNaN32 defaultQNaN32 = defaultQNaN32 ∧ canonNaN64 defaultQNaN64 = defaultQNaN64 ∧
    BitVec.ofNat 32 binary32.defaultQNaN = defaultQNaN32 ∧
    BitVec.ofNat 64 binary64.defaultQNaN = defaultQNaN64 := by decide

/-- Lean's canonical `Float32` NaN `0x7FC00000` is the default *quiet* NaN of the IEEE 754-2008
encoding (`FCSR.NAN2008 = 1`), so canonicalisation leaves it alone. -/
theorem hostNaN_is_default_quiet :
    isQNaN32 0x7FC00000#32 = true ∧ canonNaN32 0x7FC00000#32 = 0x7FC00000#32 ∧
    isQNaN64 0x7FF8000000000000#64 = true ∧
    canonNaN64 0x7FF8000000000000#64 = 0x7FF8000000000000#64 := by decide

/-- The `C.cond.fmt` formula. -/
theorem fpCompare_eq (cond : BitVec 4) (un lt eq : Bool) :
    fpCompare cond un lt eq =
      ((cond.getLsbD 0 && un) || (cond.getLsbD 1 && eq) || (cond.getLsbD 2 && lt)) := rfl

/-- A NaN is not subnormal, so `flushIn` leaves it alone. -/
theorem Format.flushIn_of_isNaN (f : Format) (fl : Bool) (n : Nat) (hm : f.expMax ≠ 0)
    (h : f.isNaN n = true) : f.flushIn fl n = n := by
  unfold Format.flushIn Format.isSubnormal
  unfold Format.isNaN at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
  simp [h.1, hm]

/-- An infinity is not subnormal, so `flushIn` leaves it alone. -/
theorem Format.flushIn_of_isInf (f : Format) (fl : Bool) (n : Nat) (hm : f.expMax ≠ 0)
    (h : f.isInf n = true) : f.flushIn fl n = n := by
  unfold Format.flushIn Format.isSubnormal
  unfold Format.isInf at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp [h.1, hm]

/-- An operand that is not subnormal adds no flag to an operation's (`Format.withFlush`). -/
theorem Format.withFlush_single_of_not_subnormal {α : Type} (f : Format) (fl : Bool) (n : Nat)
    (r : α × Flags) (h : f.isSubnormal n = false) : f.withFlush fl [n] r = r := by
  obtain ⟨x, g⟩ := r; cases g
  simp [Format.withFlush, Format.flushFlags, Flags.or, h]

/-- A NaN is not subnormal. -/
theorem Format.isSubnormal_of_isNaN (f : Format) (n : Nat) (hm : f.expMax ≠ 0)
    (h : f.isNaN n = true) : f.isSubnormal n = false := by
  unfold Format.isSubnormal
  unfold Format.isNaN at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
  simp [h.1, hm]

/-- An infinity is not subnormal. -/
theorem Format.isSubnormal_of_isInf (f : Format) (n : Nat) (hm : f.expMax ≠ 0)
    (h : f.isInf n = true) : f.isSubnormal n = false := by
  unfold Format.isSubnormal
  unfold Format.isInf at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp [h.1, hm]

private theorem isNaN_false_of_isInf (f : Format) (n : Nat) (h : f.isInf n = true) :
    f.isNaN n = false := by
  unfold Format.isInf at h; unfold Format.isNaN
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp [h.2]

/-- Float → word of any NaN, in any rounding mode: `0` and Invalid (`FCSR.NAN2008 = 1`, MD00082 Vol
I-A Rev 6.01 Table 6.3, p.82). -/
theorem f32ToW32_of_nan (rm : RoundingMode) (fl : Bool) (x : BitVec 32) (h : isNaN32 x = true) :
    f32ToW32 rm fl x = (0#32, Flags.invalidOnly) := by
  have hn : binary32.isNaN x.toNat = true := h
  unfold f32ToW32
  rw [Format.withFlush_single_of_not_subnormal binary32 fl _ _
    (Format.isSubnormal_of_isNaN binary32 _ (by decide) hn)]
  unfold Format.toW32 Format.toFixed
  rw [Format.flushIn_of_isNaN binary32 fl _ (by decide) hn]
  simp only [hn, ↓reduceIte]

/-- Float → word of `±∞`, in any rounding mode: `2^31 - 1` / `-2^31` and Invalid (Table 6.3). -/
theorem f32ToW32_of_inf (rm : RoundingMode) (fl : Bool) (x : BitVec 32) (h : isInf32 x = true) :
    f32ToW32 rm fl x = (if sign32 x then 0x80000000#32 else 0x7FFFFFFF#32, Flags.invalidOnly) := by
  have hi : binary32.isInf x.toNat = true := h
  unfold f32ToW32
  rw [Format.withFlush_single_of_not_subnormal binary32 fl _ _
    (Format.isSubnormal_of_isInf binary32 _ (by decide) hi)]
  unfold Format.toW32 Format.toFixed
  rw [Format.flushIn_of_isInf binary32 fl _ (by decide) hi, isNaN_false_of_isInf _ _ hi]
  simp only [hi, Bool.false_eq_true, ↓reduceIte, sign32]
  split <;> simp_all <;> decide

/-- Double → word of any NaN, in any rounding mode: `0` and Invalid. -/
theorem f64ToW32_of_nan (rm : RoundingMode) (fl : Bool) (x : BitVec 64) (h : isNaN64 x = true) :
    f64ToW32 rm fl x = (0#32, Flags.invalidOnly) := by
  have hn : binary64.isNaN x.toNat = true := h
  unfold f64ToW32
  rw [Format.withFlush_single_of_not_subnormal binary64 fl _ _
    (Format.isSubnormal_of_isNaN binary64 _ (by decide) hn)]
  unfold Format.toW32 Format.toFixed
  rw [Format.flushIn_of_isNaN binary64 fl _ (by decide) hn]
  simp only [hn, ↓reduceIte]

/-- Double → word of `±∞`, in any rounding mode: `2^31 - 1` / `-2^31` and Invalid. -/
theorem f64ToW32_of_inf (rm : RoundingMode) (fl : Bool) (x : BitVec 64) (h : isInf64 x = true) :
    f64ToW32 rm fl x = (if sign64 x then 0x80000000#32 else 0x7FFFFFFF#32, Flags.invalidOnly) := by
  have hi : binary64.isInf x.toNat = true := h
  unfold f64ToW32
  rw [Format.withFlush_single_of_not_subnormal binary64 fl _ _
    (Format.isSubnormal_of_isInf binary64 _ (by decide) hi)]
  unfold Format.toW32 Format.toFixed
  rw [Format.flushIn_of_isInf binary64 fl _ (by decide) hi, isNaN_false_of_isInf _ _ hi]
  simp only [hi, Bool.false_eq_true, ↓reduceIte, sign64]
  split <;> simp_all <;> decide

/-- The only flags float → fixed point can ever raise are Invalid and Inexact, never both. -/
theorem f32ToW32_flags (rm : RoundingMode) (fl : Bool) (x : BitVec 32) :
    (f32ToW32 rm fl x).2 = Flags.none ∨ (f32ToW32 rm fl x).2 = Flags.invalidOnly ∨
      (f32ToW32 rm fl x).2 = Flags.inexactOnly := by
  unfold f32ToW32 Format.withFlush
  by_cases hs : (fl && binary32.isSubnormal x.toNat) = true
  · -- a flushed operand is a zero, and the flush signals Inexact
    have hz : binary32.flushIn fl x.toNat = binary32.zero (binary32.signBit x.toNat) := by
      simp only [Format.flushIn, hs, ↓reduceIte]
    have hf : binary32.flushFlags fl [x.toNat] = Flags.inexactOnly := by
      simp only [Bool.and_eq_true] at hs
      simp [Format.flushFlags, Flags.inexactOnly, hs.1, hs.2]
    rw [hz, hf]; right; right
    cases rm <;> cases binary32.signBit x.toNat <;> decide
  have hf : binary32.flushFlags fl [x.toNat] = Flags.none := by
    simp only [Bool.not_eq_true] at hs
    simp [Format.flushFlags, Flags.none, List.any, hs]
  have hor : ∀ g : Flags, g.or Flags.none = g := by
    intro g; cases g; simp [Flags.or, Flags.none]
  simp only [hf, hor]
  unfold Format.toW32 Format.toFixed
  split
  · simp
  · split
    · simp
    · dsimp only
      split
      · simp
      · split
        · simp
        · split <;> simp

/-- Any NaN operand makes the relation "unordered". -/
theorem f32Relation_of_nan_left (a b : BitVec 32) (h : isNaN32 a = true) :
    f32Relation a b = ⟨true, false, false⟩ := by
  simp only [isNaN32] at h
  simp [f32Relation, Format.relation, h]

/-- Any NaN operand makes the relation "unordered". -/
theorem f32Relation_of_nan_right (a b : BitVec 32) (h : isNaN32 b = true) :
    f32Relation a b = ⟨true, false, false⟩ := by
  simp only [isNaN32] at h
  simp [f32Relation, Format.relation, h]

/-- `Flags.or` has `Flags.none` as unit. -/
theorem Flags.or_none (f : Flags) : f.or Flags.none = f ∧ Flags.none.or f = f := by
  cases f; simp [Flags.or, Flags.none]

/-- `Flags.toBits`/`ofBits` round-trip (all 32 flag sets). -/
theorem Flags.ofBits_toBits (f : Flags) : Flags.ofBits f.toBits = f := by
  obtain ⟨a, b, c, d, e⟩ := f
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

/-- `RoundingMode` encoding round-trip. -/
theorem RoundingMode.ofBits_toBits (rm : RoundingMode) :
    RoundingMode.ofBits rm.toBits = rm := by
  cases rm <;> decide

/-! ### Float → word: concrete cases

Constants: `0x40200000` = 2.5, `0x40600000` = 3.5, `0xC0200000` = −2.5,
`0x4F32D05E` = 3e9, `0xCF32D05E` = −3e9, `0x7F800000` = +∞,
`0x4EFFFFFF` = 2147483520 (largest single below 2^31), `0x4F000000` = 2^31,
`0xCF000000` = −2^31, `0xCF000001` = −2147483904. -/

/-- Table 6.3 (MD00082 Vol I-A Rev 6.01 p.82), `FCSR.NAN2008 = 1`: a NaN gives 0, a value too big
`2^31 - 1`, a value too small `-2^31`. -/
theorem f32ToW32_special :
    f32ToW32 .RN false 0x7FBFFFFF#32 = (0#32, Flags.invalidOnly) ∧            -- SNaN
    f32ToW32 .RZ false 0x7FC00000#32 = (0#32, Flags.invalidOnly) ∧            -- QNaN
    f32ToW32 .RZ false 0xFFC00000#32 = (0#32, Flags.invalidOnly) ∧            -- −NaN
    f32ToW32 .RN false 0x7F800000#32 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧  -- +∞
    f32ToW32 .RM false 0xFF800000#32 = (0x80000000#32, Flags.invalidOnly) ∧  -- −∞
    f32ToW32 .RZ false 0x4F32D05E#32 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧  -- 3e9
    f32ToW32 .RZ false 0xCF32D05E#32 = (0x80000000#32, Flags.invalidOnly) ∧  -- −3e9
    f32ToW32 .RN false 0xCF32D05E#32 = (0x80000000#32, Flags.invalidOnly) := by decide

theorem f32ToW32_ties_to_even :
    f32ToW32 .RN false 0x40200000#32 = (2#32, Flags.inexactOnly) ∧            -- 2.5 → 2
    f32ToW32 .RN false 0x40600000#32 = (4#32, Flags.inexactOnly) ∧            -- 3.5 → 4
    f32ToW32 .RN false 0xC0200000#32 = (0xFFFFFFFE#32, Flags.inexactOnly) ∧   -- −2.5 → −2
    f32ToW32 .RN false 0x3F000000#32 = (0#32, Flags.inexactOnly) ∧            -- 0.5 → 0
    f32ToW32 .RN false 0x3FC00000#32 = (2#32, Flags.inexactOnly) := by decide -- 1.5 → 2

theorem f32ToW32_directed :
    f32ToW32 .RZ false 0x40200000#32 = (2#32, Flags.inexactOnly) ∧            -- trunc 2.5
    f32ToW32 .RP false 0x40200000#32 = (3#32, Flags.inexactOnly) ∧            -- ceil 2.5
    f32ToW32 .RM false 0x40200000#32 = (2#32, Flags.inexactOnly) ∧            -- floor 2.5
    f32ToW32 .RZ false 0xC0200000#32 = (0xFFFFFFFE#32, Flags.inexactOnly) ∧   -- trunc −2.5
    f32ToW32 .RP false 0xC0200000#32 = (0xFFFFFFFE#32, Flags.inexactOnly) ∧   -- ceil −2.5
    f32ToW32 .RM false 0xC0200000#32 = (0xFFFFFFFD#32, Flags.inexactOnly) := by decide

theorem f32ToW32_zero_and_exact :
    f32ToW32 .RN false 0x80000000#32 = (0#32, Flags.none) ∧                   -- −0.0
    f32ToW32 .RM false 0x80000000#32 = (0#32, Flags.none) ∧
    f32ToW32 .RN false 0x00000000#32 = (0#32, Flags.none) ∧
    f32ToW32 .RN false 0x40400000#32 = (3#32, Flags.none) ∧                   -- 3.0
    f32ToW32 .RP false 0x00000001#32 = (1#32, Flags.inexactOnly) ∧            -- ceil 2^−149
    f32ToW32 .RM false 0x80000001#32 = (0xFFFFFFFF#32, Flags.inexactOnly) ∧  -- floor −2^−149
    -- FCSR.FS = 1: the subnormal operand is flushed to a zero first (Table 6.8, `FS`, p.93)
    -- and the flush signals Inexact (MD00082 Vol I-A Rev 6.01 §6.7.2.4, p.102)
    f32ToW32 .RP true 0x00000001#32 = (0#32, Flags.inexactOnly) ∧
    f32ToW32 .RM true 0x80000001#32 = (0#32, Flags.inexactOnly) ∧
    f32ToW32 .RN true 0x00800000#32 = (0#32, Flags.inexactOnly) :=
  by decide

theorem f32ToW32_boundaries :
    f32ToW32 .RN false 0x4EFFFFFF#32 = (0x7FFFFF80#32, Flags.none) ∧          -- 2147483520
    f32ToW32 .RN false 0x4F000000#32 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧   -- 2^31
    f32ToW32 .RN false 0xCF000000#32 = (0x80000000#32, Flags.none) ∧          -- −2^31 exactly
    f32ToW32 .RZ false 0xCF000000#32 = (0x80000000#32, Flags.none) ∧
    f32ToW32 .RZ false 0xCF000001#32 = (0x80000000#32, Flags.invalidOnly) := by decide

/-! Double → word.  Constants: `0x41DFFFFFFFC00000` = 2147483647.0,
`0x41DFFFFFFFE00000` = 2147483647.5, `0x41E0000000000000` = 2^31,
`0xC1E0000000000000` = −2^31, `0xC1E0000000100000` = −2147483648.5,
`0xC1E0000000200000` = −2147483649.0, `0x4004000000000000` = 2.5. -/

theorem f64ToW32_boundaries :
    -- 2^31 − 1 exactly: a *valid* 0x7FFFFFFF, no flag
    f64ToW32 .RN false 0x41DFFFFFFFC00000#64 = (0x7FFFFFFF#32, Flags.none) ∧
    -- 2^31 − 0.5: valid when rounded down, Invalid when rounded up to 2^31
    f64ToW32 .RZ false 0x41DFFFFFFFE00000#64 = (0x7FFFFFFF#32, Flags.inexactOnly) ∧
    f64ToW32 .RM false 0x41DFFFFFFFE00000#64 = (0x7FFFFFFF#32, Flags.inexactOnly) ∧
    f64ToW32 .RN false 0x41DFFFFFFFE00000#64 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧
    f64ToW32 .RP false 0x41DFFFFFFFE00000#64 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧
    f64ToW32 .RZ false 0x41E0000000000000#64 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧
    -- −2^31 exactly: valid
    f64ToW32 .RN false 0xC1E0000000000000#64 = (0x80000000#32, Flags.none) ∧
    -- −2^31 − 0.5: valid when rounded toward zero / to even, Invalid toward −∞
    f64ToW32 .RZ false 0xC1E0000000100000#64 = (0x80000000#32, Flags.inexactOnly) ∧
    f64ToW32 .RN false 0xC1E0000000100000#64 = (0x80000000#32, Flags.inexactOnly) ∧
    f64ToW32 .RP false 0xC1E0000000100000#64 = (0x80000000#32, Flags.inexactOnly) ∧
    f64ToW32 .RM false 0xC1E0000000100000#64 = (0x80000000#32, Flags.invalidOnly) ∧
    f64ToW32 .RZ false 0xC1E0000000200000#64 = (0x80000000#32, Flags.invalidOnly) := by decide

theorem f64ToW32_misc :
    f64ToW32 .RN false 0x4004000000000000#64 = (2#32, Flags.inexactOnly) ∧    -- 2.5 → 2
    f64ToW32 .RP false 0x4004000000000000#64 = (3#32, Flags.inexactOnly) ∧
    f64ToW32 .RN false 0x7FF7FFFFFFFFFFFF#64 = (0#32, Flags.invalidOnly) ∧             -- SNaN
    f64ToW32 .RN false 0xFFF0000000000000#64 = (0x80000000#32, Flags.invalidOnly) ∧   -- −∞
    f64ToW32 .RZ false 0x7E37E43C8800759C#64 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧  -- 1e300
    f64ToW32 .RN false 0x8000000000000000#64 = (0#32, Flags.none) := by decide +kernel

/-! ### Format conversions: concrete cases -/

theorem f32ToF64_cases :
    f32ToF64 false 0x3F800000#32 = (0x3FF0000000000000#64, Flags.none) ∧      -- 1.0
    f32ToF64 false 0x00000001#32 = (0x36A0000000000000#64, Flags.none) ∧      -- 2^−149
    f32ToF64 false 0x7F800000#32 = (0x7FF0000000000000#64, Flags.none) ∧      -- +∞
    f32ToF64 false 0xFF800000#32 = (0xFFF0000000000000#64, Flags.none) ∧      -- −∞
    f32ToF64 false 0x80000000#32 = (0x8000000000000000#64, Flags.none) ∧      -- −0
    f32ToF64 false 0x7F7FFFFF#32 = (0x47EFFFFFE0000000#64, Flags.none) ∧      -- max finite
    -- a NaN: sign and payload preserved (widened with zeros), made quiet; Invalid for an SNaN
    -- (QEMU mips32r6-generic: cvt.d.s of 0x7f800022 is 0x7ff80004_40000000)
    f32ToF64 false 0x7FBFFFFF#32 = (0x7FFFFFFFE0000000#64, Flags.invalidOnly) ∧
    f32ToF64 false 0xFF800001#32 = (0xFFF8000020000000#64, Flags.invalidOnly) ∧
    f32ToF64 false 0x7F800022#32 = (0x7FF8000440000000#64, Flags.invalidOnly) ∧
    f32ToF64 false 0x7FC00000#32 = (defaultQNaN64, Flags.none) ∧            -- QNaN
    -- FCSR.FS = 1: a subnormal operand is flushed to a signed zero, signaling Inexact (§6.7.2.4, p.102)
    f32ToF64 true 0x00000001#32 = (0#64, Flags.inexactOnly) ∧
    f32ToF64 true 0x80000001#32 = (0x8000000000000000#64, Flags.inexactOnly) ∧
    f32ToF64 true 0x00800000#32 = (0x3810000000000000#64, Flags.none) := by decide

/-- Constants: `0x3FF0000010000000` = 1 + 2^−24 (exactly halfway between 1.0
and its single successor), `0x7E37E43C8800759C` = 1e300,
`0x3730000000000000` = 2^−140, `0x3730000000400000` = 2^−140·(1 + 2^−30),
`0x3690000000000000` = 2^−150 (half the smallest single subnormal),
`0x380FFFFFFFFFFFFF` = just below the smallest normal single 2^−126. -/
theorem f64ToF32_cases :
    f64ToF32 .RN 0x3FF0000000000000#64 = (0x3F800000#32, Flags.none) ∧
    -- tie → even
    f64ToF32 .RN 0x3FF0000010000000#64 = (0x3F800000#32, Flags.inexactOnly) ∧
    f64ToF32 .RP 0x3FF0000010000000#64 = (0x3F800001#32, Flags.inexactOnly) ∧
    f64ToF32 .RN 0x3FF0000030000000#64 = (0x3F800002#32, Flags.inexactOnly) ∧
    -- overflow
    f64ToF32 .RN 0x7E37E43C8800759C#64 =
      (0x7F800000#32, { overflow := true, inexact := true }) ∧
    f64ToF32 .RZ 0x7E37E43C8800759C#64 =
      (0x7F7FFFFF#32, { overflow := true, inexact := true }) ∧
    f64ToF32 .RM 0x7E37E43C8800759C#64 =
      (0x7F7FFFFF#32, { overflow := true, inexact := true }) ∧
    f64ToF32 .RP 0xFE37E43C8800759C#64 =
      (0xFF7FFFFF#32, { overflow := true, inexact := true }) ∧
    f64ToF32 .RM 0xFE37E43C8800759C#64 =
      (0xFF800000#32, { overflow := true, inexact := true }) ∧
    -- subnormal results: exact ⇒ no flag; inexact ⇒ Underflow + Inexact
    f64ToF32 .RN 0x3730000000000000#64 = (0x00000200#32, Flags.none) ∧
    f64ToF32 .RN 0x3730000000400000#64 =
      (0x00000200#32, { underflow := true, inexact := true }) ∧
    f64ToF32 .RN 0x3690000000000000#64 =
      (0x00000000#32, { underflow := true, inexact := true }) ∧
    f64ToF32 .RP 0x3690000000000000#64 =
      (0x00000001#32, { underflow := true, inexact := true }) ∧
    -- rounds up to the smallest normal: not tiny after rounding
    f64ToF32 .RN 0x380FFFFFFFFFFFFF#64 = (0x00800000#32, Flags.inexactOnly) ∧
    f64ToF32 .RZ 0x380FFFFFFFFFFFFF#64 =
      (0x007FFFFF#32, { underflow := true, inexact := true }) ∧
    -- specials
    f64ToF32 .RN 0xFFF0000000000000#64 = (0xFF800000#32, Flags.none) ∧
    f64ToF32 .RN 0x8000000000000000#64 = (0x80000000#32, Flags.none) ∧
    -- a NaN: sign and the top 23 payload bits preserved, made quiet; Invalid for an SNaN
    f64ToF32 .RN 0x7FF7FFFFFFFFFFFF#64 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧
    f64ToF32 .RN 0xFFF4000000000000#64 = (0xFFE00000#32, Flags.invalidOnly) ∧
    f64ToF32 .RN 0xFFF0000000000001#64 = (0xFFC00000#32, Flags.invalidOnly) ∧
    f64ToF32 .RN 0x7FF8000000000000#64 = (defaultQNaN32, Flags.none) ∧
    -- QEMU mips32r6-generic: cvt.s.d of 0x7ff80000_00000123 and 0x7ff00000_00000123 is 0x7fc00000
    f64ToF32 .RN 0x7FF8000000000123#64 = (0x7FC00000#32, Flags.none) ∧
    f64ToF32 .RN 0x7FF0000000000123#64 = (0x7FC00000#32, Flags.invalidOnly) := by decide +kernel

theorem w32ToF32_cases :
    w32ToF32 .RN 0x80000000#32 = (0xCF000000#32, Flags.none) ∧          -- −2^31
    w32ToF32 .RN 0#32 = (0#32, Flags.none) ∧
    w32ToF32 .RN 1#32 = (0x3F800000#32, Flags.none) ∧
    w32ToF32 .RN 0xFFFFFFFF#32 = (0xBF800000#32, Flags.none) ∧          -- −1
    w32ToF32 .RN 16777216#32 = (0x4B800000#32, Flags.none) ∧            -- 2^24
    w32ToF32 .RN 16777217#32 = (0x4B800000#32, Flags.inexactOnly) ∧     -- 2^24+1 ↓
    w32ToF32 .RP 16777217#32 = (0x4B800001#32, Flags.inexactOnly) ∧
    w32ToF32 .RN 16777219#32 = (0x4B800002#32, Flags.inexactOnly) ∧     -- tie → even
    w32ToF32 .RN 0x7FFFFFFF#32 = (0x4F000000#32, Flags.inexactOnly) ∧   -- → 2^31
    w32ToF32 .RZ 0x7FFFFFFF#32 = (0x4EFFFFFF#32, Flags.inexactOnly) := by decide

theorem w32ToF64_cases :
    w32ToF64 0x80000000#32 = 0xC1E0000000000000#64 ∧
    w32ToF64 0#32 = 0#64 ∧
    w32ToF64 1#32 = 0x3FF0000000000000#64 ∧
    w32ToF64 0xFFFFFFFF#32 = 0xBFF0000000000000#64 ∧
    w32ToF64 0x7FFFFFFF#32 = 0x41DFFFFFFFC00000#64 ∧
    w32ToF64 16777217#32 = 0x4170000010000000#64 := by decide

/-! ### Longword conversions (Release 6, 64-bit FPU) -/

/-- `CVT.L.fmt`/`ROUND.L.fmt`/... and `CVT.S.L`/`CVT.D.L` (Table 6.3 p.82 with `FCSR.NAN2008 = 1`:
0 for a NaN, `2^63 - 1` too big, `-2^63` too small; QEMU `mips32r6-generic` gives the same for
`cvt.l.s` of `0xdf000001`, `0x7f800022`, `0x5f000000`). Constants: `0xDF000001` = −(2^63 + 2^40),
`0x5F000000` = 2^63, `0x0020000000000001` = 2^53 + 1 (a tie for a double). -/
theorem long_cases :
    f32ToW64 .RN false 0xDF000001#32 = (0x8000000000000000#64, Flags.invalidOnly) ∧
    f32ToW64 .RN false 0x7F800022#32 = (0#64, Flags.invalidOnly) ∧
    f32ToW64 .RN false 0x5F000000#32 = (0x7FFFFFFFFFFFFFFF#64, Flags.invalidOnly) ∧
    f32ToW64 .RN false 0xFF800000#32 = (0x8000000000000000#64, Flags.invalidOnly) ∧
    f32ToW64 .RN false 0x40200000#32 = (2#64, Flags.inexactOnly) ∧
    f32ToW64 .RM false 0xC0200000#32 = (0xFFFFFFFFFFFFFFFD#64, Flags.inexactOnly) ∧
    f64ToW64 .RZ false 0xC3E0000000000000#64 = (0x8000000000000000#64, Flags.none) ∧
    w64ToF64 .RN 0x0020000000000001#64 = (0x4340000000000000#64, Flags.inexactOnly) ∧
    w64ToF64 .RP 0x0020000000000001#64 = (0x4340000000000001#64, Flags.inexactOnly) ∧
    w64ToF64 .RN 0x8000000000000000#64 = (0xC3E0000000000000#64, Flags.none) ∧
    w64ToF32 .RN 0x7FFFFFFFFFFFFFFF#64 = (0x5F000000#32, Flags.inexactOnly) ∧
    w64ToF32 .RN 0x0000000001000001#64 = (0x4B800000#32, Flags.inexactOnly) := by
  decide +kernel

/-! ### Classification and `abs`/`neg` -/

theorem classify_cases :
    isNaN32 0x7F800001#32 = true ∧ isSNaN32 0x7F800001#32 = true ∧
    isQNaN32 0x7FC00000#32 = true ∧ isSNaN32 0x7FC00000#32 = false ∧
    isNaN32 0x7F800000#32 = false ∧ isInf32 0xFF800000#32 = true ∧
    isZero32 0x80000000#32 = true ∧ isSubnormal32 0x007FFFFF#32 = true ∧
    isSubnormal32 0x00800000#32 = false ∧
    sign32 0xBF800000#32 = true ∧ expField32 0xBF800000#32 = 127 ∧
    fracField32 0x3FC00000#32 = 0x400000 ∧
    toExact32 0xC0200000#32 = ⟨true, 0xA00000, -22⟩ ∧                   -- −2.5
    toExact32 0x00000001#32 = ⟨false, 1, -149⟩ ∧
    isQNaN64 0x7FF8000000000000#64 = true ∧ isSNaN64 0x7FF0000000000001#64 = true ∧
    isInf64 0x7FF0000000000000#64 = true ∧ isSubnormal64 1#64 = true ∧
    expField64 0x3FF0000000000000#64 = 1023 ∧
    toExact64 0x3FF8000000000000#64 = ⟨false, 0x18000000000000, -52⟩ := by decide +kernel

/-- `ABS`/`NEG` with `FCSR.ABS2008 = 1` (MD00086 Vol II-A Rev 6.06, ABS.fmt p.32, NEG.fmt p.307):
only the sign bit changes, NaNs included. -/
theorem absNeg_cases :
    f32Abs 0xBF800000#32 = 0x3F800000#32 ∧
    f32Neg 0x3F800000#32 = 0xBF800000#32 ∧
    f32Neg 0x00000000#32 = 0x80000000#32 ∧
    f32Abs 0xFF800000#32 = 0x7F800000#32 ∧
    f32Abs 0xFFC00001#32 = 0x7FC00001#32 ∧          -- QNaN
    f32Neg 0x7F800022#32 = 0xFF800022#32 ∧          -- SNaN: not quieted
    f64Abs 0xBFF0000000000000#64 = 0x3FF0000000000000#64 ∧
    f64Neg 0x3FF0000000000000#64 = 0xBFF0000000000000#64 ∧
    f64Neg 0x7FF0000000000001#64 = 0xFFF0000000000001#64 ∧
    f64Abs 0xFFF8000000000000#64 = 0x7FF8000000000000#64 := by decide

/-! ### Comparison -/

/-- All sixteen predicates on "less": true for codes with `cond₂` set. -/
theorem fpCompare_less :
    Cond.all.map (fun c => fpCompare c false true false) =
      [false, false, false, false, true, true, true, true,
       false, false, false, false, true, true, true, true] := by decide

/-- All sixteen predicates on "equal": true for codes with `cond₁` set. -/
theorem fpCompare_equal :
    Cond.all.map (fun c => fpCompare c false false true) =
      [false, false, true, true, false, false, true, true,
       false, false, true, true, false, false, true, true] := by decide

/-- All sixteen predicates on "greater": all false. -/
theorem fpCompare_greater :
    Cond.all.map (fun c => fpCompare c false false false) =
      [false, false, false, false, false, false, false, false,
       false, false, false, false, false, false, false, false] := by decide

/-- All sixteen predicates on "unordered": true for codes with `cond₀` set. -/
theorem fpCompare_unordered :
    Cond.all.map (fun c => fpCompare c true false false) =
      [false, true, false, true, false, true, false, true,
       false, true, false, true, false, true, false, true] := by decide

/-- Invalid on a quiet-NaN (unordered, no SNaN) comparison: exactly the
signaling predicates 8..15. -/
theorem fpCompareInvalid_quiet :
    Cond.all.map (fun c => fpCompareInvalid c true false) =
      [false, false, false, false, false, false, false, false,
       true, true, true, true, true, true, true, true] := by decide

/-- A signaling NaN raises Invalid under every predicate; ordered operands
never do. -/
theorem fpCompareInvalid_other (c : BitVec 4) (un : Bool) :
    fpCompareInvalid c un true = true ∧ fpCompareInvalid c false false = false := by
  simp [fpCompareInvalid]

/-- Relations from bit patterns (1.0 = `0x3F800000`, 2.0 = `0x40000000`). -/
theorem f32Relation_cases :
    f32Relation 0x3F800000#32 0x40000000#32 = ⟨false, true, false⟩ ∧   -- 1 < 2
    f32Relation 0x40000000#32 0x3F800000#32 = ⟨false, false, false⟩ ∧  -- 2 > 1
    f32Relation 0x3F800000#32 0x3F800000#32 = ⟨false, false, true⟩ ∧   -- 1 = 1
    f32Relation 0x80000000#32 0x00000000#32 = ⟨false, false, true⟩ ∧   -- −0 = +0
    f32Relation 0xBF800000#32 0x00000001#32 = ⟨false, true, false⟩ ∧   -- −1 < tiny
    f32Relation 0xC0000000#32 0xBF800000#32 = ⟨false, true, false⟩ ∧   -- −2 < −1
    f32Relation 0xFF800000#32 0xFF7FFFFF#32 = ⟨false, true, false⟩ ∧   -- −∞ < −max
    f32Relation 0x7F7FFFFF#32 0x7F800000#32 = ⟨false, true, false⟩ ∧   -- max < +∞
    f32Relation 0x7FBFFFFF#32 0x3F800000#32 = ⟨true, false, false⟩ ∧   -- NaN ? 1
    f32Relation 0x3F800000#32 0x7FC00000#32 = ⟨true, false, false⟩ ∧
    f32Relation 0x7FBFFFFF#32 0x7FBFFFFF#32 = ⟨true, false, false⟩ ∧
    f64Relation 0x3FF0000000000000#64 0x4000000000000000#64 = ⟨false, true, false⟩ ∧
    f64Relation 0x8000000000000000#64 0#64 = ⟨false, false, true⟩ ∧
    f64Relation 0x7FF7FFFFFFFFFFFF#64 0#64 = ⟨true, false, false⟩ := by decide

theorem f32Compare_cases :
    f32Compare Cond.olt 0x3F800000#32 0x40000000#32 = (true, Flags.none) ∧
    f32Compare Cond.ole 0x40000000#32 0x3F800000#32 = (false, Flags.none) ∧
    f32Compare Cond.eq 0x80000000#32 0x00000000#32 = (true, Flags.none) ∧
    -- quiet NaN: non-signaling predicate is silent, signaling one raises
    f32Compare Cond.ult 0x7FC00000#32 0x3F800000#32 = (true, Flags.none) ∧
    f32Compare Cond.eq 0x7FC00000#32 0x3F800000#32 = (false, Flags.none) ∧
    f32Compare Cond.lt 0x7FC00000#32 0x3F800000#32 = (false, Flags.invalidOnly) ∧
    f32Compare Cond.ngt 0x7FC00000#32 0x3F800000#32 = (true, Flags.invalidOnly) ∧
    -- signaling NaN: always raises
    f32Compare Cond.un 0x7FBFFFFF#32 0x3F800000#32 = (true, Flags.invalidOnly) ∧
    f64Compare Cond.le 0x3FF0000000000000#64 0x3FF0000000000000#64 = (true, Flags.none) ∧
    f64Compare Cond.sf 0x7FF8000000000000#64 0#64 = (false, Flags.invalidOnly) := by decide

/-! ### FCSR -/

theorem fcsr_field_cases :
    getRM 0#32 = .RN ∧ getRM 1#32 = .RZ ∧ getRM 2#32 = .RP ∧ getRM 0xFFFFFFFF#32 = .RM ∧
    setRM 0xFFFFFFFF#32 .RZ = 0xFFFFFFFD#32 ∧ setRM 0#32 .RM = 3#32 ∧
    getFlags 0x00000004#32 = Flags.inexactOnly ∧                         -- I = bit 2
    getFlags 0x00000040#32 = Flags.invalidOnly ∧                         -- V = bit 6
    getEnables 0x00000800#32 = Flags.invalidOnly ∧                       -- V = bit 11
    getEnables 0x00000080#32 = Flags.inexactOnly ∧                       -- I = bit 7
    getCause 0x00010000#32 = Flags.invalidOnly ∧                         -- V = bit 16
    getCause 0x00001000#32 = Flags.inexactOnly ∧                         -- I = bit 12
    getCause 0x00008000#32 = { divZero := true } ∧                       -- Z = bit 15
    getCause 0x00004000#32 = { overflow := true } ∧                      -- O = bit 14
    getCause 0x00002000#32 = { underflow := true } ∧                     -- U = bit 13
    getCauseE 0x00020000#32 = true ∧ getFS 0x01000000#32 = true := by decide

theorem raiseFlags_cases :
    -- Invalid: Cause.V (bit 16) and Flags.V (bit 6)
    raiseFlags 0#32 Flags.invalidOnly = 0x00010040#32 ∧
    -- Inexact: Cause.I (bit 12) and Flags.I (bit 2)
    raiseFlags 0#32 Flags.inexactOnly = 0x00001004#32 ∧
    raiseFlags 0#32 { overflow := true, inexact := true } = 0x00005014#32 ∧
    raiseFlags 0#32 { divZero := true } = 0x00008020#32 ∧
    raiseFlags 0#32 { underflow := true } = 0x00002008#32 ∧
    -- Cause is replaced (old V and E cleared), Flags are sticky
    raiseFlags 0x00030040#32 Flags.inexactOnly = 0x00001044#32 ∧
    -- no exception: Cause cleared, everything else kept
    raiseFlags 0xFFFFFFFF#32 Flags.none = 0xFFFC0FFF#32 ∧
    -- enabled?
    fpeEnabled 0x00000800#32 Flags.invalidOnly = true ∧
    fpeEnabled 0x00000800#32 Flags.inexactOnly = false ∧
    fpeEnabled 0x00000080#32 Flags.inexactOnly = true ∧
    fpeEnabled 0xFFFFF07F#32 { invalid := true, inexact := true } = false ∧
    fpeEnabled 0xFFFFFFFF#32 Flags.none = false ∧
    -- trapping: Cause set, Flags untouched
    fpUpdate 0x00000800#32 Flags.invalidOnly = (0x00010800#32, true) ∧
    fpUpdate 0x00000800#32 Flags.inexactOnly = (0x00001804#32, false) := by decide

/-- `raiseFlags` only ever changes Cause and Flags bits. -/
theorem raiseFlags_frame (fcsr : BitVec 32) (f : Flags) :
    raiseFlags fcsr f &&& ~~~(fcsrCauseMask ||| fcsrFlagsMask) =
      fcsr &&& ~~~(fcsrCauseMask ||| fcsrFlagsMask) := by
  -- the bits ORed in lie inside Cause ∪ Flags, for each of the 32 flag sets
  have hk : ((f.toBits.zeroExtend 32 : BitVec 32) <<< 12 ||| f.toBits.zeroExtend 32 <<< 2) &&&
      ~~~(fcsrCauseMask ||| fcsrFlagsMask) = 0#32 := by
    obtain ⟨a, b, c, d, e⟩ := f
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide
  have hm : ~~~fcsrCauseMask &&& ~~~(fcsrCauseMask ||| fcsrFlagsMask) =
      ~~~(fcsrCauseMask ||| fcsrFlagsMask) := by decide
  simp only [raiseFlags]
  rw [BitVec.or_assoc, BitVec.and_or_distrib_right, hk, BitVec.or_zero, BitVec.and_assoc, hm]

/-- The Release 6 control registers (MD00086 Vol II-A Rev 6.06, CFC1 p.129-130, CTC1 p.149-150):
`none` is Reserved Instruction. -/
theorem control_register_cases :
    readControl 0xFFFFFFFF#32 0 = some 0x00F30000#32 ∧                  -- FIR
    readControl 0xFFFFFFFF#32 31 = some 0x010FFFFF#32 ∧                 -- FCSR (NAN2008, ABS2008 read 1)
    readControl 0#32 31 = some 0x000C0000#32 ∧
    readControl 0xFFFFFFFF#32 25 = some 0#32 ∧                          -- FCCR: FCCs reserved
    readControl 0xFFFFFFFF#32 26 = some 0x0003F07C#32 ∧                 -- FEXR
    readControl 0xFFFFFFFF#32 28 = some 0x00000F87#32 ∧                 -- FENR
    readControl 0xFFFFFFFF#32 1 = none ∧ readControl 0#32 4 = none ∧    -- UFR, UNFR
    readControl 0#32 2 = none ∧ readControl 0#32 5 = none ∧             -- FRE: absent (FIR.FREP = 0), W7
    -- FENR bit 2 ↔ FS (FCSR bit 24)
    readFENR 0x01000000#32 = 0x04#32 ∧
    -- writes touch only their own fields
    writeControl 0#32 31 0xFFFFFFFF#32 = some 0x0103FFFF#32 ∧
    writeControl 0#32 25 0xFFFFFFFF#32 = some 0#32 ∧
    writeControl 0#32 26 0xFFFFFFFF#32 = some 0x0003F07C#32 ∧
    writeControl 0#32 28 0xFFFFFFFF#32 = some 0x01000F83#32 ∧
    writeControl 0xFFFFFFFF#32 25 0#32 = some 0xFFFFFFFF#32 ∧
    writeControl 0xFFFFFFFF#32 26 0#32 = some 0xFFFC0F83#32 ∧
    writeControl 0xFFFFFFFF#32 28 0#32 = some 0xFEFFF07C#32 ∧
    writeControl 0xFFFFFFFF#32 31 0#32 = some 0#32 ∧
    writeControl 0x12345678#32 0 0xFFFFFFFF#32 = none ∧                -- FIR: Reserved Instruction
    writeControl 0#32 2 0#32 = none ∧ writeControl 0#32 5 0#32 = none ∧
    -- CTC1 can raise a pending enabled exception
    fcsrTrapPending 0x00010800#32 = true ∧ fcsrTrapPending 0x00010000#32 = false ∧
    fcsrTrapPending 0x00020000#32 = true ∧ fcsrTrapPending 0x00000F80#32 = false := by decide

/-- Each `CTC1` view reads back what was written (on the bits that view
exposes). -/
theorem control_read_write (fcsr v : BitVec 32) :
    readFCSR (writeFCSR fcsr v) = (v &&& fcsrWritableMask) ||| fcsr2008Bits ∧
    readFEXR (writeFEXR fcsr v) = v &&& (fcsrCauseMask ||| fcsrFlagsMask) := by
  constructor
  · ext i hi; simp [readFCSR, writeFCSR]
  · have hm : ~~~(fcsrCauseMask ||| fcsrFlagsMask) &&& (fcsrCauseMask ||| fcsrFlagsMask) = 0#32 := by
      decide
    simp only [readFEXR, writeFEXR]
    rw [BitVec.and_or_distrib_right, BitVec.and_assoc, hm, BitVec.and_zero, BitVec.zero_or,
      BitVec.and_assoc, BitVec.and_self]

/-! ### `fpUpdate` -/

/-- `fpUpdate` reports a trap exactly when an enabled exception was raised. -/
theorem fpUpdate_snd (fcsr : BitVec 32) (f : Flags) :
    (fpUpdate fcsr f).2 = fpeEnabled fcsr f := by
  unfold fpUpdate; split <;> simp_all

/-- Without a trap, `fpUpdate` is `raiseFlags`: Cause := this operation's
exceptions, Flags accumulate. -/
theorem fpUpdate_fst_of_not_enabled (fcsr : BitVec 32) (f : Flags)
    (h : fpeEnabled fcsr f = false) : (fpUpdate fcsr f).1 = raiseFlags fcsr f := by
  unfold fpUpdate; simp [h]

/-- With a trap, `fpUpdate` writes only Cause (Flags are not updated). -/
theorem fpUpdate_fst_of_enabled (fcsr : BitVec 32) (f : Flags)
    (h : fpeEnabled fcsr f = true) :
    (fpUpdate fcsr f).1 =
      (fcsr &&& ~~~fcsrCauseMask) ||| ((f.toBits.zeroExtend 32 : BitVec 32) <<< 12) := by
  unfold fpUpdate; simp [h]

/-- An operation raising nothing never traps. -/
theorem fpeEnabled_none (fcsr : BitVec 32) : fpeEnabled fcsr Flags.none = false := by
  simp [fpeEnabled, Flags.none, Flags.toBits]

/-- `CTC1`/`CFC1` on register 31 round-trip every writable FCSR bit; `ABS2008`/`NAN2008` read 1. -/
theorem readControl_writeControl_fcsr (fcsr v : BitVec 32) :
    (writeControl fcsr 31 v).bind (fun x => readControl x 31) =
      some ((v &&& fcsrWritableMask) ||| fcsr2008Bits) := by
  simp only [writeControl, readControl, Option.bind_some, (control_read_write fcsr v).1]

/-! ### Arithmetic: NaN rules (general) -/

private theorem ofNat_toNat32 (a : BitVec 32) : BitVec.ofNat 32 a.toNat = a := by simp
private theorem ofNat_toNat64 (a : BitVec 64) : BitVec.ofNat 64 a.toNat = a := by simp

private theorem isNaN_of_isQNaN (f : Format) (n : Nat) (h : f.isQNaN n = true) :
    f.isNaN n = true := by
  simp only [Format.isQNaN, Bool.and_eq_true] at h; exact h.1

private theorem isSNaN_false_of_isQNaN (f : Format) (n : Nat) (h : f.isQNaN n = true) :
    f.isSNaN n = false := by
  simp only [Format.isQNaN, Format.isSNaN, Bool.and_eq_true, beq_iff_eq] at h ⊢
  simp [h.1, h.2]

/-- `flushIn` replaces only subnormals (never NaNs) by zeros (never NaNs): the NaN classes of an
operand are those of the flushed operand. -/
theorem Format.nanClass_flushIn (f : Format) (fl : Bool) (n : Nat) (hm : f.expMax ≠ 0)
    (hz : ∀ s, f.isNaN (f.zero s) = false) :
    f.isNaN (f.flushIn fl n) = f.isNaN n ∧ f.isSNaN (f.flushIn fl n) = f.isSNaN n ∧
      f.isQNaN (f.flushIn fl n) = f.isQNaN n := by
  unfold Format.flushIn
  split
  · rename_i hs
    have hsub : f.isSubnormal n = true := by simp_all
    have hn : f.isNaN n = false := by
      unfold Format.isSubnormal at hsub; unfold Format.isNaN
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hsub
      simp [hsub.1, Ne.symm hm]
    have hz' := hz (f.signBit n)
    simp [Format.isSNaN, Format.isQNaN, hn, hz']
  · exact ⟨rfl, rfl, rfl⟩

theorem nanClass_flushIn32 (fl : Bool) (n : Nat) :
    binary32.isNaN (binary32.flushIn fl n) = binary32.isNaN n ∧
      binary32.isSNaN (binary32.flushIn fl n) = binary32.isSNaN n ∧
      binary32.isQNaN (binary32.flushIn fl n) = binary32.isQNaN n :=
  Format.nanClass_flushIn binary32 fl n (by decide) (by decide)

theorem nanClass_flushIn64 (fl : Bool) (n : Nat) :
    binary64.isNaN (binary64.flushIn fl n) = binary64.isNaN n ∧
      binary64.isSNaN (binary64.flushIn fl n) = binary64.isSNaN n ∧
      binary64.isQNaN (binary64.flushIn fl n) = binary64.isQNaN n :=
  Format.nanClass_flushIn binary64 fl n (by decide) (by decide)

/-- **A quiet NaN first operand is the result** of `add`/`sub`/`mul`/`div`, unchanged, when the other
operand is not a signaling NaN (MD00082 Vol I-A Rev 6.01 §6.3.1.5, p.82-83; the model's choice of
operand, SPEC-NOTES §9 item 13: a signaling NaN operand is chosen first). The only exception is the
Inexact of flushing a subnormal second operand under FCSR.FS ("Flushing of subnormal input operands in
all instructions except comparisons causes Inexact exception to be signaled", §6.7.2.4, p.102). -/
theorem f32_arith_qnan_left (e : Env) (a b : BitVec 32) (h : isQNaN32 a = true)
    (hb : isSNaN32 b = false) :
    f32Add e a b = (a, { inexact := e.flush && isSubnormal32 b }) ∧ f32Sub e a b = (a, { inexact := e.flush && isSubnormal32 b }) ∧
    f32Mul e a b = (a, { inexact := e.flush && isSubnormal32 b }) ∧ f32Div e a b = (a, { inexact := e.flush && isSubnormal32 b }) := by
  have h1 := isNaN_of_isQNaN binary32 a.toNat h
  have h2 := isSNaN_false_of_isQNaN binary32 a.toNat h
  have hq : binary32.isQNaN a.toNat = true := h
  have hb' : binary32.isSNaN b.toNat = false := hb
  have fa := Format.flushIn_of_isNaN binary32 e.flush a.toNat (by decide) h1
  have ⟨_, sb, _⟩ := nanClass_flushIn32 e.flush b.toNat
  have hnb : binary32.isSNaN (Format.negBits binary32 (binary32.flushIn e.flush b.toNat)) = false ∨ True :=
    Or.inr trivial
  have sa := Format.isSubnormal_of_isNaN binary32 a.toNat (by decide) h1
  simp [f32Add, f32Sub, f32Mul, f32Div, Format.add, Format.sub, Format.mul, Format.div,
    Format.nanResult, Format.nanFlags, h1, h2, hq, fa, sb, hb', Format.withFlush,
    Format.flushFlags, Flags.or, sa, isSubnormal32]

/-- Double-precision form of `f32_arith_qnan_left`. -/
theorem f64_arith_qnan_left (e : Env) (a b : BitVec 64) (h : isQNaN64 a = true)
    (hb : isSNaN64 b = false) :
    f64Add e a b = (a, { inexact := e.flush && isSubnormal64 b }) ∧ f64Sub e a b = (a, { inexact := e.flush && isSubnormal64 b }) ∧
    f64Mul e a b = (a, { inexact := e.flush && isSubnormal64 b }) ∧ f64Div e a b = (a, { inexact := e.flush && isSubnormal64 b }) := by
  have h1 := isNaN_of_isQNaN binary64 a.toNat h
  have h2 := isSNaN_false_of_isQNaN binary64 a.toNat h
  have hq : binary64.isQNaN a.toNat = true := h
  have hb' : binary64.isSNaN b.toNat = false := hb
  have fa := Format.flushIn_of_isNaN binary64 e.flush a.toNat (by decide) h1
  have ⟨_, sb, _⟩ := nanClass_flushIn64 e.flush b.toNat
  have sa := Format.isSubnormal_of_isNaN binary64 a.toNat (by decide) h1
  simp [f64Add, f64Sub, f64Mul, f64Div, Format.add, Format.sub, Format.mul, Format.div,
    Format.nanResult, Format.nanFlags, h1, h2, hq, fa, sb, hb', Format.withFlush,
    Format.flushFlags, Flags.or, sa, isSubnormal64]

/-- **A signaling NaN operand signals Invalid Operation** in `add`/`sub`/
`mul`/`div`, whatever the other operand and the rounding mode
(MD00082 Vol I-A Rev 6.01 §6.3.1.4, p.81). -/
theorem f32_arith_snan_invalid (e : Env) (a b : BitVec 32)
    (h : isSNaN32 a = true ∨ isSNaN32 b = true) :
    (f32Add e a b).2.invalid = true ∧ (f32Sub e a b).2.invalid = true ∧
    (f32Mul e a b).2.invalid = true ∧ (f32Div e a b).2.invalid = true := by
  have hn : binary32.isNaN a.toNat = true ∨ binary32.isNaN b.toNat = true := by
    rcases h with h | h
    · left; simp only [isSNaN32, Format.isSNaN, Bool.and_eq_true] at h; exact h.1
    · right; simp only [isSNaN32, Format.isSNaN, Bool.and_eq_true] at h; exact h.1
  have hs : (binary32.isSNaN a.toNat || binary32.isSNaN b.toNat) = true := by
    rcases h with h | h
    · simp [show binary32.isSNaN a.toNat = true from h]
    · simp [show binary32.isSNaN b.toNat = true from h]
  have hn' : (binary32.isNaN a.toNat || binary32.isNaN b.toNat) = true := by
    rcases hn with h | h <;> simp [h]
  have ⟨na, sa, _⟩ := nanClass_flushIn32 e.flush a.toNat
  have ⟨nb, sb, _⟩ := nanClass_flushIn32 e.flush b.toNat
  simp [f32Add, f32Sub, f32Mul, f32Div, Format.add, Format.sub, Format.mul, Format.div,
    Format.nanFlags, na, sa, nb, sb, hn', hs, Format.withFlush, Flags.or]

/-! ### Arithmetic: concrete cases in every rounding mode

Constants: `0x3F800000` = 1.0, `0x33800000` = 2^−24 (half an ulp of 1.0),
`0x7F7FFFFF` = largest finite single, `0x00800000` = 2^−126 (smallest
normal), `0x00000001` = 2^−149 (smallest subnormal), `0x40400000` = 3.0. -/

/-- 1 + 2^−24 is exactly halfway between 1 and its successor: ties-to-even
keeps 1, only RP goes up; the negated sum mirrors it with RM. -/
theorem f32Add_tie :
    f32Add .RN 0x3F800000#32 0x33800000#32 = (0x3F800000#32, Flags.inexactOnly) ∧
    f32Add .RZ 0x3F800000#32 0x33800000#32 = (0x3F800000#32, Flags.inexactOnly) ∧
    f32Add .RP 0x3F800000#32 0x33800000#32 = (0x3F800001#32, Flags.inexactOnly) ∧
    f32Add .RM 0x3F800000#32 0x33800000#32 = (0x3F800000#32, Flags.inexactOnly) ∧
    f32Add .RN 0xBF800000#32 0xB3800000#32 = (0xBF800000#32, Flags.inexactOnly) ∧
    f32Add .RP 0xBF800000#32 0xB3800000#32 = (0xBF800000#32, Flags.inexactOnly) ∧
    f32Add .RM 0xBF800000#32 0xB3800000#32 = (0xBF800001#32, Flags.inexactOnly) := by
  decide +kernel

/-- Overflow default results (MD00082 Vol I-A Rev 6.01 Table 6.14, p.100):
RN ±∞; RZ ± largest finite; RP +∞ / −largest; RM +largest / −∞. -/
theorem f32Add_overflow :
    f32Add .RN 0x7F7FFFFF#32 0x7F7FFFFF#32 = (0x7F800000#32, { overflow := true, inexact := true }) ∧
    f32Add .RZ 0x7F7FFFFF#32 0x7F7FFFFF#32 = (0x7F7FFFFF#32, { overflow := true, inexact := true }) ∧
    f32Add .RP 0x7F7FFFFF#32 0x7F7FFFFF#32 = (0x7F800000#32, { overflow := true, inexact := true }) ∧
    f32Add .RM 0x7F7FFFFF#32 0x7F7FFFFF#32 = (0x7F7FFFFF#32, { overflow := true, inexact := true }) ∧
    f32Add .RN 0xFF7FFFFF#32 0xFF7FFFFF#32 = (0xFF800000#32, { overflow := true, inexact := true }) ∧
    f32Add .RZ 0xFF7FFFFF#32 0xFF7FFFFF#32 = (0xFF7FFFFF#32, { overflow := true, inexact := true }) ∧
    f32Add .RP 0xFF7FFFFF#32 0xFF7FFFFF#32 = (0xFF7FFFFF#32, { overflow := true, inexact := true }) ∧
    f32Add .RM 0xFF7FFFFF#32 0xFF7FFFFF#32 = (0xFF800000#32, { overflow := true, inexact := true }) := by
  decide +kernel

/-- Signs of exact zero sums: `x − x` is `+0` except under RM; `(−0) + (−0)`
is `−0` in every mode; `(+0) + (−0)` is `+0` except under RM. -/
theorem f32_zero_sums :
    f32Sub .RN 0x3F800000#32 0x3F800000#32 = (0x00000000#32, Flags.none) ∧
    f32Sub .RZ 0x3F800000#32 0x3F800000#32 = (0x00000000#32, Flags.none) ∧
    f32Sub .RP 0x3F800000#32 0x3F800000#32 = (0x00000000#32, Flags.none) ∧
    f32Sub .RM 0x3F800000#32 0x3F800000#32 = (0x80000000#32, Flags.none) ∧
    f32Add .RN 0x80000000#32 0x80000000#32 = (0x80000000#32, Flags.none) ∧
    f32Add .RP 0x80000000#32 0x80000000#32 = (0x80000000#32, Flags.none) ∧
    f32Add .RN 0x00000000#32 0x80000000#32 = (0x00000000#32, Flags.none) ∧
    f32Add .RM 0x00000000#32 0x80000000#32 = (0x80000000#32, Flags.none) := by
  decide +kernel

/-- 1/3 in the four modes, and division's special cases (MD00082 Vol I-A
Rev 6.01 §6.7.2.1, §6.7.2.2, p.100). -/
theorem f32Div_cases :
    f32Div .RN 0x3F800000#32 0x40400000#32 = (0x3EAAAAAB#32, Flags.inexactOnly) ∧
    f32Div .RZ 0x3F800000#32 0x40400000#32 = (0x3EAAAAAA#32, Flags.inexactOnly) ∧
    f32Div .RP 0x3F800000#32 0x40400000#32 = (0x3EAAAAAB#32, Flags.inexactOnly) ∧
    f32Div .RM 0x3F800000#32 0x40400000#32 = (0x3EAAAAAA#32, Flags.inexactOnly) ∧
    -- finite nonzero / 0: correctly signed ∞, Divide by Zero
    f32Div .RN 0x3F800000#32 0x80000000#32 = (0xFF800000#32, { divZero := true }) ∧
    -- 0/0 and ∞/∞: Invalid, default QNaN; ∞/0: ∞, no exception
    f32Div .RN 0x00000000#32 0x80000000#32 = (defaultQNaN32, Flags.invalidOnly) ∧
    f32Div .RN 0x7F800000#32 0xFF800000#32 = (defaultQNaN32, Flags.invalidOnly) ∧
    f32Div .RN 0x7F800000#32 0x00000000#32 = (0x7F800000#32, Flags.none) ∧
    f32Div .RN 0x3F800000#32 0xFF800000#32 = (0x80000000#32, Flags.none) := by
  decide +kernel

/-- Underflow (MD00082 Vol I-A Rev 6.01 §6.7.2.3, p.101): half the smallest
subnormal is tiny and inexact in every mode; 2^−126 × 0.5 is tiny but exact,
so it signals Underflow only when the Underflow trap is enabled; with
FCSR.FS = 1 (§6.7.2.4) a tiny result is flushed to a same-signed zero with
Underflow and Inexact. -/
theorem f32_underflow_cases :
    f32Div .RN 0x00000001#32 0x40000000#32 = (0x00000000#32, { underflow := true, inexact := true }) ∧
    f32Div .RZ 0x00000001#32 0x40000000#32 = (0x00000000#32, { underflow := true, inexact := true }) ∧
    f32Div .RP 0x00000001#32 0x40000000#32 = (0x00000001#32, { underflow := true, inexact := true }) ∧
    f32Div .RM 0x00000001#32 0x40000000#32 = (0x00000000#32, { underflow := true, inexact := true }) ∧
    f32Mul .RN 0x00800000#32 0x3F000000#32 = (0x00400000#32, Flags.none) ∧
    f32Mul { enables := { underflow := true } } 0x00800000#32 0x3F000000#32 =
      (0x00400000#32, { underflow := true }) ∧
    f32Mul { flush := true } 0x00800000#32 0x3F000000#32 =
      (0x00000000#32, { underflow := true, inexact := true }) ∧
    f32Mul { flush := true } 0x80800000#32 0x3F000000#32 =
      (0x80000000#32, { underflow := true, inexact := true }) := by
  decide +kernel

/-- Inexact on overflow (MD00082 Vol I-A Rev 6.01 §6.7.2.6, p.102): signaled
"if the rounded result of an operation overflows without an overflow trap";
with the Overflow trap enabled, only if the rounding itself was inexact. -/
theorem f32Mul_overflow_inexact :
    f32Mul .RN 0x7F7FFFFF#32 0x40000000#32 = (0x7F800000#32, { overflow := true, inexact := true }) ∧
    f32Mul { enables := { overflow := true } } 0x7F7FFFFF#32 0x40000000#32 =
      (0x7F800000#32, { overflow := true }) ∧
    f32Mul { enables := { overflow := true } } 0x7F7FFFFF#32 0x7F7FFFFF#32 =
      (0x7F800000#32, { overflow := true, inexact := true }) := by
  decide +kernel

/-- Invalid operations with no NaN operand create the default QNaN
(MD00082 Vol I-A Rev 6.01 §6.7.2.1, p.100; Table 6.3, p.82). -/
theorem f32_invalid_cases :
    f32Sub .RN 0x7F800000#32 0x7F800000#32 = (defaultQNaN32, Flags.invalidOnly) ∧   -- ∞ − ∞
    f32Add .RN 0x7F800000#32 0xFF800000#32 = (defaultQNaN32, Flags.invalidOnly) ∧   -- ∞ + −∞
    f32Add .RN 0x7F800000#32 0x7F800000#32 = (0x7F800000#32, Flags.none) ∧          -- ∞ + ∞
    f32Mul .RN 0x00000000#32 0xFF800000#32 = (defaultQNaN32, Flags.invalidOnly) ∧   -- 0 × ∞
    f32Sqrt .RN 0xBF800000#32 = (defaultQNaN32, Flags.invalidOnly) ∧                -- √−1
    f32Sqrt .RN 0xFF800000#32 = (defaultQNaN32, Flags.invalidOnly) := by            -- √−∞
  decide +kernel

/-- The NaN rule with `FCSR.NAN2008 = 1` (MD00082 Vol I-A Rev 6.01 §6.3.1.5, p.82-83; the model's
choice of operand, SPEC-NOTES §9 item 13): the first signaling NaN operand, made quiet, with Invalid;
else the first quiet NaN, unchanged. The values are those QEMU `mips32r6-generic` returns for the
same operands (`0x7f800001 + 1.0 = 0x7fc00001`, `0x7fc00011 + 0x7f800022 = 0x7fc00022`, ...). -/
theorem f32_nan_cases :
    f32Add .RN 0x7F800001#32 0x3F800000#32 = (0x7FC00001#32, Flags.invalidOnly) ∧
    f32Add .RN 0x3F800000#32 0xFF800005#32 = (0xFFC00005#32, Flags.invalidOnly) ∧
    f32Add .RN 0x7FC00011#32 0x7F800022#32 = (0x7FC00022#32, Flags.invalidOnly) ∧
    f32Add .RN 0x7F800033#32 0x7F800022#32 = (0x7FC00033#32, Flags.invalidOnly) ∧
    f32Mul .RN 0x3F800000#32 0x7FC00011#32 = (0x7FC00011#32, Flags.none) ∧
    f32Div .RN 0x7FC00002#32 0x7FC00001#32 = (0x7FC00002#32, Flags.none) ∧
    f32Sqrt .RN 0x7F800022#32 = (0x7FC00022#32, Flags.invalidOnly) ∧
    f32Sqrt .RN 0xFFC00077#32 = (0xFFC00077#32, Flags.none) ∧
    -- an invalid operation without NaN operands creates the default QNaN 0x7fc00000 (Table 6.3)
    f32Sub .RN 0x7F800000#32 0x7F800000#32 = (defaultQNaN32, Flags.invalidOnly) := by
  decide +kernel

/-- Square root: √2 in the four modes; √4 exact; `√−0 = −0`; `√+∞ = +∞`;
the smallest subnormal. -/
theorem f32Sqrt_cases :
    f32Sqrt .RN 0x40000000#32 = (0x3FB504F3#32, Flags.inexactOnly) ∧
    f32Sqrt .RZ 0x40000000#32 = (0x3FB504F3#32, Flags.inexactOnly) ∧
    f32Sqrt .RP 0x40000000#32 = (0x3FB504F4#32, Flags.inexactOnly) ∧
    f32Sqrt .RM 0x40000000#32 = (0x3FB504F3#32, Flags.inexactOnly) ∧
    f32Sqrt .RN 0x40800000#32 = (0x40000000#32, Flags.none) ∧
    f32Sqrt .RN 0x80000000#32 = (0x80000000#32, Flags.none) ∧
    f32Sqrt .RN 0x7F800000#32 = (0x7F800000#32, Flags.none) ∧
    f32Sqrt .RN 0x00000001#32 = (0x1A3504F3#32, Flags.inexactOnly) := by
  decide +kernel

/-- `recip` and `rsqrt` (model pin: `1.0 / x`, `1.0 / sqrt x`). -/
theorem f32_recip_rsqrt_cases :
    f32Recip .RN 0x40400000#32 = (0x3EAAAAAB#32, Flags.inexactOnly) ∧
    f32Recip .RZ 0x40400000#32 = (0x3EAAAAAA#32, Flags.inexactOnly) ∧
    f32Recip .RN 0x00000000#32 = (0x7F800000#32, { divZero := true }) ∧
    f32Recip .RN 0x7F800000#32 = (0x00000000#32, Flags.none) ∧
    f32Rsqrt .RN 0x40800000#32 = (0x3F000000#32, Flags.none) ∧
    f32Rsqrt .RN 0x40000000#32 = (0x3F3504F3#32, Flags.inexactOnly) ∧
    f32Rsqrt .RN 0x00000000#32 = (0x7F800000#32, { divZero := true }) ∧
    f32Rsqrt .RN 0x80000000#32 = (0xFF800000#32, { divZero := true }) ∧
    f32Rsqrt .RN 0xBF800000#32 = (defaultQNaN32, Flags.invalidOnly) := by
  decide +kernel

/-- Double precision in the four modes: 1 + 2^−53 (a tie), 1/3, √2, overflow
of 2 × largest, underflow of half the smallest subnormal, and specials. -/
theorem f64_arith_cases :
    f64Add .RN 0x3FF0000000000000#64 0x3CA0000000000000#64 = (0x3FF0000000000000#64, Flags.inexactOnly) ∧
    f64Add .RP 0x3FF0000000000000#64 0x3CA0000000000000#64 = (0x3FF0000000000001#64, Flags.inexactOnly) ∧
    f64Div .RN 0x3FF0000000000000#64 0x4008000000000000#64 = (0x3FD5555555555555#64, Flags.inexactOnly) ∧
    f64Div .RP 0x3FF0000000000000#64 0x4008000000000000#64 = (0x3FD5555555555556#64, Flags.inexactOnly) ∧
    f64Sqrt .RN 0x4000000000000000#64 = (0x3FF6A09E667F3BCD#64, Flags.inexactOnly) ∧
    f64Sqrt .RZ 0x4000000000000000#64 = (0x3FF6A09E667F3BCC#64, Flags.inexactOnly) ∧
    f64Sqrt .RP 0x4000000000000000#64 = (0x3FF6A09E667F3BCD#64, Flags.inexactOnly) ∧
    f64Sqrt .RM 0x4000000000000000#64 = (0x3FF6A09E667F3BCC#64, Flags.inexactOnly) ∧
    f64Mul .RN 0x7FEFFFFFFFFFFFFF#64 0x4000000000000000#64 =
      (0x7FF0000000000000#64, { overflow := true, inexact := true }) ∧
    f64Mul .RZ 0x7FEFFFFFFFFFFFFF#64 0x4000000000000000#64 =
      (0x7FEFFFFFFFFFFFFF#64, { overflow := true, inexact := true }) ∧
    f64Mul .RN 0x0000000000000001#64 0x3FE0000000000000#64 =
      (0x0000000000000000#64, { underflow := true, inexact := true }) ∧
    f64Mul .RP 0x0000000000000001#64 0x3FE0000000000000#64 =
      (0x0000000000000001#64, { underflow := true, inexact := true }) ∧
    f64Sub .RN 0x7FF0000000000000#64 0x7FF0000000000000#64 = (defaultQNaN64, Flags.invalidOnly) ∧
    f64Div .RN 0x3FF0000000000000#64 0x0000000000000000#64 =
      (0x7FF0000000000000#64, { divZero := true }) ∧
    f64Add .RN 0x7FF8000000000000#64 0x7FF0000000000001#64 =
      (0x7FF8000000000001#64, Flags.invalidOnly) ∧
    f64Rsqrt .RN 0x4010000000000000#64 = (0x3FE0000000000000#64, Flags.none) ∧
    f64Recip .RN 0x4000000000000000#64 = (0x3FE0000000000000#64, Flags.none) ∧
    f64Sub .RM 0x4000000000000000#64 0x4000000000000000#64 = (0x8000000000000000#64, Flags.none) := by
  decide +kernel

/-- `isqrt` on small inputs and at perfect-square boundaries. -/
theorem isqrt_cases :
    (List.range 17).map isqrt = [0, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 4] ∧
    isqrt (2 ^ 64) = 2 ^ 32 ∧ isqrt (2 ^ 64 - 1) = 2 ^ 32 - 1 ∧
    isqrt (10 ^ 40) = 10 ^ 20 ∧ isqrt (10 ^ 40 + 2 * 10 ^ 20) = 10 ^ 20 := by
  decide +kernel

end Theorems

end Mips.Fp
