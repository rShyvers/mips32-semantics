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

/-- The default QNaNs are quiet NaNs in the legacy encoding, and fixed points
of canonicalisation. -/
theorem defaultQNaN_facts :
    isQNaN32 defaultQNaN32 = true ∧ isSNaN32 defaultQNaN32 = false ∧
    isQNaN64 defaultQNaN64 = true ∧ isSNaN64 defaultQNaN64 = false ∧
    canonNaN32 defaultQNaN32 = defaultQNaN32 ∧ canonNaN64 defaultQNaN64 = defaultQNaN64 ∧
    BitVec.ofNat 32 binary32.defaultQNaN = defaultQNaN32 ∧
    BitVec.ofNat 64 binary64.defaultQNaN = defaultQNaN64 := by decide

/-- Lean's canonical `Float32` NaN `0x7FC00000` is *signaling* in the legacy
encoding, which is why `canonNaN32` is needed. -/
theorem hostNaN_is_legacy_signaling :
    isSNaN32 0x7FC00000#32 = true ∧ canonNaN32 0x7FC00000#32 = 0x7FBFFFFF#32 ∧
    isSNaN64 0x7FF8000000000000#64 = true ∧
    canonNaN64 0x7FF8000000000000#64 = 0x7FF7FFFFFFFFFFFF#64 := by decide

/-- The `C.cond.fmt` formula. -/
theorem fpCompare_eq (cond : BitVec 4) (un lt eq : Bool) :
    fpCompare cond un lt eq =
      ((cond.getLsbD 0 && un) || (cond.getLsbD 1 && eq) || (cond.getLsbD 2 && lt)) := rfl

/-- Float → word of any NaN, in any rounding mode: `0x7FFFFFFF`, Invalid. -/
theorem f32ToW32_of_nan (rm : RoundingMode) (x : BitVec 32) (h : isNaN32 x = true) :
    f32ToW32 rm x = (0x7FFFFFFF#32, Flags.invalidOnly) := by
  simp only [isNaN32] at h
  simp [f32ToW32, Format.toW32, h]

/-- Float → word of ±∞, in any rounding mode: `0x7FFFFFFF`, Invalid. -/
theorem f32ToW32_of_inf (rm : RoundingMode) (x : BitVec 32) (h : isInf32 x = true) :
    f32ToW32 rm x = (0x7FFFFFFF#32, Flags.invalidOnly) := by
  simp only [isInf32] at h
  simp [f32ToW32, Format.toW32, h]

/-- Double → word of any NaN, in any rounding mode: `0x7FFFFFFF`, Invalid. -/
theorem f64ToW32_of_nan (rm : RoundingMode) (x : BitVec 64) (h : isNaN64 x = true) :
    f64ToW32 rm x = (0x7FFFFFFF#32, Flags.invalidOnly) := by
  simp only [isNaN64] at h
  simp [f64ToW32, Format.toW32, h]

/-- Double → word of ±∞, in any rounding mode: `0x7FFFFFFF`, Invalid. -/
theorem f64ToW32_of_inf (rm : RoundingMode) (x : BitVec 64) (h : isInf64 x = true) :
    f64ToW32 rm x = (0x7FFFFFFF#32, Flags.invalidOnly) := by
  simp only [isInf64] at h
  simp [f64ToW32, Format.toW32, h]

/-- The only flags float → word can ever raise are Invalid and Inexact, never
both. -/
theorem f32ToW32_flags (rm : RoundingMode) (x : BitVec 32) :
    (f32ToW32 rm x).2 = Flags.none ∨ (f32ToW32 rm x).2 = Flags.invalidOnly ∨
      (f32ToW32 rm x).2 = Flags.inexactOnly := by
  unfold f32ToW32 Format.toW32
  split
  · simp
  · dsimp only
    split
    · simp
    · split <;> simp

/-- `abs`/`neg` of a NaN signal Invalid; a quiet NaN is returned unchanged, a
signaling NaN gives the default QNaN. -/
theorem f32Abs_of_nan (x : BitVec 32) (h : isNaN32 x = true) :
    f32Abs x = (if isQNaN32 x then x else defaultQNaN32, Flags.invalidOnly) ∧
      f32Neg x = (if isQNaN32 x then x else defaultQNaN32, Flags.invalidOnly) := by
  simp [f32Abs, f32Neg, h]

/-- `abs`/`neg` of a non-NaN only touch the sign bit and raise nothing. -/
theorem f32Abs_of_not_nan (x : BitVec 32) (h : isNaN32 x = false) :
    f32Abs x = (x &&& 0x7FFFFFFF#32, Flags.none) ∧
      f32Neg x = (x ^^^ 0x80000000#32, Flags.none) := by
  simp [f32Abs, f32Neg, h]

/-- `abs`/`neg` of a double NaN signal Invalid; a quiet NaN is returned
unchanged, a signaling NaN gives the default QNaN. -/
theorem f64Abs_of_nan (x : BitVec 64) (h : isNaN64 x = true) :
    f64Abs x = (if isQNaN64 x then x else defaultQNaN64, Flags.invalidOnly) ∧
      f64Neg x = (if isQNaN64 x then x else defaultQNaN64, Flags.invalidOnly) := by
  simp [f64Abs, f64Neg, h]

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

theorem f32ToW32_special :
    f32ToW32 .RN 0x7FBFFFFF#32 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧  -- QNaN
    f32ToW32 .RZ 0x7FC00000#32 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧  -- SNaN
    f32ToW32 .RZ 0xFFC00000#32 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧  -- −NaN
    f32ToW32 .RN 0x7F800000#32 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧  -- +∞
    f32ToW32 .RM 0xFF800000#32 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧  -- −∞
    f32ToW32 .RZ 0x4F32D05E#32 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧  -- 3e9
    f32ToW32 .RZ 0xCF32D05E#32 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧  -- −3e9
    f32ToW32 .RN 0xCF32D05E#32 = (0x7FFFFFFF#32, Flags.invalidOnly) := by decide

theorem f32ToW32_ties_to_even :
    f32ToW32 .RN 0x40200000#32 = (2#32, Flags.inexactOnly) ∧            -- 2.5 → 2
    f32ToW32 .RN 0x40600000#32 = (4#32, Flags.inexactOnly) ∧            -- 3.5 → 4
    f32ToW32 .RN 0xC0200000#32 = (0xFFFFFFFE#32, Flags.inexactOnly) ∧   -- −2.5 → −2
    f32ToW32 .RN 0x3F000000#32 = (0#32, Flags.inexactOnly) ∧            -- 0.5 → 0
    f32ToW32 .RN 0x3FC00000#32 = (2#32, Flags.inexactOnly) := by decide -- 1.5 → 2

theorem f32ToW32_directed :
    f32ToW32 .RZ 0x40200000#32 = (2#32, Flags.inexactOnly) ∧            -- trunc 2.5
    f32ToW32 .RP 0x40200000#32 = (3#32, Flags.inexactOnly) ∧            -- ceil 2.5
    f32ToW32 .RM 0x40200000#32 = (2#32, Flags.inexactOnly) ∧            -- floor 2.5
    f32ToW32 .RZ 0xC0200000#32 = (0xFFFFFFFE#32, Flags.inexactOnly) ∧   -- trunc −2.5
    f32ToW32 .RP 0xC0200000#32 = (0xFFFFFFFE#32, Flags.inexactOnly) ∧   -- ceil −2.5
    f32ToW32 .RM 0xC0200000#32 = (0xFFFFFFFD#32, Flags.inexactOnly) := by decide

theorem f32ToW32_zero_and_exact :
    f32ToW32 .RN 0x80000000#32 = (0#32, Flags.none) ∧                   -- −0.0
    f32ToW32 .RM 0x80000000#32 = (0#32, Flags.none) ∧
    f32ToW32 .RN 0x00000000#32 = (0#32, Flags.none) ∧
    f32ToW32 .RN 0x40400000#32 = (3#32, Flags.none) ∧                   -- 3.0
    f32ToW32 .RP 0x00000001#32 = (1#32, Flags.inexactOnly) ∧            -- ceil 2^−149
    f32ToW32 .RM 0x80000001#32 = (0xFFFFFFFF#32, Flags.inexactOnly) :=  -- floor −2^−149
  by decide

theorem f32ToW32_boundaries :
    f32ToW32 .RN 0x4EFFFFFF#32 = (0x7FFFFF80#32, Flags.none) ∧          -- 2147483520
    f32ToW32 .RN 0x4F000000#32 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧   -- 2^31
    f32ToW32 .RN 0xCF000000#32 = (0x80000000#32, Flags.none) ∧          -- −2^31 exactly
    f32ToW32 .RZ 0xCF000000#32 = (0x80000000#32, Flags.none) ∧
    f32ToW32 .RZ 0xCF000001#32 = (0x7FFFFFFF#32, Flags.invalidOnly) := by decide

/-! Double → word.  Constants: `0x41DFFFFFFFC00000` = 2147483647.0,
`0x41DFFFFFFFE00000` = 2147483647.5, `0x41E0000000000000` = 2^31,
`0xC1E0000000000000` = −2^31, `0xC1E0000000100000` = −2147483648.5,
`0xC1E0000000200000` = −2147483649.0, `0x4004000000000000` = 2.5. -/

theorem f64ToW32_boundaries :
    -- 2^31 − 1 exactly: a *valid* 0x7FFFFFFF, no flag
    f64ToW32 .RN 0x41DFFFFFFFC00000#64 = (0x7FFFFFFF#32, Flags.none) ∧
    -- 2^31 − 0.5: valid when rounded down, Invalid when rounded up to 2^31
    f64ToW32 .RZ 0x41DFFFFFFFE00000#64 = (0x7FFFFFFF#32, Flags.inexactOnly) ∧
    f64ToW32 .RM 0x41DFFFFFFFE00000#64 = (0x7FFFFFFF#32, Flags.inexactOnly) ∧
    f64ToW32 .RN 0x41DFFFFFFFE00000#64 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧
    f64ToW32 .RP 0x41DFFFFFFFE00000#64 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧
    f64ToW32 .RZ 0x41E0000000000000#64 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧
    -- −2^31 exactly: valid
    f64ToW32 .RN 0xC1E0000000000000#64 = (0x80000000#32, Flags.none) ∧
    -- −2^31 − 0.5: valid when rounded toward zero / to even, Invalid toward −∞
    f64ToW32 .RZ 0xC1E0000000100000#64 = (0x80000000#32, Flags.inexactOnly) ∧
    f64ToW32 .RN 0xC1E0000000100000#64 = (0x80000000#32, Flags.inexactOnly) ∧
    f64ToW32 .RP 0xC1E0000000100000#64 = (0x80000000#32, Flags.inexactOnly) ∧
    f64ToW32 .RM 0xC1E0000000100000#64 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧
    f64ToW32 .RZ 0xC1E0000000200000#64 = (0x7FFFFFFF#32, Flags.invalidOnly) := by decide

theorem f64ToW32_misc :
    f64ToW32 .RN 0x4004000000000000#64 = (2#32, Flags.inexactOnly) ∧    -- 2.5 → 2
    f64ToW32 .RP 0x4004000000000000#64 = (3#32, Flags.inexactOnly) ∧
    f64ToW32 .RN 0x7FF7FFFFFFFFFFFF#64 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧
    f64ToW32 .RN 0xFFF0000000000000#64 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧
    f64ToW32 .RZ 0x7E37E43C8800759C#64 = (0x7FFFFFFF#32, Flags.invalidOnly) ∧  -- 1e300
    f64ToW32 .RN 0x8000000000000000#64 = (0#32, Flags.none) := by decide +kernel

/-! ### Format conversions: concrete cases -/

theorem f32ToF64_cases :
    f32ToF64 0x3F800000#32 = (0x3FF0000000000000#64, Flags.none) ∧      -- 1.0
    f32ToF64 0x00000001#32 = (0x36A0000000000000#64, Flags.none) ∧      -- 2^−149
    f32ToF64 0x7F800000#32 = (0x7FF0000000000000#64, Flags.none) ∧      -- +∞
    f32ToF64 0xFF800000#32 = (0xFFF0000000000000#64, Flags.none) ∧      -- −∞
    f32ToF64 0x80000000#32 = (0x8000000000000000#64, Flags.none) ∧      -- −0
    f32ToF64 0x7F7FFFFF#32 = (0x47EFFFFFE0000000#64, Flags.none) ∧      -- max finite
    -- QNaN: sign and payload preserved (widened with zeros)
    f32ToF64 0x7FBFFFFF#32 = (0x7FF7FFFFE0000000#64, Flags.none) ∧
    f32ToF64 0xFF800001#32 = (0xFFF0000020000000#64, Flags.none) ∧
    f32ToF64 0x7FC00000#32 = (defaultQNaN64, Flags.invalidOnly) := by decide  -- SNaN

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
    -- QNaN: sign and the top 23 payload bits preserved …
    f64ToF32 .RN 0x7FF7FFFFFFFFFFFF#64 = (defaultQNaN32, Flags.none) ∧
    f64ToF32 .RN 0xFFF4000000000000#64 = (0xFFA00000#32, Flags.none) ∧
    -- … unless they are all zero (would be ∞): default QNaN
    f64ToF32 .RN 0xFFF0000000000001#64 = (defaultQNaN32, Flags.none) ∧
    f64ToF32 .RN 0x7FF8000000000000#64 = (defaultQNaN32, Flags.invalidOnly) := by decide +kernel

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

/-! ### Classification and `abs`/`neg` -/

theorem classify_cases :
    isNaN32 0x7F800001#32 = true ∧ isQNaN32 0x7F800001#32 = true ∧
    isSNaN32 0x7FC00000#32 = true ∧ isQNaN32 0x7FC00000#32 = false ∧
    isNaN32 0x7F800000#32 = false ∧ isInf32 0xFF800000#32 = true ∧
    isZero32 0x80000000#32 = true ∧ isSubnormal32 0x007FFFFF#32 = true ∧
    isSubnormal32 0x00800000#32 = false ∧
    sign32 0xBF800000#32 = true ∧ expField32 0xBF800000#32 = 127 ∧
    fracField32 0x3FC00000#32 = 0x400000 ∧
    toExact32 0xC0200000#32 = ⟨true, 0xA00000, -22⟩ ∧                   -- −2.5
    toExact32 0x00000001#32 = ⟨false, 1, -149⟩ ∧
    isSNaN64 0x7FF8000000000000#64 = true ∧ isQNaN64 0x7FF0000000000001#64 = true ∧
    isInf64 0x7FF0000000000000#64 = true ∧ isSubnormal64 1#64 = true ∧
    expField64 0x3FF0000000000000#64 = 1023 ∧
    toExact64 0x3FF8000000000000#64 = ⟨false, 0x18000000000000, -52⟩ := by decide +kernel

theorem absNeg_cases :
    f32Abs 0xBF800000#32 = (0x3F800000#32, Flags.none) ∧
    f32Neg 0x3F800000#32 = (0xBF800000#32, Flags.none) ∧
    f32Neg 0x00000000#32 = (0x80000000#32, Flags.none) ∧
    f32Abs 0xFF800000#32 = (0x7F800000#32, Flags.none) ∧
    f32Abs 0xFFBFFFFF#32 = (0xFFBFFFFF#32, Flags.invalidOnly) ∧          -- QNaN: unchanged
    f32Neg 0x7FC00000#32 = (defaultQNaN32, Flags.invalidOnly) ∧          -- SNaN

    f64Abs 0xBFF0000000000000#64 = (0x3FF0000000000000#64, Flags.none) ∧
    f64Neg 0x3FF0000000000000#64 = (0xBFF0000000000000#64, Flags.none) ∧
    f64Neg 0x7FF0000000000001#64 = (0x7FF0000000000001#64, Flags.invalidOnly) ∧  -- QNaN
    f64Abs 0xFFF8000000000000#64 = (defaultQNaN64, Flags.invalidOnly) := by decide

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
    f32Compare Cond.ult 0x7FBFFFFF#32 0x3F800000#32 = (true, Flags.none) ∧
    f32Compare Cond.eq 0x7FBFFFFF#32 0x3F800000#32 = (false, Flags.none) ∧
    f32Compare Cond.lt 0x7FBFFFFF#32 0x3F800000#32 = (false, Flags.invalidOnly) ∧
    f32Compare Cond.ngt 0x7FBFFFFF#32 0x3F800000#32 = (true, Flags.invalidOnly) ∧
    -- signaling NaN: always raises
    f32Compare Cond.un 0x7FC00000#32 0x3F800000#32 = (true, Flags.invalidOnly) ∧
    f64Compare Cond.le 0x3FF0000000000000#64 0x3FF0000000000000#64 = (true, Flags.none) ∧
    f64Compare Cond.sf 0x7FF7FFFFFFFFFFFF#64 0#64 = (false, Flags.invalidOnly) := by decide

/-! ### FCSR -/

/-- Condition-code bit positions: FCC0 ↔ bit 23, FCC1 ↔ bit 25, …, FCC7 ↔
bit 31 (bit 24 is FS, not a condition code). -/
theorem ccBit_positions :
    [ccBit 0, ccBit 1, ccBit 2, ccBit 3, ccBit 4, ccBit 5, ccBit 6, ccBit 7] =
      [23, 25, 26, 27, 28, 29, 30, 31] := by decide

theorem setCC_cases :
    setCC 0#32 0 true = 0x00800000#32 ∧ setCC 0#32 1 true = 0x02000000#32 ∧
    setCC 0#32 7 true = 0x80000000#32 ∧
    setCC 0xFFFFFFFF#32 0 false = 0xFF7FFFFF#32 ∧
    setCC 0xFFFFFFFF#32 1 false = 0xFDFFFFFF#32 ∧
    setCC 0xFFFFFFFF#32 7 false = 0x7FFFFFFF#32 ∧
    getCC 0x00800000#32 0 = true ∧ getCC 0x01000000#32 0 = false ∧
    getCC 0x01000000#32 1 = false ∧ getCC 0x02000000#32 1 = true ∧
    getCC 0x80000000#32 7 = true ∧ getCC 0x7FFFFFFF#32 7 = false := by decide

/-- Reading back a condition code just written. -/
theorem getCC_setCC (fcsr : BitVec 32) (cc : Fin 8) (b : Bool) :
    getCC (setCC fcsr cc b) cc = b := by
  have hcc : ccBit cc < 32 := by unfold ccBit; split <;> omega
  cases b <;> simp [getCC, setCC, hcc]

/-- Writing one condition code leaves the others alone. -/
theorem getCC_setCC_ne (fcsr : BitVec 32) (cc cc' : Fin 8) (b : Bool) (h : cc ≠ cc') :
    getCC (setCC fcsr cc b) cc' = getCC fcsr cc' := by
  have hne : ccBit cc ≠ ccBit cc' := by
    unfold ccBit
    intro heq
    apply h
    apply Fin.ext
    split at heq <;> split at heq <;> omega
  have hcc : ccBit cc' < 32 := by unfold ccBit; split <;> omega
  cases b <;> simp [getCC, setCC, hcc] <;> omega

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

theorem control_register_cases :
    readControl 0xFFFFFFFF#32 0 = some 0x00130000#32 ∧                  -- FIR
    readControl 0xFFFFFFFF#32 31 = some 0xFF83FFFF#32 ∧                 -- FCSR
    readControl 0xFFFFFFFF#32 25 = some 0x000000FF#32 ∧                 -- FCCR
    readControl 0xFFFFFFFF#32 26 = some 0x0003F07C#32 ∧                 -- FEXR
    readControl 0xFFFFFFFF#32 28 = some 0x00000F87#32 ∧                 -- FENR
    readControl 0xFFFFFFFF#32 1 = none ∧
    -- FCCR bit n ↔ FCCn
    readFCCR 0x00800000#32 = 0x01#32 ∧ readFCCR 0x02000000#32 = 0x02#32 ∧
    readFCCR 0x80000000#32 = 0x80#32 ∧ readFCCR 0x01000000#32 = 0x00#32 ∧
    -- FENR bit 2 ↔ FS (FCSR bit 24)
    readFENR 0x01000000#32 = 0x04#32 ∧
    -- writes touch only their own fields
    writeControl 0#32 31 0xFFFFFFFF#32 = some 0xFF83FFFF#32 ∧
    writeControl 0#32 25 0xFFFFFFFF#32 = some 0xFE800000#32 ∧
    writeControl 0#32 26 0xFFFFFFFF#32 = some 0x0003F07C#32 ∧
    writeControl 0#32 28 0xFFFFFFFF#32 = some 0x01000F83#32 ∧
    writeControl 0xFFFFFFFF#32 25 0#32 = some 0x017FFFFF#32 ∧
    writeControl 0xFFFFFFFF#32 26 0#32 = some 0xFFFC0F83#32 ∧
    writeControl 0xFFFFFFFF#32 28 0#32 = some 0xFEFFF07C#32 ∧
    writeControl 0xFFFFFFFF#32 31 0#32 = some 0#32 ∧
    writeControl 0x12345678#32 0 0xFFFFFFFF#32 = some 0x12345678#32 ∧   -- FIR read-only
    writeControl 0#32 2 0#32 = none ∧
    -- CTC1 can raise a pending enabled exception
    fcsrTrapPending 0x00010800#32 = true ∧ fcsrTrapPending 0x00010000#32 = false ∧
    fcsrTrapPending 0x00020000#32 = true ∧ fcsrTrapPending 0x00000F80#32 = false := by decide

/-- Each `CTC1` view reads back what was written (on the bits that view
exposes). -/
theorem control_read_write (fcsr v : BitVec 32) :
    readFCSR (writeFCSR fcsr v) = v &&& fcsrWritableMask ∧
    readFEXR (writeFEXR fcsr v) = v &&& (fcsrCauseMask ||| fcsrFlagsMask) := by
  constructor
  · ext i hi; simp [readFCSR, writeFCSR]
  · have hm : ~~~(fcsrCauseMask ||| fcsrFlagsMask) &&& (fcsrCauseMask ||| fcsrFlagsMask) = 0#32 := by
      decide
    simp only [readFEXR, writeFEXR]
    rw [BitVec.and_or_distrib_right, BitVec.and_assoc, hm, BitVec.and_zero, BitVec.zero_or,
      BitVec.and_assoc, BitVec.and_self]

/-! ### `fpUpdate`, condition codes -/

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

/-- Recording an operation's exceptions leaves every condition code alone. -/
theorem getCC_raiseFlags (fcsr : BitVec 32) (f : Flags) (cc : Fin 8) :
    getCC (raiseFlags fcsr f) cc = getCC fcsr cc := by
  have hbit : (~~~(fcsrCauseMask ||| fcsrFlagsMask)).getLsbD (ccBit cc) = true := by
    revert cc; decide
  have h := congrArg (fun x => x.getLsbD (ccBit cc)) (raiseFlags_frame fcsr f)
  simp only [BitVec.getLsbD_and, hbit, Bool.and_true] at h
  exact h

/-- **A compare writes exactly its condition code.** After recording the
flags `f` and storing `b` in condition code `cc`, `cc` reads `b` and every
other condition code is unchanged. -/
theorem getCC_setCC_raiseFlags (fcsr : BitVec 32) (f : Flags) (cc cc' : Fin 8) (b : Bool) :
    getCC (setCC (raiseFlags fcsr f) cc b) cc' = if cc' = cc then b else getCC fcsr cc' := by
  by_cases h : cc' = cc
  · subst h; simp [getCC_setCC]
  · rw [getCC_setCC_ne _ _ _ _ (fun h' => h h'.symm), getCC_raiseFlags]; simp [h]

/-- `CTC1`/`CFC1` on register 31 round-trip every non-reserved FCSR bit. -/
theorem readControl_writeControl_fcsr (fcsr v : BitVec 32) :
    (writeControl fcsr 31 v).bind (fun x => readControl x 31) = some (v &&& fcsrWritableMask) := by
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

/-- **A quiet NaN first operand is the result** of `add`/`sub`/`mul`/`div`,
unchanged; Invalid is signaled iff the other operand is a signaling NaN
(MD00082 Vol I-A Rev 6.01 §6.3.1.5, p.82). -/
theorem f32_arith_qnan_left (e : Env) (a b : BitVec 32) (h : isQNaN32 a = true) :
    f32Add e a b = (a, { invalid := isSNaN32 b }) ∧ f32Sub e a b = (a, { invalid := isSNaN32 b }) ∧
    f32Mul e a b = (a, { invalid := isSNaN32 b }) ∧ f32Div e a b = (a, { invalid := isSNaN32 b }) := by
  have h1 := isNaN_of_isQNaN binary32 a.toNat h
  have h2 := isSNaN_false_of_isQNaN binary32 a.toNat h
  have hq : binary32.isQNaN a.toNat = true := h
  simp [f32Add, f32Sub, f32Mul, f32Div, Format.add, Format.sub, Format.mul, Format.div,
    Format.nanResult, Format.nanFlags, h1, h2, hq, isSNaN32]

/-- Double-precision form of `f32_arith_qnan_left`. -/
theorem f64_arith_qnan_left (e : Env) (a b : BitVec 64) (h : isQNaN64 a = true) :
    f64Add e a b = (a, { invalid := isSNaN64 b }) ∧ f64Sub e a b = (a, { invalid := isSNaN64 b }) ∧
    f64Mul e a b = (a, { invalid := isSNaN64 b }) ∧ f64Div e a b = (a, { invalid := isSNaN64 b }) := by
  have h1 := isNaN_of_isQNaN binary64 a.toNat h
  have h2 := isSNaN_false_of_isQNaN binary64 a.toNat h
  have hq : binary64.isQNaN a.toNat = true := h
  simp [f64Add, f64Sub, f64Mul, f64Div, Format.add, Format.sub, Format.mul, Format.div,
    Format.nanResult, Format.nanFlags, h1, h2, hq, isSNaN64]

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
  simp [f32Add, f32Sub, f32Mul, f32Div, Format.add, Format.sub, Format.mul, Format.div,
    Format.nanFlags, hn', hs]

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

/-- NaN operands (legacy encoding: `0x7F800123` quiet, `0x7FC00000`
signaling): a quiet NaN is copied — the first one in operand order if both
are quiet, and also when the other operand is signaling (then with Invalid);
a signaling NaN with no quiet NaN to copy gives the default QNaN. -/
theorem f32_nan_cases :
    f32Add .RN 0x7F800123#32 0x3F800000#32 = (0x7F800123#32, Flags.none) ∧
    f32Add .RN 0x3F800000#32 0xFF800123#32 = (0xFF800123#32, Flags.none) ∧
    f32Add .RN 0x7FC00000#32 0x7F800123#32 = (0x7F800123#32, Flags.invalidOnly) ∧
    f32Add .RN 0x7FC00000#32 0x3F800000#32 = (defaultQNaN32, Flags.invalidOnly) ∧
    f32Mul .RN 0x7F800001#32 0x7F800002#32 = (0x7F800001#32, Flags.none) ∧
    f32Div .RN 0x7F800002#32 0x7F800001#32 = (0x7F800002#32, Flags.none) ∧
    f32Sqrt .RN 0xFF800077#32 = (0xFF800077#32, Flags.none) ∧
    f32Sqrt .RN 0xFFC00077#32 = (defaultQNaN32, Flags.invalidOnly) := by
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

/-- The multiply-add family is **unfused**: (1 + 2^−23)² = 1 + 2^−22 + 2^−46
is first rounded to 1 + 2^−22 (`0x3F800002`, Inexact), so adding
−(1 + 2^−22) gives +0, where a fused operation would give 2^−46.
`nmadd`/`nmsub` negate with the arithmetic `NEG`: 2 × 3 + 1 ↦ −7,
2 × 3 − 1 ↦ −5, and a quiet NaN addend comes back unchanged with Invalid. -/
theorem f32_madd_cases :
    f32Mul .RN 0x3F800001#32 0x3F800001#32 = (0x3F800002#32, Flags.inexactOnly) ∧
    f32Madd .RN 0xBF800002#32 0x3F800001#32 0x3F800001#32 = (0x00000000#32, Flags.inexactOnly) ∧
    f32Msub .RN 0x3F800002#32 0x3F800001#32 0x3F800001#32 = (0x00000000#32, Flags.inexactOnly) ∧
    f32Nmadd .RN 0x3F800000#32 0x40000000#32 0x40400000#32 = (0xC0E00000#32, Flags.none) ∧
    f32Nmsub .RN 0x3F800000#32 0x40000000#32 0x40400000#32 = (0xC0A00000#32, Flags.none) ∧
    f32Nmadd .RN 0x7F800001#32 0x40000000#32 0x40400000#32 = (0x7F800001#32, Flags.invalidOnly) := by
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
      (0x7FF0000000000001#64, Flags.invalidOnly) ∧
    f64Madd .RN 0xBFF0000000000002#64 0x3FF0000000000001#64 0x3FF0000000000001#64 =
      (0x0000000000000000#64, Flags.inexactOnly) ∧
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
