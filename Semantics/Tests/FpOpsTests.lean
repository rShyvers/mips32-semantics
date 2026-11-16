import Semantics.FpOps

/-!
# Differential tests for `Semantics/FpOps.lean` against Lean's `Float32` / `Float`

Formerly §11 of `Semantics/FpOps.lean`. This is the only place where the host's
floating point appears: it is an oracle for `#guard`s, never part of a definition.

Release 6 FPU (`FCSR.NAN2008 = ABS2008 = 1`): NaNs use the IEEE 754-2008 encoding (quiet bit = the
fraction MSB set), so the host's NaN classification agrees with the model's; the default QNaN is
`0x7FC00000` (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82), the host's NaN pattern up to the sign bit;
an invalid conversion to a fixed point format gives 0 for a NaN and the saturated integer otherwise
(same table); `abs`/`neg` only change the sign bit (MD00086 Vol II-A Rev 6.06, ABS.fmt p.32, NEG.fmt
p.307). The conversions take FCSR.FS as an explicit flush flag (`false` below unless stated).
-/

namespace Mips.Fp

/-! ## §11  Differential tests against Lean's `Float32` / `Float`

`#guard`s (evaluated by the compiler, so the host's IEEE hardware is the
oracle) comparing the definitions above with Lean's native floating point
wherever the two are supposed to agree.  Lean has no directed-rounding or
ties-to-even primitives, so for those the oracle is derived from the
round-to-nearest result (`dirOracle`) or from `floor`/`round` plus an explicit
tie fix-up (`rnOracle…`). -/

namespace Test

/-- Bits → host single. -/
def toF32 (x : BitVec 32) : Float32 := Float32.ofBits x.toNat.toUInt32
/-- Host single → bits. -/
def ofF32 (f : Float32) : BitVec 32 := BitVec.ofNat 32 f.toBits.toNat
/-- Bits → host double. -/
def toF64 (x : BitVec 64) : Float := Float.ofBits x.toNat.toUInt64
/-- Host double → bits. -/
def ofF64 (f : Float) : BitVec 64 := BitVec.ofNat 64 f.toBits.toNat

/-- `n` pseudo-random 32-bit patterns (Numerical Recipes LCG). -/
def lcg32 : Nat → Nat → List (BitVec 32)
  | 0, _ => []
  | n + 1, s =>
    let s' := (s * 1664525 + 1013904223) % 2 ^ 32
    BitVec.ofNat 32 s' :: lcg32 n s'

/-- `n` pseudo-random 64-bit patterns (Knuth MMIX LCG). -/
def lcg64 : Nat → Nat → List (BitVec 64)
  | 0, _ => []
  | n + 1, s =>
    let s' := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    BitVec.ofNat 64 s' :: lcg64 n s'

/-- Hand-picked single patterns: zeros, subnormals, extreme normals, powers of
two ± 1 ulp, the 2^31 neighbourhood, infinities, NaNs of both kinds. -/
def edge32 : List (BitVec 32) :=
  [0x00000000, 0x80000000, 0x00000001, 0x80000001, 0x00000002, 0x007FFFFF, 0x807FFFFF,
   0x00800000, 0x80800000, 0x00800001, 0x7F7FFFFF, 0xFF7FFFFF, 0x7F7FFFFE,
   0x3F800000, 0xBF800000, 0x3F7FFFFF, 0x3F800001, 0xBF7FFFFF, 0xBF800001,
   0x3F000000, 0xBF000000, 0x3EFFFFFF, 0x3F000001, 0xBEFFFFFF, 0xBF000001,
   0x3FC00000, 0xBFC00000, 0x40200000, 0xC0200000, 0x40600000, 0xC0600000,
   0x40000000, 0x3FFFFFFF, 0x40000001, 0x4B000000, 0x4AFFFFFF, 0x4B000001,
   0x4B800000, 0x4B7FFFFF, 0x4B800001, 0xCB000000, 0xCAFFFFFF, 0xCB7FFFFF,
   0x4F000000, 0x4EFFFFFF, 0x4F000001, 0xCF000000, 0xCEFFFFFF, 0xCF000001,
   0x4F32D05E, 0xCF32D05E, 0x4F800000, 0x5F000000, 0xDF000000,
   0x7F800000, 0xFF800000, 0x7FBFFFFF, 0x7FC00000, 0xFFC00000, 0x7F800001, 0xFFFFFFFF]

/-- Singles `n/4` for `n ∈ [-200, 200]`: integers, quarters and exact halves. -/
def quarters32 : List (BitVec 32) :=
  (List.range 401).map fun (n : Nat) => ofF32 ((Float32.ofInt ((n : Int) - 200)) / 4.0)

/-- Random singles of moderate magnitude with fractional parts (so that the
float → word tests mostly exercise the in-range path). -/
def moderate32 : List (BitVec 32) :=
  (lcg32 200 7).map fun r => ofF32 ((Int32.ofBitVec r).toFloat32 / 1024.0)

/-- All single test patterns (≈ 960). -/
def pats32 : List (BitVec 32) := edge32 ++ quarters32 ++ moderate32 ++ lcg32 300 12345

/-- Integer test patterns for word → float. -/
def ints32 : List (BitVec 32) :=
  [0, 1, 2, 3, 0xFFFFFFFF, 0xFFFFFFFE, 0x7FFFFFFF, 0x80000000, 0x80000001, 0x7FFFFFFE,
   0x00FFFFFF, 0x01000000, 0x01000001, 0x01000002, 0x01000003, 0x01FFFFFF, 0x02000001,
   0x02000002, 0x02000003, 0x02000005, 0x02000006, 0x02000007, 0xFEFFFFFF, 0xFF000000,
   0xFEFFFFFD, 0x7FFFFF80, 0x7FFFFFC0, 0x7FFFFFBF, 0x7FFFFFC1, 0x80000040, 0x80000080,
   0x800000C0, 0x80000041] ++ lcg32 300 99

/-- Hand-picked double patterns. -/
def edge64 : List (BitVec 64) :=
  [0x0000000000000000, 0x8000000000000000, 0x0000000000000001, 0x8000000000000001,
   0x000FFFFFFFFFFFFF, 0x0010000000000000, 0x7FEFFFFFFFFFFFFF, 0xFFEFFFFFFFFFFFFF,
   0x3FF0000000000000, 0xBFF0000000000000, 0x3FEFFFFFFFFFFFFF, 0x3FF0000000000001,
   0x3FE0000000000000, 0xBFE0000000000000, 0x3FDFFFFFFFFFFFFF, 0x3FE0000000000001,
   0x4004000000000000, 0xC004000000000000, 0x400C000000000000,
   -- the 2^31 neighbourhood
   0x41DFFFFFFFC00000, 0x41DFFFFFFFE00000, 0x41DFFFFFFFDFFFFF, 0x41DFFFFFFFE00001,
   0x41DFFFFFFFFFFFFF, 0x41E0000000000000, 0xC1E0000000000000, 0xC1E0000000000001,
   0xC1E00000000FFFFF, 0xC1E0000000100000, 0xC1E0000000100001, 0xC1E00000001FFFFF,
   0xC1E0000000200000, 0xC1DFFFFFFFFFFFFF,
   -- single-precision ties, overflow and underflow thresholds
   0x3FF0000010000000, 0x3FF0000010000001, 0x3FF000000FFFFFFF, 0x3FF0000030000000,
   0x47EFFFFFE0000000, 0x47EFFFFFEFFFFFFF, 0x47EFFFFFF0000000, 0x47EFFFFFF0000001,
   0x47F0000000000000, 0xC7EFFFFFF0000000, 0xC7EFFFFFEFFFFFFF, 0x7E37E43C8800759C,
   0x3810000000000000, 0x380FFFFFFFFFFFFF, 0x380FFFFFF0000000, 0x380FFFFFEFFFFFFF,
   0x380FFFFFE0000000, 0x380FFFFFD0000000, 0xB80FFFFFFFFFFFFF, 0xB80FFFFFF0000000,
   0x36A0000000000000, 0x3690000000000000, 0x3690000000000001, 0x368FFFFFFFFFFFFF,
   0x36A8000000000000, 0x36B8000000000000, 0xB690000000000000, 0xB690000000000001,
   0x3730000000000000, 0x3730000000400000, 0x0000000000000400, 0x1E37E43C8800759C,
   0x7FF0000000000000, 0xFFF0000000000000, 0x7FF7FFFFFFFFFFFF, 0x7FF8000000000000,
   0xFFF8000000000000, 0x7FF0000000000001, 0xFFFFFFFFFFFFFFFF]

/-- Doubles in a 2-single-ulp window around each finite single test pattern:
the single itself, ± 1 double ulp, the halfway points to both neighbours
(± 2^28 double ulps) and those ± 1. -/
def nearSingles64 : List (BitVec 64) :=
  (pats32.filter fun x => !isNaN32 x && !isInf32 x && !isZero32 x).flatMap fun x =>
    let d := ofF64 (toF32 x).toFloat
    [d, d + 1, d - 1, d + 0x10000000, d + 0x0FFFFFFF, d + 0x10000001,
     d - 0x10000000, d - 0x0FFFFFFF, d - 0x10000001, d + 0x08000000, d - 0x18000000]

/-- Doubles `n/4`, and random doubles of moderate magnitude with fractions. -/
def moderate64 : List (BitVec 64) :=
  ((List.range 401).map fun (n : Nat) => ofF64 ((Float.ofInt ((n : Int) - 200)) / 4.0)) ++
  ((lcg32 300 31).map fun r => ofF64 ((Int32.ofBitVec r).toFloat / 1024.0)) ++
  ((lcg32 100 32).map fun r => ofF64 ((Int32.ofBitVec r).toFloat + 0.5)) ++
  ((lcg32 100 33).map fun r => ofF64 ((Int32.ofBitVec r).toFloat * 1.75))

/-- All double test patterns (≈ 11 000). -/
def pats64 : List (BitVec 64) := edge64 ++ moderate64 ++ lcg64 300 2024 ++ nearSingles64

/-- Next single bit pattern toward +∞ (not used on −0). -/
def nextUp32 (b : BitVec 32) : BitVec 32 := if b.msb then b - 1 else b + 1
/-- Next single bit pattern toward −∞ (not used on +0). -/
def nextDown32 (b : BitVec 32) : BitVec 32 := if b.msb then b + 1 else b - 1

/-- Directed-rounding oracle.  `n` is the round-to-nearest single result for
an exact source value whose double image is `src` (`neg` its sign): if `n` is
exact all modes agree, otherwise the source lies strictly between `n` and one
neighbour, which fixes the RP / RM / RZ results. -/
def dirOracle (rm : RoundingMode) (n : BitVec 32) (src : Float) (neg : Bool) : BitVec 32 :=
  let back := (toF32 n).toFloat
  if back == src then n else
  let down := if back < src then n else nextDown32 n
  let up := if back < src then nextUp32 n else n
  match rm with
  | .RN => n
  | .RZ => if neg then up else down
  | .RP => up
  | .RM => down

/-- Overflow oracle for double → single: the finite source, rounded to 24 bits
with unbounded exponent range, has magnitude ≥ 2^128.  Under RN that starts
at 2^128 − 2^103 (halfway past the largest single, which rounds up); when
rounding away from zero, just above the largest single; when rounding toward
zero, at 2^128 itself. -/
def overflowOracle (rm : RoundingMode) (src : Float) : Bool :=
  let maxSingle := (toF32 0x7F7FFFFF#32).toFloat
  let halfway := toF64 0x47EFFFFFF0000000#64
  let two128 := toF64 0x47F0000000000000#64
  let a := src.abs
  let away : Bool := a > maxSingle
  let toward : Bool := a ≥ two128
  src.isFinite &&
    match rm with
    | .RN => a ≥ halfway
    | .RZ => toward
    | .RP => if src < 0.0 then toward else away
    | .RM => if src < 0.0 then away else toward

/-! ### Classification -/

#guard pats32.all fun x =>
  isNaN32 x == (toF32 x).isNaN && isInf32 x == (toF32 x).isInf &&
  (!isNaN32 x && !isInf32 x) == (toF32 x).isFinite &&
  isZero32 x == (toF32 x == 0.0) &&
  (isNaN32 x == (isQNaN32 x || isSNaN32 x)) && !(isQNaN32 x && isSNaN32 x) &&
  -- 2008 encoding: a NaN is quiet iff the fraction MSB (bit 22) is set
  (!isNaN32 x || isQNaN32 x == x.getLsbD 22)

#guard pats64.all fun x =>
  isNaN64 x == (toF64 x).isNaN && isInf64 x == (toF64 x).isInf &&
  isZero64 x == (toF64 x == 0.0) &&
  (isNaN64 x == (isQNaN64 x || isSNaN64 x)) && !(isQNaN64 x && isSNaN64 x) &&
  (!isNaN64 x || isQNaN64 x == x.getLsbD 51)

/-! ### `f32ToF64` vs `Float32.toFloat` (exact, never raises on non-NaN) -/

#guard pats32.all fun x =>
  isNaN32 x || f32ToF64 false x == (ofF64 (toF32 x).toFloat, Flags.none)

-- a NaN keeps its sign and payload (widened), made quiet; Invalid iff it was signaling
#guard pats32.all fun x =>
  !isNaN32 x || isQNaN64 (f32ToF64 false x).1 && (toF32 x).toFloat.isNaN &&
    (f32ToF64 false x).2.invalid == isSNaN32 x &&
    (f32ToF64 false x).1 ==
      ((x.zeroExtend 64 &&& 0x80000000#64) <<< 32 ||| 0x7FF8000000000000#64 |||
        ((x.zeroExtend 64 &&& 0x003FFFFF#64) <<< 29))

-- FCSR.FS = 1: a subnormal operand is converted as a zero of the same sign, and the flush signals
-- Inexact (MD00082 Vol I-A Rev 6.01 §6.7.2.4, p.102)
#guard pats32.all fun x =>
  f32ToF64 true x ==
    (let r := f32ToF64 false (if isSubnormal32 x then x &&& 0x80000000#32 else x)
     (r.1, if isSubnormal32 x then r.2.or Flags.inexactOnly else r.2))

/-! ### `f64ToF32` vs `Float.toFloat32` -/

-- round to nearest even: value
#guard pats64.all fun d =>
  isNaN64 d || (f64ToF32 .RN d).1 == ofF32 (toF64 d).toFloat32

-- directed modes: value
#guard pats64.all fun d =>
  isNaN64 d || [RoundingMode.RZ, .RP, .RM].all fun rm =>
    (f64ToF32 rm d).1 == dirOracle rm (ofF32 (toF64 d).toFloat32) (toF64 d) (sign64 d)

-- flags (all modes): Inexact iff the result differs from the source; Overflow
-- iff the source rounded with unbounded exponent range would reach 2^128
-- (`overflowOracle`); Underflow whenever an inexact result is subnormal or zero, never when it is
-- above the smallest normal (the result *equal* to the smallest normal is the
-- tininess-after-rounding corner, pinned by `f64ToF32_cases` instead)
#guard pats64.all fun d =>
  isNaN64 d || [RoundingMode.RN, .RZ, .RP, .RM].all fun rm =>
    let r := f64ToF32 rm d
    let exact := (toF32 r.1).toFloat == toF64 d
    let big := overflowOracle rm (toF64 d)
    let small := isSubnormal32 r.1 || isZero32 r.1
    let aboveMin := (toF32 r.1).abs > toF32 0x00800000#32
    r.2.inexact == !exact && r.2.overflow == big && !r.2.invalid && !r.2.divZero &&
      (!small || r.2.underflow == !exact) && (!aboveMin || !r.2.underflow)

/-! ### `w32ToF32` / `w32ToF64` vs `Int32.toFloat32` / `Int32.toFloat` -/

#guard ints32.all fun i => w32ToF64 i == ofF64 (Int32.ofBitVec i).toFloat

#guard ints32.all fun i => (w32ToF32 .RN i).1 == ofF32 (Int32.ofBitVec i).toFloat32

#guard ints32.all fun i =>
  [RoundingMode.RN, .RZ, .RP, .RM].all fun rm =>
    let r := w32ToF32 rm i
    let src := (Int32.ofBitVec i).toFloat
    r.1 == dirOracle rm (ofF32 (Int32.ofBitVec i).toFloat32) src i.msb &&
      r.2 == { inexact := (toF32 r.1).toFloat != src }

/-! ### Float → word vs `toInt32` ∘ `floor` / `ceil` / `round` -/

/-- Expected float → word result given the already-rounded (integral, or
NaN/∞) host double `r` and whether the source was integral. -/
def w32Oracle (r : Float) (srcIntegral : Bool) : BitVec 32 × Flags :=
  if r.isNaN then (0#32, Flags.invalidOnly)
  else if r < -2147483648.0 then (0x80000000#32, Flags.invalidOnly)
  else if r > 2147483647.0 then (0x7FFFFFFF#32, Flags.invalidOnly)
  else (r.toInt32.toBitVec, if srcIntegral then Flags.none else Flags.inexactOnly)

/-- As `w32Oracle`, for a 64-bit longword (`2^63` itself is out of range). -/
def w64Oracle (r : Float) (srcIntegral : Bool) : BitVec 64 × Flags :=
  if r.isNaN then (0#64, Flags.invalidOnly)
  else if r < -9223372036854775808.0 then (0x8000000000000000#64, Flags.invalidOnly)
  else if r ≥ 9223372036854775808.0 then (0x7FFFFFFFFFFFFFFF#64, Flags.invalidOnly)
  else (r.toInt64.toBitVec, if srcIntegral then Flags.none else Flags.inexactOnly)

/-- Round-half-even on a host double, from `floor`. -/
def rnOracle (f : Float) : Float :=
  let lo := f.floor
  let diff := f - lo  -- exact
  if diff < 0.5 then lo
  else if diff > 0.5 then lo + 1.0
  else if (lo / 2.0).floor * 2.0 == lo then lo else lo + 1.0

/-- Truncation on a host double. -/
def rzOracle (f : Float) : Float := if f < 0.0 then f.ceil else f.floor

#guard pats64.all fun d =>
  let f := toF64 d
  let integral := f.floor == f
  f64ToW32 .RZ false d == w32Oracle (rzOracle f) integral &&
  f64ToW32 .RM false d == w32Oracle f.floor integral &&
  f64ToW32 .RP false d == w32Oracle f.ceil integral &&
  f64ToW32 .RN false d == w32Oracle (rnOracle f) integral

-- singles: widen exactly with the host, then use the same oracles
#guard pats32.all fun x =>
  let f := (toF32 x).toFloat
  let integral := f.floor == f
  f32ToW32 .RZ false x == w32Oracle (rzOracle f) integral &&
  f32ToW32 .RM false x == w32Oracle f.floor integral &&
  f32ToW32 .RP false x == w32Oracle f.ceil integral &&
  f32ToW32 .RN false x == w32Oracle (rnOracle f) integral

-- direct comparison with the host's own truncating conversion, in range
#guard pats32.all fun x =>
  let f := toF32 x
  !(f.abs < 2147483648.0) || (f32ToW32 .RZ false x).1 == f.toInt32.toBitVec

#guard pats64.all fun d =>
  let f := toF64 d
  !(f.abs < 2147483648.0) || (f64ToW32 .RZ false d).1 == f.toInt32.toBitVec

-- … and with the host's `floor`/`ceil` on singles (the functions the old
-- model used), where the result is in range
#guard pats32.all fun x =>
  let f := toF32 x
  !(f.abs < 2147483000.0) ||
    ((f32ToW32 .RM false x).1 == f.floor.toInt32.toBitVec &&
     (f32ToW32 .RP false x).1 == f.ceil.toInt32.toBitVec)

/-! ### Float → longword vs `toInt64` ∘ `floor` / `ceil` / `round` (CVT/ROUND/TRUNC/CEIL/FLOOR.L) -/

#guard pats64.all fun d =>
  let f := toF64 d
  let integral := f.floor == f
  f64ToW64 .RZ false d == w64Oracle (rzOracle f) integral &&
  f64ToW64 .RM false d == w64Oracle f.floor integral &&
  f64ToW64 .RP false d == w64Oracle f.ceil integral &&
  f64ToW64 .RN false d == w64Oracle (rnOracle f) integral

#guard pats32.all fun x =>
  let f := (toF32 x).toFloat
  let integral := f.floor == f
  f32ToW64 .RZ false x == w64Oracle (rzOracle f) integral &&
  f32ToW64 .RM false x == w64Oracle f.floor integral &&
  f32ToW64 .RP false x == w64Oracle f.ceil integral &&
  f32ToW64 .RN false x == w64Oracle (rnOracle f) integral

-- FCSR.FS = 1 flushes a subnormal operand first: ceil of the smallest subnormal is 1, or 0 (and the
-- flush signals Inexact, §6.7.2.4, p.102)
#guard f32ToW32 .RP false 0x00000001#32 == (1#32, Flags.inexactOnly) &&
  f32ToW32 .RP true 0x00000001#32 == (0#32, Flags.inexactOnly) &&
  f64ToW64 .RM false 0x8000000000000001#64 == (0xFFFFFFFFFFFFFFFF#64, Flags.inexactOnly) &&
  f64ToW64 .RM true 0x8000000000000001#64 == (0#64, Flags.inexactOnly) &&
  f64ToW64 .RM true 0x0000000000000000#64 == (0#64, Flags.none)

/-! ### Longword → float vs `Int64.toFloat` / `Int64.toFloat32` (CVT.D.L, CVT.S.L) -/

/-- Longword test patterns: small, around 2^24 / 2^53 / 2^63, and random. -/
def ints64 : List (BitVec 64) :=
  ([0, 1, 2, 0xFFFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0x8000000000000001,
   0x0000000001000001, 0x0000000001000003, 0x0020000000000001, 0x0020000000000003,
   0x0020000000000002, 0xFFDFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFC00, 0x7FFFFFFFFFFFFDFF,
   0x7FFFFF8000000000, 0x7FFFFFBFFFFFFFFF, 0x7FFFFFC000000000] : List (BitVec 64)) ++ lcg64 300 4711 ++
  ((lcg64 100 17).map fun (r : BitVec 64) => r >>> 20) ++
  ((lcg32 100 3).map fun (r : BitVec 32) => r.signExtend 64)

#guard ints64.all fun i =>
  (w64ToF64 .RN i).1 == ofF64 (Int64.ofBitVec i).toFloat &&
  (w64ToF32 .RN i).1 == ofF32 (Int64.ofBitVec i).toFloat32

-- Inexact iff the result differs from the integer (exact comparison through the host's in-range
-- conversion back); no other flag
#guard ints64.all fun i =>
  [RoundingMode.RN, .RZ, .RP, .RM].all fun rm =>
    let r := w64ToF64 rm i
    let exact := i == 0x8000000000000000#64 ||
      (toF64 r.1 < 9223372036854775808.0 && (toF64 r.1).toInt64.toBitVec == i)
    r.2 == { inexact := !exact }

-- directed modes for longword → double bracket the round-to-nearest result
#guard ints64.all fun i =>
  let n := (w64ToF64 .RN i).1
  let lo := (w64ToF64 .RM i).1
  let hi := (w64ToF64 .RP i).1
  toF64 lo ≤ toF64 n && toF64 n ≤ toF64 hi &&
    ((w64ToF64 .RN i).2.inexact || (lo == n && hi == n))

/-! ### Relations vs `Float32` / `Float` `<`, `==` -/

#guard (edge32 ++ lcg32 40 5).all fun a => (edge32 ++ lcg32 40 6).all fun b =>
  let r := f32Relation a b
  r.unordered == ((toF32 a).isNaN || (toF32 b).isNaN) &&
  r.less == decide (toF32 a < toF32 b) && r.equal == (toF32 a == toF32 b) &&
  fpCompare Cond.ole r.unordered r.less r.equal == decide (toF32 a ≤ toF32 b) &&
  fpCompare Cond.ueq r.unordered r.less r.equal == (r.unordered || toF32 a == toF32 b)

#guard (edge64 ++ lcg64 40 5).all fun a => (edge64 ++ lcg64 40 6).all fun b =>
  let r := f64Relation a b
  r.unordered == ((toF64 a).isNaN || (toF64 b).isNaN) &&
  r.less == decide (toF64 a < toF64 b) && r.equal == (toF64 a == toF64 b) &&
  fpCompare Cond.ole r.unordered r.less r.equal == decide (toF64 a ≤ toF64 b)

/-! ### `abs` / `neg` vs the host, and NaN canonicalisation of host results -/

#guard pats32.all fun x =>
  isNaN32 x || (f32Abs x == ofF32 (toF32 x).abs && f32Neg x == ofF32 (-(toF32 x)))

#guard pats64.all fun d =>
  isNaN64 d || (f64Abs d == ofF64 (toF64 d).abs && f64Neg d == ofF64 (-(toF64 d)))

-- non-arithmetic (`ABS2008 = 1`): on every pattern, NaNs included, only the sign bit changes
#guard pats32.all fun x =>
  f32Abs x == x &&& 0x7FFFFFFF#32 && f32Neg x == x ^^^ 0x80000000#32
#guard pats64.all fun d =>
  f64Abs d == d &&& 0x7FFFFFFFFFFFFFFF#64 && f64Neg d == d ^^^ 0x8000000000000000#64

-- host-generated NaNs (0/0, ∞ − ∞, sqrt(−1)) canonicalise to the default QNaN, which is the
-- host's NaN up to the sign bit
#guard (ofF32 ((0.0 : Float32) / 0.0)) &&& 0x7FFFFFFF#32 == defaultQNaN32 &&
  (ofF64 ((0.0 : Float) / 0.0)) &&& 0x7FFFFFFFFFFFFFFF#64 == defaultQNaN64
#guard canonNaN32 (ofF32 ((0.0 : Float32) / 0.0)) == defaultQNaN32 &&
  canonNaN32 (ofF32 (toF32 0x7F800000#32 - toF32 0x7F800000#32)) == defaultQNaN32 &&
  canonNaN64 (ofF64 ((0.0 : Float) / 0.0)) == defaultQNaN64 &&
  canonNaN64 (ofF64 (Float.sqrt (-1.0))) == defaultQNaN64

/-! ### `add` / `sub` / `mul` / `div` / `sqrt` vs the host's IEEE arithmetic

Under round-to-nearest the model must agree **bit for bit** with the host on
every non-NaN result, and produce a quiet NaN exactly when the host does. The NaN *pattern* is
checked against the manual's rule, not the host's (whose operand choice is not IEEE-specified):
the first signaling NaN operand made quiet, else the first quiet NaN operand, else the default
QNaN (MD00082 Vol I-A Rev 6.01 §6.3.1.5, Table 6.3, p.82; operand order is a model pin,
SPEC-NOTES). -/

/-- Operand pairs: every pair of hand-picked edge patterns (≈ 3 700), random
pairs, and moderate × random pairs. -/
def pairs32 : List (BitVec 32 × BitVec 32) :=
  (edge32.flatMap fun a => edge32.map fun b => (a, b)) ++
  ((lcg32 400 77).zip (lcg32 400 78)) ++ (moderate32.zip (lcg32 200 5)) ++
  (moderate32.zip (moderate32.drop 7))

/-- Double operand pairs (≈ 5 500 edge pairs + random + moderate). -/
def pairs64 : List (BitVec 64 × BitVec 64) :=
  (edge64.flatMap fun a => edge64.map fun b => (a, b)) ++
  ((lcg64 400 77).zip (lcg64 400 78)) ++ (moderate64.zip (moderate64.drop 13))

/-- Agreement of a model single result with a host result. -/
def agree32 (m : BitVec 32) (h : Float32) : Bool :=
  if h.isNaN then isQNaN32 m else m == ofF32 h
/-- Agreement of a model double result with a host result. -/
def agree64 (m : BitVec 64) (h : Float) : Bool :=
  if h.isNaN then isQNaN64 m else m == ofF64 h

#guard pairs32.all fun (a, b) =>
  agree32 (f32Add .RN a b).1 (toF32 a + toF32 b) && agree32 (f32Sub .RN a b).1 (toF32 a - toF32 b) &&
  agree32 (f32Mul .RN a b).1 (toF32 a * toF32 b) && agree32 (f32Div .RN a b).1 (toF32 a / toF32 b)

#guard pairs64.all fun (a, b) =>
  agree64 (f64Add .RN a b).1 (toF64 a + toF64 b) && agree64 (f64Sub .RN a b).1 (toF64 a - toF64 b) &&
  agree64 (f64Mul .RN a b).1 (toF64 a * toF64 b) && agree64 (f64Div .RN a b).1 (toF64 a / toF64 b)

#guard pats32.all fun a => agree32 (f32Sqrt .RN a).1 (toF32 a).sqrt
#guard pats64.all fun a => agree64 (f64Sqrt .RN a).1 (toF64 a).sqrt

-- `recip` / `rsqrt` are `1/x` and `1/sqrt x` computed with two host operations
#guard pats32.all fun a =>
  agree32 (f32Recip .RN a).1 (1.0 / toF32 a) && agree32 (f32Rsqrt .RN a).1 (1.0 / (toF32 a).sqrt)
#guard (edge64 ++ moderate64).all fun a =>
  agree64 (f64Recip .RN a).1 (1.0 / toF64 a) && agree64 (f64Rsqrt .RN a).1 (1.0 / (toF64 a).sqrt)

-- NaN results: the propagation rule above, bit for bit
/-- The expected NaN result of a two-operand single operation (see the section comment). -/
def nan32 (a b : BitVec 32) : BitVec 32 :=
  if isSNaN32 a then a ||| 0x00400000#32 else if isSNaN32 b then b ||| 0x00400000#32
  else if isNaN32 a then a else if isNaN32 b then b else defaultQNaN32
/-- The expected NaN result of a two-operand double operation. -/
def nan64 (a b : BitVec 64) : BitVec 64 :=
  if isSNaN64 a then a ||| 0x0008000000000000#64 else if isSNaN64 b then b ||| 0x0008000000000000#64
  else if isNaN64 a then a else if isNaN64 b then b else defaultQNaN64

#guard pairs32.all fun (a, b) =>
  [(f32Add .RN a b).1, (f32Sub .RN a b).1, (f32Mul .RN a b).1, (f32Div .RN a b).1].all fun r =>
    !isNaN32 r || r == nan32 a b
#guard pairs64.all fun (a, b) =>
  [(f64Add .RN a b).1, (f64Sub .RN a b).1, (f64Mul .RN a b).1, (f64Div .RN a b).1].all fun r =>
    !isNaN64 r || r == nan64 a b
-- the Invalid flag of an operation with a NaN operand: set iff a signaling NaN is among them
#guard pairs32.all fun (a, b) =>
  !(isNaN32 a || isNaN32 b) || (f32Add .RN a b).2.invalid == (isSNaN32 a || isSNaN32 b)

-- Single multiply, directed modes and flags: the product of two singles is
-- exact in double precision (48 significant bits, exponent well in range), so
-- `dirOracle` applies; Inexact iff the delivered single differs from it;
-- Overflow as for double → single; Invalid iff 0 × ∞ or a signaling NaN.
#guard pairs32.all fun (a, b) =>
  isNaN32 a || isNaN32 b || (isInf32 a || isInf32 b) ||
  [RoundingMode.RN, .RZ, .RP, .RM].all fun rm =>
    let exact := (toF32 a).toFloat * (toF32 b).toFloat
    let r := f32Mul rm a b
    r.1 == dirOracle rm (ofF32 (toF32 a * toF32 b)) exact (sign32 a != sign32 b) &&
      r.2.inexact == ((toF32 r.1).toFloat != exact) &&
      r.2.overflow == overflowOracle rm exact && !r.2.invalid && !r.2.divZero

-- Single add/sub, directed modes: whenever the double-precision sum is exact
-- (checked with the error term of Knuth's TwoSum) and nonzero.
#guard pairs32.all fun (a, b) =>
  isNaN32 a || isNaN32 b || isInf32 a || isInf32 b ||
  let x := (toF32 a).toFloat
  let y := (toF32 b).toFloat
  let s := x + y
  let bb := s - x
  let err := (x - (s - bb)) + (y - bb)
  err != 0.0 || s == 0.0 ||
  [RoundingMode.RN, .RZ, .RP, .RM].all fun rm =>
    let r := f32Add rm a b
    r.1 == dirOracle rm (ofF32 (toF32 a + toF32 b)) s (s < 0.0) &&
      r.2.inexact == ((toF32 r.1).toFloat != s)

-- Flags of invalid / divide-by-zero cases against the host's NaN / ∞ results
#guard pairs32.all fun (a, b) =>
  isNaN32 a || isNaN32 b ||
  ((f32Div .RN a b).2.invalid == (toF32 a / toF32 b).isNaN &&
   (f32Div .RN a b).2.divZero == ((toF32 a).isFinite && (toF32 a / toF32 b).isInf && isZero32 b) &&
   (f32Mul .RN a b).2.invalid == (toF32 a * toF32 b).isNaN &&
   (f32Add .RN a b).2.invalid == (toF32 a + toF32 b).isNaN &&
   (f32Sub .RN a b).2.invalid == (toF32 a - toF32 b).isNaN)

end Test

end Mips.Fp

-- BEGIN R6-6A
/-! ## `MADDF.fmt` / `MSUBF.fmt` (`f32Fma`, `f64Fma`; MD00086 Vol II-A Rev 6.06, p.259-260)

`fma e sub c a b` is `c + a·b` (`sub = false`, MADDF) or `c − a·b` (MSUBF), `c` = fd, `a` = fs,
`b` = ft. The explicit cases below were also run on QEMU `mips32r6-generic` (a scratch MADDF/MSUBF
program through the `scripts/oracle.py` harness, 2026-11-16), which gave the same results and Cause
bits, except where noted. -/

namespace Mips.Fp

namespace Test

/-- `(sub, FCSR environment, c, a, b, expected result, expected flags)` for `f32Fma`. -/
def fma32Cases : List (Bool × Env × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × Flags) :=
  [ -- ∞ × 0 + QNaN: the QNaN, and Invalid (pin; QEMU agrees)
    (false, Env.RN, 0x7FC12345, 0x7F800000, 0x00000000, 0x7FC12345, ({ invalid := true } : Flags)),
    (false, Env.RN, 0x7FC12345, 0x00000000, 0xFF800000, 0x7FC12345, ({ invalid := true } : Flags)),
    -- ∞ × 0 + SNaN: the SNaN made quiet, Invalid
    (false, Env.RN, 0x7F812345, 0x7F800000, 0x00000000, 0x7FC12345, ({ invalid := true } : Flags)),
    -- NaN order [fd, fs, ft], the first signaling NaN first
    (false, Env.RN, 0x7FC11111, 0x7F822222, 0x3F800000, 0x7FC22222, ({ invalid := true } : Flags)),
    (false, Env.RN, 0x7F811111, 0x7FC22222, 0x3F800000, 0x7FC11111, ({ invalid := true } : Flags)),
    (false, Env.RN, 0x7FC11111, 0x7FC22222, 0x3F800000, 0x7FC11111, Flags.none),
    (false, Env.RN, 0x3F800000, 0x7FC22222, 0x7F833333, 0x7FC33333, ({ invalid := true } : Flags)),
    (false, Env.RN, 0x3F800000, 0x7FC22222, 0x7FC33333, 0x7FC22222, Flags.none),
    -- MSUBF does not negate a NaN
    (true, Env.RN, 0xFFC11111, 0x3F800000, 0x3F800000, 0xFFC11111, Flags.none),
    -- fused ≠ unfused: (1 + 2^-23)(1 - 2^-24) - 1 = 2^-24 - 2^-47, exact (the product alone rounds to 1)
    (false, Env.RN, 0xBF800000, 0x3F800001, 0x3F7FFFFF, 0x337FFFFE, Flags.none),
    -- exact zero: +0 in RN, −0 in RM (opposite-signed terms); equal-signed zero terms keep the sign
    (true, Env.RN, 0x3F800000, 0x3F800000, 0x3F800000, 0x00000000, Flags.none),
    (true, Env.RM, 0x3F800000, 0x3F800000, 0x3F800000, 0x80000000, Flags.none),
    (false, Env.RN, 0x80000000, 0x00000000, 0x40A00000, 0x00000000, Flags.none),
    (false, Env.RN, 0x80000000, 0x80000000, 0x40A00000, 0x80000000, Flags.none),
    (true, Env.RN, 0x80000000, 0x00000000, 0x40A00000, 0x80000000, Flags.none),
    -- (+∞) + (+∞ × −1) and +∞ + ∞ × 0: Invalid, the default QNaN
    (false, Env.RN, 0x7F800000, 0x7F800000, 0xBF800000, 0x7FC00000, ({ invalid := true } : Flags)),
    (false, Env.RN, 0x7F800000, 0x7F800000, 0x00000000, 0x7FC00000, ({ invalid := true } : Flags)),
    -- (+∞) + (+∞ × +1): +∞; −∞ + finite: −∞; both exact
    (false, Env.RN, 0x7F800000, 0x7F800000, 0x3F800000, 0x7F800000, Flags.none),
    (false, Env.RN, 0xFF800000, 0x3F800000, 0x3F800000, 0xFF800000, Flags.none),
    -- overflow (Overflow + Inexact), tiny inexact result (Underflow + Inexact)
    (false, Env.RN, 0x00000000, 0x7F7FFFFF, 0x40000000, 0x7F800000, ({ overflow := true, inexact := true } : Flags)),
    (false, Env.RN, 0x00000000, 0x00800001, 0x3E800000, 0x00200000, ({ underflow := true, inexact := true } : Flags)),
    -- FCSR.FS = 0: 1 + 2^-149 rounds to 1, Inexact
    (false, Env.RN, 0x3F800000, 0x00000001, 0x3F800000, 0x3F800000, ({ inexact := true } : Flags)),
    -- FCSR.FS = 1: the subnormal operand is flushed, 1 + 0 = 1 exactly, and the flush signals Inexact
    -- ("Inexact may be signaled both by input flushing and/or by the fused-multiply-add", MADDF.fmt
    -- p.260; MD00082 Vol I-A Rev 6.01 §6.7.2.4 p.102)
    (false, ({ flush := true } : Env), 0x3F800000, 0x00000001, 0x3F800000, 0x3F800000, Flags.inexactOnly),
    (false, ({ flush := true } : Env), 0x00000001, 0x3F800000, 0x3F800000, 0x3F800000, Flags.inexactOnly),
    -- FCSR.FS = 1 and no subnormal operand: no flush, exact
    (false, ({ flush := true } : Env), 0x3F800000, 0x3F800000, 0x3F800000, 0x40000000, Flags.none) ]

#guard fma32Cases.all fun (sub, e, c, a, b, r, fl) => f32Fma e sub c a b == (r, fl)

-- fused differs from MUL then ADD (two roundings) on the same operands
#guard (f32Add .RN (f32Mul .RN 0x3F800001#32 0x3F7FFFFF#32).1 0xBF800000#32).1 == 0x00000000#32

-- binary64: the double-rounding case and ∞ × 0 + QNaN (both as on QEMU)
#guard f64Fma .RN false 0xBFF0000000000000#64 0x3FF0000000000001#64 0x3FEFFFFFFFFFFFFF#64 ==
  (0x3C9FFFFFFFFFFFFE#64, Flags.none)
#guard f64Fma .RN false 0x7FF8000000012345#64 0x7FF0000000000000#64 0#64 ==
  (0x7FF8000000012345#64, Flags.invalidOnly)
#guard (f64Add .RN (f64Mul .RN 0x3FF0000000000001#64 0x3FEFFFFFFFFFFFFF#64).1
  0xBFF0000000000000#64).1 == 0#64

-- Against the host, round to nearest: the product of two singles is exact in double precision; when
-- `c ± a·b` is also exact in double (Knuth's TwoSum error term is 0), rounding it to single once is the
-- correctly rounded fused result (zeros included: the host's zero sign follows the same IEEE rule).
#guard pairs32.all fun (a, b) =>
  isNaN32 a || isNaN32 b || isInf32 a || isInf32 b ||
  [0x00000000#32, 0x80000000#32, 0x3F800000#32, 0xBF800000#32, 0x00800000#32, 0x4B000001#32].all fun c =>
  [false, true].all fun sub =>
    let x := (toF32 c).toFloat
    let p := (toF32 a).toFloat * (toF32 b).toFloat
    let y := if sub then -p else p
    let s := x + y
    let bb := s - x
    let err := (x - (s - bb)) + (y - bb)
    err != 0.0 ||
      let r := f32Fma .RN sub c a b
      r.1 == ofF32 s.toFloat32 && r.2.inexact == ((toF32 r.1).toFloat != s) && !r.2.invalid

end Test

end Mips.Fp
-- END R6-6A
-- BEGIN R6-6C
/-! ## Release 6: `CMP.condn.fmt`, `MAX/MIN/MAXA/MINA.fmt`, `CLASS.fmt`, `RINT.fmt`

Hand-computed expectations (MD00086 Vol II-A Rev 6.06: CMP.condn.fmt Table 3.9 p.138-139; MAX/MIN
Table 4.1 p.264-265; CLASS.fmt p.132; RINT.fmt p.337). -/

namespace Mips.Fp.TestR6C

-- single-precision patterns
def pz : BitVec 32 := 0x00000000#32
def nz : BitVec 32 := 0x80000000#32
def one : BitVec 32 := 0x3F800000#32
def mone : BitVec 32 := 0xBF800000#32
def two : BitVec 32 := 0x40000000#32
def mtwo : BitVec 32 := 0xC0000000#32
def three : BitVec 32 := 0x40400000#32
def mthree : BitVec 32 := 0xC0400000#32
def half : BitVec 32 := 0x3F000000#32
def mhalf : BitVec 32 := 0xBF000000#32
def onehalf : BitVec 32 := 0x3FC00000#32
def twohalf : BitVec 32 := 0x40200000#32
def mtwohalf : BitVec 32 := 0xC0200000#32
def mpoint3 : BitVec 32 := 0xBE99999A#32
def pinf : BitVec 32 := 0x7F800000#32
def ninf : BitVec 32 := 0xFF800000#32
def qnan1 : BitVec 32 := 0x7FC00001#32
def qnan2 : BitVec 32 := 0x7FC00002#32
def snan : BitVec 32 := 0x7F800001#32
def psub : BitVec 32 := 0x00000001#32
def nsub : BitVec 32 := 0x80000001#32
def big : BitVec 32 := 0x4E800000#32   -- 2^30, an integer

def flushEnv : Env := { flush := true }

/-! ### MAX/MIN/MAXA/MINA -/

-- Table 4.1: signed zeros, both operand orders
#guard (f32MinMax .max .RN nz pz).1 == pz && (f32MinMax .max .RN pz nz).1 == pz
#guard (f32MinMax .min .RN nz pz).1 == nz && (f32MinMax .min .RN pz nz).1 == nz
#guard (f32MinMax .maxa .RN nz pz).1 == pz && (f32MinMax .maxa .RN pz nz).1 == pz
#guard (f32MinMax .mina .RN nz pz).1 == nz && (f32MinMax .mina .RN pz nz).1 == nz
-- ordinary values
#guard (f32MinMax .max .RN mone two).1 == two && (f32MinMax .min .RN mone two).1 == mone
#guard (f32MinMax .maxa .RN mthree two).1 == mthree && (f32MinMax .mina .RN mthree two).1 == two
-- equal magnitudes: MAXA returns the larger, MINA the smaller (p.264)
#guard (f32MinMax .maxa .RN mtwo two).1 == two && (f32MinMax .maxa .RN two mtwo).1 == two
#guard (f32MinMax .mina .RN mtwo two).1 == mtwo && (f32MinMax .mina .RN two mtwo).1 == mtwo
-- infinities
#guard (f32MinMax .max .RN ninf one).1 == one && (f32MinMax .min .RN ninf one).1 == ninf
#guard (f32MinMax .maxa .RN ninf one).1 == ninf && (f32MinMax .mina .RN ninf one).1 == one
-- one QNaN: the number, no exception; two QNaNs: the fs one
#guard [Format.MinMaxOp.max, .min, .maxa, .mina].all fun op =>
  f32MinMax op .RN qnan1 one == (one, Flags.none) && f32MinMax op .RN one qnan1 == (one, Flags.none) &&
  f32MinMax op .RN qnan1 qnan2 == (qnan1, Flags.none) && f32MinMax op .RN qnan2 qnan1 == (qnan2, Flags.none)
-- an SNaN: Invalid; a number is still preferred; NaN results are not quietened
#guard [Format.MinMaxOp.max, .min, .maxa, .mina].all fun op =>
  f32MinMax op .RN snan one == (one, Flags.invalidOnly) &&
  f32MinMax op .RN one snan == (one, Flags.invalidOnly) &&
  f32MinMax op .RN snan qnan1 == (snan, Flags.invalidOnly) &&
  f32MinMax op .RN qnan1 snan == (qnan1, Flags.invalidOnly)
-- FCSR.FS: subnormal operands are flushed (to zero of the same sign) before the choice
#guard (f32MinMax .max .RN psub nz).1 == psub && (f32MinMax .max flushEnv psub nz).1 == pz
#guard (f32MinMax .min flushEnv nsub pz).1 == nz
-- double precision
#guard (f64MinMax .max .RN 0x8000000000000000#64 0#64).1 == 0#64
#guard (f64MinMax .mina .RN 0xC000000000000000#64 0x4000000000000000#64).1 == 0xC000000000000000#64
#guard f64MinMax .min .RN 0x7FF0000000000001#64 0x3FF0000000000000#64 ==
  (0x3FF0000000000000#64, Flags.invalidOnly)

/-! ### CLASS -/

#guard [(snan, 1), (qnan1, 2), (ninf, 4), (mone, 8), (nsub, 16), (nz, 32),
        (pinf, 64), (one, 128), (psub, 256), (pz, 512)].all fun (x, m) => f32Class x == BitVec.ofNat 32 m
#guard [(0x7FF0000000000001#64, 1), (0x7FF8000000000000#64, 2), (0xFFF0000000000000#64, 4),
        (0xBFF0000000000000#64, 8), (0x8000000000000001#64, 16), (0x8000000000000000#64, 32),
        (0x7FF0000000000000#64, 64), (0x3FF0000000000000#64, 128), (0x0000000000000001#64, 256),
        (0#64, 512)].all fun (x, m) => f64Class x == BitVec.ofNat 64 m

/-! ### RINT -/

-- 2.5 and -2.5 in the four modes (halfway: RN ties to even)
#guard f32Rint .RN twohalf == (two, Flags.inexactOnly) && f32Rint .RZ twohalf == (two, Flags.inexactOnly) &&
  f32Rint .RP twohalf == (three, Flags.inexactOnly) && f32Rint .RM twohalf == (two, Flags.inexactOnly)
#guard f32Rint .RN mtwohalf == (mtwo, Flags.inexactOnly) && f32Rint .RZ mtwohalf == (mtwo, Flags.inexactOnly) &&
  f32Rint .RP mtwohalf == (mtwo, Flags.inexactOnly) && f32Rint .RM mtwohalf == (mthree, Flags.inexactOnly)
#guard f32Rint .RN onehalf == (two, Flags.inexactOnly)
-- zero results keep the operand's sign
#guard f32Rint .RN half == (pz, Flags.inexactOnly) && f32Rint .RN mhalf == (nz, Flags.inexactOnly)
#guard f32Rint .RP mpoint3 == (nz, Flags.inexactOnly) && f32Rint .RM mpoint3 == (mone, Flags.inexactOnly)
#guard f32Rint .RN nz == (nz, Flags.none) && f32Rint .RM pz == (pz, Flags.none)
-- integers are exact
#guard f32Rint .RN three == (three, Flags.none) && f32Rint .RZ big == (big, Flags.none)
-- infinities, NaNs
#guard f32Rint .RN ninf == (ninf, Flags.none) && f32Rint .RN qnan1 == (qnan1, Flags.none)
#guard f32Rint .RN snan == (0x7FC00001#32, Flags.invalidOnly)
-- subnormals: rounded (inexact), or flushed under FCSR.FS (the flushing signals Inexact, MD00082
-- Vol I-A Rev 6.01 §6.7.2.4, p.102)
#guard f32Rint .RP psub == (one, Flags.inexactOnly) &&
  f32Rint { rm := .RP, flush := true } psub == (pz, Flags.inexactOnly) &&
  f32Rint { rm := .RM, flush := true } nsub == (nz, Flags.inexactOnly)
-- double precision
#guard f64Rint .RN 0x4004000000000000#64 == (0x4000000000000000#64, Flags.inexactOnly)
#guard f64Rint .RP 0x4004000000000000#64 == (0x4008000000000000#64, Flags.inexactOnly)
#guard f64Rint .RN 0x7FEFFFFFFFFFFFFF#64 == (0x7FEFFFFFFFFFFFFF#64, Flags.none)
#guard f64Rint .RM 0xBFE0000000000000#64 == (0xBFF0000000000000#64, Flags.inexactOnly)

/-! ### CMP: the 22 implemented predicates on the four relations

Each predicate is the set of relations it accepts (`g` greater, `l` less, `e` equal, `u` unordered),
transcribed from the CMP column of Table 3.9. -/

def cmpPreds : List (Nat × String) :=
  [(0, ""), (1, "u"), (2, "e"), (3, "eu"), (4, "l"), (5, "lu"), (6, "le"), (7, "leu"),
   (8, ""), (9, "u"), (10, "e"), (11, "eu"), (12, "l"), (13, "lu"), (14, "le"), (15, "leu"),
   (17, "gle"), (18, "glu"), (19, "gl"), (25, "gle"), (26, "glu"), (27, "gl")]

/-- Operand pairs with their relation; `+0`/`-0` compare equal. -/
def cmpPairs32 : List (BitVec 32 × BitVec 32 × Char) :=
  [(two, one, 'g'), (one, two, 'l'), (one, one, 'e'), (pz, nz, 'e'), (ninf, mone, 'l'),
   (pinf, pinf, 'e'), (qnan1, one, 'u'), (one, qnan1, 'u')]

#guard cmpPreds.all fun (c, s) => cmpPairs32.all fun (a, b, r) =>
  f32Cmp (BitVec.ofNat 5 c) a b == (s.contains r, Flags.none) || r == 'u'
-- unordered (QNaN): predicate value, and Invalid exactly for the signalling ones (cond3)
#guard cmpPreds.all fun (c, s) =>
  f32Cmp (BitVec.ofNat 5 c) qnan1 one == (s.contains 'u', { invalid := c % 16 ≥ 8 })
-- an SNaN: always Invalid
#guard cmpPreds.all fun (c, s) =>
  f32Cmp (BitVec.ofNat 5 c) one snan == (s.contains 'u', Flags.invalidOnly)
-- double precision
#guard cmpPreds.all fun (c, s) =>
  [(0x4000000000000000#64, 0x3FF0000000000000#64, 'g'), (0x8000000000000000#64, 0#64, 'e'),
   (0xFFF0000000000000#64, 0#64, 'l')].all fun (a, b, r) =>
    f64Cmp (BitVec.ofNat 5 c) a b == (s.contains r, Flags.none)
#guard cmpPreds.all fun (c, s) =>
  f64Cmp (BitVec.ofNat 5 c) 0x7FF8000000000000#64 0#64 == (s.contains 'u', { invalid := c % 16 ≥ 8 })

end Mips.Fp.TestR6C
-- END R6-6C

-- BEGIN R6-6D
/-! FCSR.FS = 1 input flushing: every non-comparison operation that flushes a subnormal operand
signals Inexact for it (MD00082 Vol I-A Rev 6.01 §6.7.2.4, p.102: "Flushing of subnormal input operands
in all instructions except comparisons causes Inexact exception to be signaled"); the comparisons
(here MAX/MIN, "Floating Point Comparison Instructions", Table 7.9, p.110) do not. -/
namespace Mips.Fp.TestR6D

def fs : Env := { flush := true }

-- arithmetic: 1 + 2^-149 is 1 + 0 = 1 exactly, Inexact from the flush; no subnormal, no flag
#guard f32Add fs 0x3F800000#32 0x00000001#32 == (0x3F800000#32, Flags.inexactOnly)
#guard f32Add fs 0x3F800000#32 0x3F800000#32 == (0x40000000#32, Flags.none)
#guard f64Mul fs 0x0000000000000001#64 0x4630000000000000#64 == (0#64, Flags.inexactOnly)
#guard f32Sub fs 0x80000001#32 0x00000000#32 == (0x80000000#32, Flags.inexactOnly)
-- division by a flushed operand: Division by Zero and the flush's Inexact
#guard f32Div fs 0x3F800000#32 0x00000001#32 == (0x7F800000#32, { divZero := true, inexact := true })
#guard f64Sqrt fs 0x0000000000000001#64 == (0#64, Flags.inexactOnly)
-- RECIP / RSQRT
#guard f32Recip fs 0x80000001#32 == (0xFF800000#32, { divZero := true, inexact := true })
#guard f64Rsqrt fs 0x0000000000000001#64 == (0x7FF0000000000000#64, { divZero := true, inexact := true })
-- a NaN with a subnormal: Invalid from the SNaN, Inexact from the flush (ORed)
#guard f32Mul fs 0x7F800001#32 0x00000001#32 == (0x7FC00001#32, { invalid := true, inexact := true })
-- conversions
#guard f64ToF32 fs 0x0000000000000001#64 == (0#32, Flags.inexactOnly)
#guard f32ToW64 .RP true 0x00000001#32 == (0#64, Flags.inexactOnly)
-- fused multiply-add: any of the three operands
#guard f32Fma fs false 0x00000000#32 0x00000001#32 0x71800000#32 == (0#32, Flags.inexactOnly)
#guard f64Fma fs true 0x0000000000000001#64 0x3FF0000000000000#64 0x3FF0000000000000#64 ==
  (0xBFF0000000000000#64, Flags.inexactOnly)
-- comparisons: flushed, no flag (MAX(+2^-149, -0) is MAX(+0, -0) = +0)
#guard f32MinMax .max fs 0x00000001#32 0x80000000#32 == (0#32, Flags.none)
#guard f64MinMax .mina fs 0x8000000000000001#64 0x3FF0000000000000#64 == (0x8000000000000000#64, Flags.none)

end Mips.Fp.TestR6D
-- END R6-6D
