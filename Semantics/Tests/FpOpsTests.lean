import Semantics.FpOps

/-!
# Differential tests for `Semantics/FpOps.lean` against Lean's `Float32` / `Float`

Formerly §11 of `Semantics/FpOps.lean`; moved verbatim. This is the only place where the host's
floating point appears: it is an oracle for `#guard`s, never part of a definition.
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
  (isNaN32 x == (isQNaN32 x || isSNaN32 x)) && !(isQNaN32 x && isSNaN32 x)

#guard pats64.all fun x =>
  isNaN64 x == (toF64 x).isNaN && isInf64 x == (toF64 x).isInf &&
  isZero64 x == (toF64 x == 0.0) &&
  (isNaN64 x == (isQNaN64 x || isSNaN64 x)) && !(isQNaN64 x && isSNaN64 x)

/-! ### `f32ToF64` vs `Float32.toFloat` (exact, never raises on non-NaN) -/

#guard pats32.all fun x =>
  isNaN32 x || f32ToF64 x == (ofF64 (toF32 x).toFloat, Flags.none)

#guard pats32.all fun x =>
  !isNaN32 x || isQNaN64 (f32ToF64 x).1 && (toF32 x).toFloat.isNaN &&
    (f32ToF64 x).2.invalid == isSNaN32 x

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
  if r.isNaN || r < -2147483648.0 || r > 2147483647.0 then (0x7FFFFFFF#32, Flags.invalidOnly)
  else (r.toInt32.toBitVec, if srcIntegral then Flags.none else Flags.inexactOnly)

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
  f64ToW32 .RZ d == w32Oracle (rzOracle f) integral &&
  f64ToW32 .RM d == w32Oracle f.floor integral &&
  f64ToW32 .RP d == w32Oracle f.ceil integral &&
  f64ToW32 .RN d == w32Oracle (rnOracle f) integral

-- singles: widen exactly with the host, then use the same oracles
#guard pats32.all fun x =>
  let f := (toF32 x).toFloat
  let integral := f.floor == f
  f32ToW32 .RZ x == w32Oracle (rzOracle f) integral &&
  f32ToW32 .RM x == w32Oracle f.floor integral &&
  f32ToW32 .RP x == w32Oracle f.ceil integral &&
  f32ToW32 .RN x == w32Oracle (rnOracle f) integral

-- direct comparison with the host's own truncating conversion, in range
#guard pats32.all fun x =>
  let f := toF32 x
  !(f.abs < 2147483648.0) || (f32ToW32 .RZ x).1 == f.toInt32.toBitVec

#guard pats64.all fun d =>
  let f := toF64 d
  !(f.abs < 2147483648.0) || (f64ToW32 .RZ d).1 == f.toInt32.toBitVec

-- … and with the host's `floor`/`ceil` on singles (the functions the old
-- model used), where the result is in range
#guard pats32.all fun x =>
  let f := toF32 x
  !(f.abs < 2147483000.0) ||
    ((f32ToW32 .RM x).1 == f.floor.toInt32.toBitVec &&
     (f32ToW32 .RP x).1 == f.ceil.toInt32.toBitVec)

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
  isNaN32 x || ((f32Abs x).1 == ofF32 (toF32 x).abs && (f32Neg x).1 == ofF32 (-(toF32 x)))

#guard pats64.all fun d =>
  isNaN64 d || ((f64Abs d).1 == ofF64 (toF64 d).abs && (f64Neg d).1 == ofF64 (-(toF64 d)))

-- host-generated NaNs (0/0, ∞ − ∞, sqrt(−1)) canonicalise to the default QNaN
#guard canonNaN32 (ofF32 ((0.0 : Float32) / 0.0)) == defaultQNaN32 &&
  canonNaN32 (ofF32 (toF32 0x7F800000#32 - toF32 0x7F800000#32)) == defaultQNaN32 &&
  canonNaN64 (ofF64 ((0.0 : Float) / 0.0)) == defaultQNaN64 &&
  canonNaN64 (ofF64 (Float.sqrt (-1.0))) == defaultQNaN64

/-! ### `add` / `sub` / `mul` / `div` / `sqrt` vs the host's IEEE arithmetic

Under round-to-nearest the model must agree **bit for bit** with the host on
every non-NaN result, and produce a NaN exactly when the host does (the NaN
*pattern* is MIPS-legacy and deliberately differs). -/

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

-- unfused multiply-add = two host operations
#guard (pairs32.zip (lcg32 5000 4242)).all fun ((a, b), c) =>
  agree32 (f32Madd .RN c a b).1 (toF32 a * toF32 b + toF32 c) &&
  agree32 (f32Msub .RN c a b).1 (toF32 a * toF32 b - toF32 c)
#guard (pairs64.zip (lcg64 6000 4242)).all fun ((a, b), c) =>
  agree64 (f64Madd .RN c a b).1 (toF64 a * toF64 b + toF64 c) &&
  agree64 (f64Msub .RN c a b).1 (toF64 a * toF64 b - toF64 c)

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
