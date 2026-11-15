import Semantics.Word

/-!
# FpOps — pure bit-level IEEE-754 helpers for the MIPS32r2 FPU (COP1)

Everything in this file is a *total, kernel-reducible* function over
`BitVec 32` / `BitVec 64` (internally: over `Nat`/`Int`, whose arithmetic the
kernel evaluates natively).  No `Float`/`Float32` appears in any definition
(they appear only in `Semantics/Tests/FpOpsTests.lean`, as an oracle), so
every fact about it can be proved by `decide`/`rfl`/`simp`.

`Semantics/Step.lean` uses nothing else for floating point: the whole FPU
model is these definitions.

| Section | Content | Manual |
|---|---|---|
| §1 | `Flags`, `RoundingMode` | MD00082 Vol I, FPU chapter: FCSR `RM`, `Flags` |
| §2 | exact values, `roundToInt` | IEEE-754 rounding-direction attributes |
| §3 | formats, unpacking, classification, legacy NaN encoding | MD00082 Vol I, "Formats" / QNaN-SNaN encoding (pre-NAN2008) |
| §4 | correctly rounded packing (`Format.round`) | IEEE-754 §4, §7.4, §7.5 |
| §5 | float → word (`f32ToW32`, `f64ToW32`) | MD00086 `CVT.W.fmt`, `ROUND.W.fmt`, `TRUNC.W.fmt`, `CEIL.W.fmt`, `FLOOR.W.fmt` |
| §6 | format conversions (`f32ToF64`, `f64ToF32`, `w32ToF32`, `w32ToF64`) | MD00086 `CVT.D.fmt`, `CVT.S.fmt` |
| §7 | NaN policy, `abs`/`neg` | MD00086 `ABS.fmt`, `NEG.fmt`; MD00082 default QNaN |
| §8 | comparison | MD00086 `C.cond.fmt` |
| §9 | FCSR and the `CFC1`/`CTC1` control-register views | MD00086 `CFC1`, `CTC1`; MD00082 Vol I FCSR/FIR/FCCR/FEXR/FENR |
| §9a | arithmetic: `add`/`sub`/`mul`/`div`/`sqrt`, multiply-add family, `recip`/`rsqrt` (exact result, one rounding; NaN rules) | MD00082 Vol I §6.3, §6.7; MD00086 `ADD.fmt` … `MADD.fmt` |

Kernel-checked facts about these definitions (formerly §10) are in
`Semantics/FpOpsFacts.lean`; the differential tests against Lean's
`Float32`/`Float` (formerly §11) are in `Semantics/Tests/FpOpsTests.lean`.

Conventions:

* NaN encoding is the MIPS32r2 **legacy** one (FCSR.NAN2008 = 0): a NaN whose
  fraction MSB is **1 is signaling**, **0 is quiet**.  The default generated
  QNaN is `0x7FBFFFFF` / `0x7FF7FFFF_FFFFFFFF`.
* Tininess (for the Underflow flag) is detected **after rounding**, and
  Underflow is flagged only when the result is also inexact (the untrapped
  IEEE default).
* Functions returning `… × Flags` report the IEEE exceptions *raised by that
  operation*; folding them into the FCSR is §9 (`raiseFlags`/`fpUpdate`).
-/

namespace Mips.Fp

/-! ## §1  Exception flags and rounding modes -/

/-- The five IEEE-754 exceptions raised by one operation
(MD00082 Vol I, FCSR `Cause`/`Enables`/`Flags` letters V, Z, O, U, I). -/
structure Flags where
  /-- V — Invalid Operation. -/
  invalid : Bool := false
  /-- Z — Divide by Zero. -/
  divZero : Bool := false
  /-- O — Overflow. -/
  overflow : Bool := false
  /-- U — Underflow. -/
  underflow : Bool := false
  /-- I — Inexact. -/
  inexact : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace Flags

/-- No exception. -/
def none : Flags := {}

/-- Only Invalid Operation. -/
def invalidOnly : Flags := { invalid := true }

/-- Only Inexact. -/
def inexactOnly : Flags := { inexact := true }

/-- Pointwise union of two flag sets. -/
def or (a b : Flags) : Flags where
  invalid := a.invalid || b.invalid
  divZero := a.divZero || b.divZero
  overflow := a.overflow || b.overflow
  underflow := a.underflow || b.underflow
  inexact := a.inexact || b.inexact

/-- `true` iff at least one exception is present. -/
def any (f : Flags) : Bool :=
  f.invalid || f.divZero || f.overflow || f.underflow || f.inexact

/-- The 5-bit FCSR field encoding, LSB first: I = bit 0, U = 1, O = 2, Z = 3,
V = 4.  (Shifted left by 2 this is FCSR.Flags, by 7 FCSR.Enables, by 12 the
low five bits of FCSR.Cause.) -/
def toBits (f : Flags) : BitVec 5 :=
  BitVec.ofNat 5
    ((if f.inexact then 1 else 0) + (if f.underflow then 2 else 0) +
     (if f.overflow then 4 else 0) + (if f.divZero then 8 else 0) +
     (if f.invalid then 16 else 0))

/-- Inverse of `toBits`. -/
def ofBits (b : BitVec 5) : Flags where
  inexact := b.getLsbD 0
  underflow := b.getLsbD 1
  overflow := b.getLsbD 2
  divZero := b.getLsbD 3
  invalid := b.getLsbD 4

end Flags

/-- IEEE rounding-direction attribute, in the FCSR.RM encoding
(MD00082 Vol I, FCSR bits 1..0): 0 = RN (nearest, ties to even),
1 = RZ (toward zero), 2 = RP (toward +∞), 3 = RM (toward −∞). -/
inductive RoundingMode where
  /-- Round to nearest, ties to even (RM = 0). `ROUND.W.fmt`. -/
  | RN
  /-- Round toward zero (RM = 1). `TRUNC.W.fmt`. -/
  | RZ
  /-- Round toward +∞ (RM = 2). `CEIL.W.fmt`. -/
  | RP
  /-- Round toward −∞ (RM = 3). `FLOOR.W.fmt`. -/
  | RM
  deriving DecidableEq, Repr, Inhabited

namespace RoundingMode

/-- FCSR.RM encoding of a rounding mode. -/
def toBits : RoundingMode → BitVec 2
  | RN => 0#2
  | RZ => 1#2
  | RP => 2#2
  | RM => 3#2

/-- Decode the FCSR.RM field. -/
def ofBits (b : BitVec 2) : RoundingMode :=
  match b.toNat with
  | 0 => RN
  | 1 => RZ
  | 2 => RP
  | _ => RM

end RoundingMode

/-! ## §2  Exact values and the integer rounding core -/

/-- An exact dyadic rational: `(-1)^sign × sig × 2^exp`.  Every finite
floating-point datum, and every integer, is exactly representable. -/
structure Exact where
  /-- `true` = negative. -/
  sign : Bool
  /-- Integer significand (magnitude). -/
  sig : Nat
  /-- Binary exponent of the significand's unit. -/
  exp : Int
  deriving DecidableEq, Repr, Inhabited

/-- `roundShift rm neg m k` is the magnitude `m / 2^k` rounded to a natural
number in direction `rm`, where `neg` says whether the value being rounded is
negative (this matters for the directed modes RP/RM only). -/
def roundShift (rm : RoundingMode) (neg : Bool) (m k : Nat) : Nat :=
  let q := m / 2 ^ k
  let r := m % 2 ^ k
  let roundUp : Bool :=
    match rm with
    | .RN => decide (2 ^ k < 2 * r) || (decide (2 * r = 2 ^ k) && q % 2 == 1)
    | .RZ => false
    | .RP => !neg && r != 0
    | .RM => neg && r != 0
  if roundUp then q + 1 else q

/-- `true` iff the exact value is an integer. -/
def Exact.isIntegral (v : Exact) : Bool :=
  match v.exp with
  | .ofNat _ => true
  | .negSucc k => v.sig % 2 ^ (k + 1) == 0

/-- The exact value rounded to an integer in direction `rm` (the unbounded
mathematical integer; range checking is the caller's job, see `Format.toW32`). -/
def roundToInt (rm : RoundingMode) (v : Exact) : Int :=
  let mag : Nat :=
    match v.exp with
    | .ofNat e => v.sig * 2 ^ e
    | .negSucc k => roundShift rm v.sign v.sig (k + 1)
  if v.sign then -(mag : Int) else (mag : Int)

/-- Bit length with explicit fuel (structural recursion keeps it reducible). -/
def bitLenAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else bitLenAux fuel (n / 2) + 1

/-- Number of significant bits of `n`: `bitLen 0 = 0`, `bitLen 1 = 1`,
`bitLen 255 = 8`, `bitLen 256 = 9`.  (`n` itself is ample fuel.) -/
def bitLen (n : Nat) : Nat := bitLenAux n n

/-! ## §3  Formats, unpacking and classification -/

/-- An IEEE-754 binary interchange format: sign bit, `expBits` biased-exponent
bits, `fracBits` fraction bits.  Bit patterns are handled as `Nat`s here; the
`BitVec` wrappers follow each generic definition. -/
structure Format where
  /-- Width of the biased-exponent field. -/
  expBits : Nat
  /-- Width of the fraction field. -/
  fracBits : Nat

/-- IEEE-754 binary32 (MIPS `S` format). -/
def binary32 : Format := ⟨8, 23⟩

/-- IEEE-754 binary64 (MIPS `D` format). -/
def binary64 : Format := ⟨11, 52⟩

namespace Format

/-- The all-ones biased exponent (Inf/NaN): 255 / 2047. -/
def expMax (f : Format) : Nat := 2 ^ f.expBits - 1

/-- Exponent bias: 127 / 1023. -/
def bias (f : Format) : Nat := 2 ^ (f.expBits - 1) - 1

/-- Exponent of the unit in the last place of subnormals and of the smallest
normals: −149 / −1074. -/
def qMin (f : Format) : Int := 1 - (f.bias : Int) - (f.fracBits : Int)

/-- Exponent of the unit in the last place of the largest finite numbers:
104 / 971. -/
def qMax (f : Format) : Int := (f.bias : Int) - (f.fracBits : Int)

/-- Sign bit. -/
def signBit (f : Format) (n : Nat) : Bool :=
  (n / 2 ^ (f.expBits + f.fracBits)) % 2 == 1

/-- Biased exponent field. -/
def expField (f : Format) (n : Nat) : Nat := (n / 2 ^ f.fracBits) % 2 ^ f.expBits

/-- Fraction field. -/
def fracField (f : Format) (n : Nat) : Nat := n % 2 ^ f.fracBits

/-- Assemble a bit pattern from sign, biased exponent and fraction. -/
def pack (f : Format) (sign : Bool) (e frac : Nat) : Nat :=
  (if sign then 2 ^ (f.expBits + f.fracBits) else 0) + e * 2 ^ f.fracBits + frac

/-- ±0. -/
def zero (f : Format) (sign : Bool) : Nat := f.pack sign 0 0

/-- ±∞. -/
def inf (f : Format) (sign : Bool) : Nat := f.pack sign f.expMax 0

/-- ± the largest finite number. -/
def maxFinite (f : Format) (sign : Bool) : Nat :=
  f.pack sign (f.expMax - 1) (2 ^ f.fracBits - 1)

/-- The MIPS32r2 legacy default quiet NaN (MD00082 Vol I): positive, exponent
all ones, fraction `0111…1`: `0x7FBFFFFF` / `0x7FF7FFFF_FFFFFFFF`. -/
def defaultQNaN (f : Format) : Nat := f.pack false f.expMax (2 ^ (f.fracBits - 1) - 1)

/-- NaN: exponent all ones, fraction nonzero. -/
def isNaN (f : Format) (n : Nat) : Bool := f.expField n == f.expMax && f.fracField n != 0

/-- ±∞: exponent all ones, fraction zero. -/
def isInf (f : Format) (n : Nat) : Bool := f.expField n == f.expMax && f.fracField n == 0

/-- ±0. -/
def isZero (f : Format) (n : Nat) : Bool := f.expField n == 0 && f.fracField n == 0

/-- Subnormal (denormalized, nonzero). -/
def isSubnormal (f : Format) (n : Nat) : Bool := f.expField n == 0 && f.fracField n != 0

/-- Zero, subnormal or normal. -/
def isFinite (f : Format) (n : Nat) : Bool := f.expField n != f.expMax

/-- Legacy-encoding signaling NaN: a NaN whose fraction MSB is **1**. -/
def isSNaN (f : Format) (n : Nat) : Bool :=
  f.isNaN n && f.fracField n / 2 ^ (f.fracBits - 1) == 1

/-- Legacy-encoding quiet NaN: a NaN whose fraction MSB is **0**. -/
def isQNaN (f : Format) (n : Nat) : Bool :=
  f.isNaN n && f.fracField n / 2 ^ (f.fracBits - 1) == 0

/-- The exact value of a **finite** datum.  (For Inf/NaN patterns the result
is the value the pattern would have if its exponent were an ordinary one; no
caller in this file uses it that way.) -/
def toExact (f : Format) (n : Nat) : Exact :=
  if f.expField n = 0 then
    ⟨f.signBit n, f.fracField n, f.qMin⟩
  else
    ⟨f.signBit n, f.fracField n + 2 ^ f.fracBits,
      (f.expField n : Int) - (f.bias : Int) - (f.fracBits : Int)⟩

/-! ## §4  Correctly rounded packing -/

/-- The raw outcome of rounding an exact value to a format: the packed bit
pattern plus the three conditions from which the IEEE flags are derived
(`Rounded.flags`). Keeping them separate lets the flags depend on FCSR.Enables
the way MD00082 Vol I-A Rev 6.01 §6.7.2.3 / §6.7.2.6 (p.101-102) specify. -/
structure Rounded where
  /-- The delivered (default) result. -/
  bits : Nat
  /-- The result rounded with unbounded exponent range exceeds the largest
  finite number (§6.7.2.5). -/
  overflow : Bool
  /-- Tininess: detected **after rounding** (§6.7.2.3), or before rounding
  when the result was flushed to zero (FCSR.FS = 1, §6.7.2.4). -/
  tiny : Bool
  /-- The rounded result (unbounded exponent range in the overflow case)
  differs from the exact value. -/
  inexact : Bool
  deriving DecidableEq, Repr, Inhabited

/-- IEEE flags of a rounding outcome, given FCSR.Enables `en`
(MD00082 Vol I-A Rev 6.01):

* Underflow (§6.7.2.3, p.101): "When an underflow trap is not enabled,
  underflow is signaled only when both tininess and loss of accuracy have
  been detected. … When an underflow trap is enabled …, underflow is signaled
  when tininess is detected regardless of loss of accuracy."
* Inexact (§6.7.2.6, p.102): "The rounded result of an operation is not
  exact", or "The rounded result of an operation overflows without an
  overflow trap". -/
def Rounded.flags (r : Rounded) (en : Flags) : Flags where
  overflow := r.overflow
  underflow := r.tiny && (r.inexact || en.underflow)
  inexact := r.inexact || (r.overflow && !en.overflow)

/-- Round the exact value `v` to format `f` in direction `rm`
(IEEE-754 §4.3, §7.4, §7.5; MD00082 Vol I-A Rev 6.01 Table 6.14, p.100).

* Overflow delivers ±∞ or ± the largest finite number as the rounding
  direction dictates (Table 6.14).
* Results below the normal range are denormalized (gradual underflow);
  `tiny` is tininess detected *after* rounding (the result rounded with
  unbounded exponent range would be below the smallest normal).
* With `flush` (FCSR.FS = 1; §6.7.2.4, p.101-102) "every tiny non-zero result
  is replaced with zero of the same sign", tininess being "detected before
  rounding", and the flush is reported as tiny and inexact.
* A zero significand gives a zero carrying `v.sign`. -/
def roundCore (f : Format) (rm : RoundingMode) (flush : Bool) (v : Exact) : Rounded :=
  if v.sig = 0 then ⟨f.zero v.sign, false, false, false⟩ else
  let p := f.fracBits + 1
  -- exponent at which the significand has exactly `p` bits
  let q0 : Int := v.exp + (bitLen v.sig : Int) - (p : Int)
  if flush && decide (q0 < f.qMin) then ⟨f.zero v.sign, false, true, true⟩ else
  -- … clamped to the subnormal exponent
  let q : Int := if q0 < f.qMin then f.qMin else q0
  let dropped : Nat := (q - v.exp).toNat
  let m := roundShift rm v.sign (v.sig * 2 ^ (v.exp - q).toNat) dropped
  let inexact : Bool := v.sig % 2 ^ dropped != 0
  -- rounding may carry out to `2^p`: renormalize
  let carry : Bool := m == 2 ^ p
  let m' := if carry then 2 ^ f.fracBits else m
  let q' : Int := if carry then q + 1 else q
  if f.qMax < q' then
    let toInf : Bool :=
      match rm with
      | .RN => true
      | .RZ => false
      | .RP => !v.sign
      | .RM => v.sign
    ⟨if toInf then f.inf v.sign else f.maxFinite v.sign, true, false, inexact⟩
  else
    -- tininess after rounding: rounded with unbounded exponent, still < 2^emin
    let tiny : Bool :=
      decide (q0 < f.qMin) &&
        !(decide (q0 + 1 = f.qMin) &&
          roundShift rm v.sign v.sig (q0 - v.exp).toNat == 2 ^ p)
    let bits :=
      if m' < 2 ^ f.fracBits then f.pack v.sign 0 m'
      else f.pack v.sign (q' - f.qMin + 1).toNat (m' - 2 ^ f.fracBits)
    ⟨bits, false, tiny, inexact⟩

/-- `roundCore` with no trap enabled and no flushing: the delivered result
and the untrapped IEEE flags (Overflow ⇒ Inexact; Underflow only when tiny
and inexact). -/
def round (f : Format) (rm : RoundingMode) (v : Exact) : Nat × Flags :=
  let r := f.roundCore rm false v
  (r.bits, r.flags Flags.none)

end Format

/-- The FCSR state an arithmetic operation consults (MD00082 Vol I-A Rev 6.01
§6.5.4, Table 6.8, p.92-95): the rounding mode `RM`, the `Enables` field
(which changes *which* conditions are signaled, see `Rounded.flags`) and the
flush-to-zero bit `FS`. `envOf` (§9) extracts it from an FCSR value. The
default is round-to-nearest, nothing enabled, no flushing. -/
structure Env where
  /-- FCSR.RM. -/
  rm : RoundingMode := .RN
  /-- FCSR.Enables. -/
  enables : Flags := {}
  /-- FCSR.FS. -/
  flush : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace Env
/-- Round to nearest even, nothing enabled, no flushing. -/
def RN : Env := {}
/-- Round toward zero, nothing enabled, no flushing. -/
def RZ : Env := { rm := .RZ }
/-- Round toward +∞, nothing enabled, no flushing. -/
def RP : Env := { rm := .RP }
/-- Round toward −∞, nothing enabled, no flushing. -/
def RM : Env := { rm := .RM }
/-- The environment with rounding mode `rm`, nothing enabled, no flushing. -/
def ofRM (rm : RoundingMode) : Env := { rm := rm }
end Env

instance : Coe RoundingMode Env := ⟨Env.ofRM⟩

namespace Format

/-- Round the exact value `v` to format `f` under the FCSR environment `e`:
the default result and the exceptions signaled (`roundCore`, `Rounded.flags`). -/
def roundEnv (f : Format) (e : Env) (v : Exact) : Nat × Flags :=
  let r := f.roundCore e.rm e.flush v
  (r.bits, r.flags e.enables)

/-- Convert a signed integer to format `f` (correctly rounded; `0 ↦ +0`). -/
def ofInt (f : Format) (e : Env) (i : Int) : Nat × Flags :=
  f.roundEnv e ⟨decide (i < 0), i.natAbs, 0⟩

/-- NaN operand of a format conversion (MD00082 Vol I-A Rev 6.01 §6.3.1.4,
§6.3.1.5, p.81-82). A signaling NaN signals Invalid Operation and the default
result is a new QNaN (Table 6.3, p.82). A quiet NaN is propagated: "Propagation
of the diagnostic information requires information contained in a QNaN to be
preserved through arithmetic operations and floating-point format
conversions" — the sign and the most significant fraction bits are kept
(widening appends zeros, narrowing drops low bits). If narrowing leaves a zero
fraction — the pattern would be an infinity, so "no input operand QNaN value
can be copied" — the destination's default QNaN is supplied (model pin). The
fraction MSB is preserved either way, so the result is again quiet. -/
def convertNaN (src dst : Format) (n : Nat) : Nat × Flags :=
  if src.isSNaN n then (dst.defaultQNaN, Flags.invalidOnly) else
  let frac :=
    if src.fracBits ≤ dst.fracBits then src.fracField n * 2 ^ (dst.fracBits - src.fracBits)
    else src.fracField n / 2 ^ (src.fracBits - dst.fracBits)
  if frac = 0 then (dst.defaultQNaN, Flags.none)
  else (dst.pack (src.signBit n) dst.expMax frac, Flags.none)

/-- Convert between formats: NaN per `convertNaN`, ±∞ ↦ ±∞, otherwise
correctly rounded under `e`. -/
def convert (src dst : Format) (e : Env) (n : Nat) : Nat × Flags :=
  if src.isNaN n then convertNaN src dst n
  else if src.isInf n then (dst.inf (src.signBit n), Flags.none)
  else dst.roundEnv e (src.toExact n)

/-! ## §5  Float → 32-bit word (generic) -/

/-- MD00086 `CVT.W.fmt` / `ROUND.W.fmt` / `TRUNC.W.fmt` / `CEIL.W.fmt` /
`FLOOR.W.fmt`: round to a signed 32-bit integer in direction `rm`.

If the source is NaN or ±∞, or the *rounded* result is outside
`[−2^31, 2^31 − 1]`, the result is `0x7FFFFFFF` (2^31 − 1) and Invalid
Operation is raised.  Otherwise the rounded integer is returned, with Inexact
raised iff the source was not already an integer. -/
def toW32 (f : Format) (rm : RoundingMode) (n : Nat) : BitVec 32 × Flags :=
  if f.isNaN n || f.isInf n then (0x7FFFFFFF#32, Flags.invalidOnly) else
  let v := f.toExact n
  let i := roundToInt rm v
  if i < -2147483648 || 2147483647 < i then (0x7FFFFFFF#32, Flags.invalidOnly)
  else (BitVec.ofInt 32 i, if v.isIntegral then Flags.none else Flags.inexactOnly)

/-- Total order key of a non-NaN datum: sign-magnitude as an integer
(−0 and +0 both map to 0; ±∞ sort outside all finite values). -/
def orderKey (f : Format) (n : Nat) : Int :=
  let mag : Nat := n % 2 ^ (f.expBits + f.fracBits)
  if f.signBit n then -(mag : Int) else (mag : Int)

end Format

/-! ### `BitVec` wrappers: unpacking and classification (binary32) -/

/-- Sign bit (bit 31). -/
def sign32 (x : BitVec 32) : Bool := binary32.signBit x.toNat
/-- Biased exponent (bits 30..23). -/
def expField32 (x : BitVec 32) : Nat := binary32.expField x.toNat
/-- Fraction (bits 22..0). -/
def fracField32 (x : BitVec 32) : Nat := binary32.fracField x.toNat
/-- NaN (either kind). -/
def isNaN32 (x : BitVec 32) : Bool := binary32.isNaN x.toNat
/-- ±∞. -/
def isInf32 (x : BitVec 32) : Bool := binary32.isInf x.toNat
/-- ±0. -/
def isZero32 (x : BitVec 32) : Bool := binary32.isZero x.toNat
/-- Subnormal. -/
def isSubnormal32 (x : BitVec 32) : Bool := binary32.isSubnormal x.toNat
/-- Legacy quiet NaN (fraction MSB, bit 22, is 0). -/
def isQNaN32 (x : BitVec 32) : Bool := binary32.isQNaN x.toNat
/-- Legacy signaling NaN (fraction MSB, bit 22, is 1). -/
def isSNaN32 (x : BitVec 32) : Bool := binary32.isSNaN x.toNat
/-- Exact value of a finite single. -/
def toExact32 (x : BitVec 32) : Exact := binary32.toExact x.toNat

/-! ### `BitVec` wrappers: unpacking and classification (binary64) -/

/-- Sign bit (bit 63). -/
def sign64 (x : BitVec 64) : Bool := binary64.signBit x.toNat
/-- Biased exponent (bits 62..52). -/
def expField64 (x : BitVec 64) : Nat := binary64.expField x.toNat
/-- Fraction (bits 51..0). -/
def fracField64 (x : BitVec 64) : Nat := binary64.fracField x.toNat
/-- NaN (either kind). -/
def isNaN64 (x : BitVec 64) : Bool := binary64.isNaN x.toNat
/-- ±∞. -/
def isInf64 (x : BitVec 64) : Bool := binary64.isInf x.toNat
/-- ±0. -/
def isZero64 (x : BitVec 64) : Bool := binary64.isZero x.toNat
/-- Subnormal. -/
def isSubnormal64 (x : BitVec 64) : Bool := binary64.isSubnormal x.toNat
/-- Legacy quiet NaN (fraction MSB, bit 51, is 0). -/
def isQNaN64 (x : BitVec 64) : Bool := binary64.isQNaN x.toNat
/-- Legacy signaling NaN (fraction MSB, bit 51, is 1). -/
def isSNaN64 (x : BitVec 64) : Bool := binary64.isSNaN x.toNat
/-- Exact value of a finite double. -/
def toExact64 (x : BitVec 64) : Exact := binary64.toExact x.toNat

/-! ### Float → word -/

/-- Single → signed 32-bit word, rounding in direction `rm`
(MD00086: `ROUND.W.S` = `.RN`, `TRUNC.W.S` = `.RZ`, `CEIL.W.S` = `.RP`,
`FLOOR.W.S` = `.RM`, `CVT.W.S` = the current FCSR.RM).  See `Format.toW32`. -/
def f32ToW32 (rm : RoundingMode) (x : BitVec 32) : BitVec 32 × Flags :=
  binary32.toW32 rm x.toNat

/-- Double → signed 32-bit word (`ROUND/TRUNC/CEIL/FLOOR/CVT.W.D`).
See `Format.toW32`. -/
def f64ToW32 (rm : RoundingMode) (x : BitVec 64) : BitVec 32 × Flags :=
  binary64.toW32 rm x.toNat

/-! ## §6  Format conversions -/

/-- `CVT.D.S`: single → double.  Exact for every non-NaN input (no rounding
mode needed); NaN per `Format.convertNaN` (QNaN payload widened, SNaN ↦
`defaultQNaN64` with Invalid). -/
def f32ToF64 (x : BitVec 32) : BitVec 64 × Flags :=
  let r := Format.convert binary32 binary64 Env.RN x.toNat
  (BitVec.ofNat 64 r.1, r.2)

/-- `CVT.S.D`: double → single, correctly rounded under `e`, with
Overflow / Underflow / Inexact (see `Format.roundCore`); NaN per
`Format.convertNaN` (QNaN payload truncated, SNaN ↦ `defaultQNaN32` with
Invalid). -/
def f64ToF32 (e : Env) (x : BitVec 64) : BitVec 32 × Flags :=
  let r := Format.convert binary64 binary32 e x.toNat
  (BitVec.ofNat 32 r.1, r.2)

/-- `CVT.S.W`: signed 32-bit word → single, correctly rounded under `e`
(Inexact when `|x| > 2^24` needs rounding). -/
def w32ToF32 (e : Env) (x : BitVec 32) : BitVec 32 × Flags :=
  let r := binary32.ofInt e x.toInt
  (BitVec.ofNat 32 r.1, r.2)

/-- `CVT.D.W`: signed 32-bit word → double.  Always exact, never raises. -/
def w32ToF64 (x : BitVec 32) : BitVec 64 :=
  BitVec.ofNat 64 (binary64.ofInt Env.RN x.toInt).1

/-! ## §7  NaN policy, `abs` and `neg` -/

/-- MIPS32r2 legacy default single QNaN (MD00082 Vol I). -/
def defaultQNaN32 : BitVec 32 := 0x7FBFFFFF#32

/-- MIPS32r2 legacy default double QNaN (MD00082 Vol I). -/
def defaultQNaN64 : BitVec 64 := 0x7FF7FFFFFFFFFFFF#64

/-- Map every NaN pattern to `defaultQNaN32`; leave everything else alone.
Intended for the outputs of host-`Float32` arithmetic, whose generated NaN
(`0x7FC00000`) is a *signaling* pattern in the legacy encoding. -/
def canonNaN32 (x : BitVec 32) : BitVec 32 := if isNaN32 x then defaultQNaN32 else x

/-- Map every NaN pattern to `defaultQNaN64`; leave everything else alone. -/
def canonNaN64 (x : BitVec 64) : BitVec 64 := if isNaN64 x then defaultQNaN64 else x

/-- `ABS.S`. With `FIR.Has2008 = 0` "this operation is arithmetic. For this
case, any NaN operand signals invalid operation" (MD00086 Vol II-A Rev 6.06,
ABS.fmt, p.32). A signaling NaN gives the default QNaN ("An SNaN is never
produced as a result value", MD00082 Vol I-A Rev 6.01 §6.3.1.4, p.81; Table
6.3, p.82). A quiet NaN operand: Invalid, and the untrapped result is the
operand with the sign bit cleared, as for any other operand (reading A′ of
SPEC-NOTES §9 item 21; `Manual.Oracle.absNegNaN`). Otherwise the sign bit is
cleared. -/
def f32Abs (x : BitVec 32) : BitVec 32 × Flags :=
  if isNaN32 x then
    (if isQNaN32 x then x &&& 0x7FFFFFFF#32 else defaultQNaN32, Flags.invalidOnly)
  else (x &&& 0x7FFFFFFF#32, Flags.none)

/-- `NEG.S` (arithmetic, as `f32Abs`; MD00086 Vol II-A Rev 6.06, NEG.fmt,
p.307: "The value is negated by changing the sign bit value"): any NaN signals
Invalid (a quiet NaN operand gives the operand with the sign bit flipped,
reading A′; signaling ↦ default QNaN); otherwise flip the sign bit. -/
def f32Neg (x : BitVec 32) : BitVec 32 × Flags :=
  if isNaN32 x then
    (if isQNaN32 x then x ^^^ 0x80000000#32 else defaultQNaN32, Flags.invalidOnly)
  else (x ^^^ 0x80000000#32, Flags.none)

/-- `ABS.D`: as `f32Abs`, for doubles. -/
def f64Abs (x : BitVec 64) : BitVec 64 × Flags :=
  if isNaN64 x then
    (if isQNaN64 x then x &&& 0x7FFFFFFFFFFFFFFF#64 else defaultQNaN64, Flags.invalidOnly)
  else (x &&& 0x7FFFFFFFFFFFFFFF#64, Flags.none)

/-- `NEG.D`: as `f32Neg`, for doubles. -/
def f64Neg (x : BitVec 64) : BitVec 64 × Flags :=
  if isNaN64 x then
    (if isQNaN64 x then x ^^^ 0x8000000000000000#64 else defaultQNaN64, Flags.invalidOnly)
  else (x ^^^ 0x8000000000000000#64, Flags.none)

/-! ## §8  Comparison (MD00086 `C.cond.fmt`) -/

/-- The IEEE relation between two operands: exactly one of `unordered`,
`less`, `equal` is set, or none of them (meaning "greater"). -/
structure FpRel where
  /-- At least one operand is a NaN. -/
  unordered : Bool
  /-- `a < b`. -/
  less : Bool
  /-- `a = b` (with `−0 = +0`). -/
  equal : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Generic relation of two bit patterns of format `f`. -/
def Format.relation (f : Format) (a b : Nat) : FpRel :=
  if f.isNaN a || f.isNaN b then ⟨true, false, false⟩
  else ⟨false, decide (f.orderKey a < f.orderKey b), decide (f.orderKey a = f.orderKey b)⟩

/-- Relation between two singles, from their bit patterns. -/
def f32Relation (a b : BitVec 32) : FpRel := binary32.relation a.toNat b.toNat

/-- Relation between two doubles, from their bit patterns. -/
def f64Relation (a b : BitVec 64) : FpRel := binary64.relation a.toNat b.toNat

/-- The `C.cond.fmt` predicate table: with `cond` the instruction's 4-bit
condition field,
`result = (cond₀ ∧ unordered) ∨ (cond₁ ∧ equal) ∨ (cond₂ ∧ less)`. -/
def fpCompare (cond : BitVec 4) (unordered less equal : Bool) : Bool :=
  (cond.getLsbD 0 && unordered) || (cond.getLsbD 1 && equal) || (cond.getLsbD 2 && less)

/-- Whether `C.cond.fmt` raises Invalid Operation: always when an operand is
a signaling NaN; for the signaling predicates (`cond₃ = 1`, codes 8..15) also
whenever the operands are unordered (i.e. on a quiet NaN too). -/
def fpCompareInvalid (cond : BitVec 4) (unordered anySNaN : Bool) : Bool :=
  anySNaN || (cond.getLsbD 3 && unordered)

/-- `C.cond.S`: the condition-code value to store, and the flags raised. -/
def f32Compare (cond : BitVec 4) (a b : BitVec 32) : Bool × Flags :=
  let r := f32Relation a b
  (fpCompare cond r.unordered r.less r.equal,
    { invalid := fpCompareInvalid cond r.unordered (isSNaN32 a || isSNaN32 b) })

/-- `C.cond.D`: the condition-code value to store, and the flags raised. -/
def f64Compare (cond : BitVec 4) (a b : BitVec 64) : Bool × Flags :=
  let r := f64Relation a b
  (fpCompare cond r.unordered r.less r.equal,
    { invalid := fpCompareInvalid cond r.unordered (isSNaN64 a || isSNaN64 b) })

/-! ### The IEEE relations as propositions on the fields

Specification vocabulary only: nothing in `Step.lean` uses these. `Semantics/FpCompareFacts.lean`
proves that `f32Relation`/`f64Relation` (and hence every `C.cond.fmt` predicate) agree with them
for all operands. -/

/-- At least one operand is a NaN. -/
def F32Unordered (a b : BitVec 32) : Prop := isNaN32 a = true ∨ isNaN32 b = true

/-- Magnitude order of two singles on their fields: `(exponent, fraction)` lexicographically. -/
def F32MagLt (a b : BitVec 32) : Prop :=
  expField32 a < expField32 b ∨ (expField32 a = expField32 b ∧ fracField32 a < fracField32 b)

/-- IEEE "less than" on singles, on the sign / exponent / fraction fields. -/
def F32Lt (a b : BitVec 32) : Prop :=
  isNaN32 a = false ∧ isNaN32 b = false ∧
    ((sign32 a = true ∧ sign32 b = false ∧ ¬(isZero32 a = true ∧ isZero32 b = true)) ∨
     (sign32 a = false ∧ sign32 b = false ∧ F32MagLt a b) ∨
     (sign32 a = true ∧ sign32 b = true ∧ F32MagLt b a))

/-- IEEE "equal" on singles: same bit pattern, or both zeros (`−0 = +0`). -/
def F32Eq (a b : BitVec 32) : Prop :=
  isNaN32 a = false ∧ isNaN32 b = false ∧ (a = b ∨ (isZero32 a = true ∧ isZero32 b = true))

/-- At least one operand is a NaN. -/
def F64Unordered (a b : BitVec 64) : Prop := isNaN64 a = true ∨ isNaN64 b = true

/-- Magnitude order of two doubles on their fields: `(exponent, fraction)` lexicographically. -/
def F64MagLt (a b : BitVec 64) : Prop :=
  expField64 a < expField64 b ∨ (expField64 a = expField64 b ∧ fracField64 a < fracField64 b)

/-- IEEE "less than" on doubles, on the sign / exponent / fraction fields. -/
def F64Lt (a b : BitVec 64) : Prop :=
  isNaN64 a = false ∧ isNaN64 b = false ∧
    ((sign64 a = true ∧ sign64 b = false ∧ ¬(isZero64 a = true ∧ isZero64 b = true)) ∨
     (sign64 a = false ∧ sign64 b = false ∧ F64MagLt a b) ∨
     (sign64 a = true ∧ sign64 b = true ∧ F64MagLt b a))

/-- IEEE "equal" on doubles: same bit pattern, or both zeros (`−0 = +0`). -/
def F64Eq (a b : BitVec 64) : Prop :=
  isNaN64 a = false ∧ isNaN64 b = false ∧ (a = b ∨ (isZero64 a = true ∧ isZero64 b = true))

/-! The sixteen named `C.cond.fmt` predicates as their 4-bit `cond` codes
(MD00086, `C.cond.fmt`, tables "FPU Comparisons Without/With Special Operand
Exceptions"). -/
namespace Cond
/-- `C.F` — always false. -/
def f : BitVec 4 := 0#4
/-- `C.UN` — unordered. -/
def un : BitVec 4 := 1#4
/-- `C.EQ` — equal. -/
def eq : BitVec 4 := 2#4
/-- `C.UEQ` — unordered or equal. -/
def ueq : BitVec 4 := 3#4
/-- `C.OLT` — ordered and less than. -/
def olt : BitVec 4 := 4#4
/-- `C.ULT` — unordered or less than. -/
def ult : BitVec 4 := 5#4
/-- `C.OLE` — ordered and less than or equal. -/
def ole : BitVec 4 := 6#4
/-- `C.ULE` — unordered or less than or equal. -/
def ule : BitVec 4 := 7#4
/-- `C.SF` — signaling false. -/
def sf : BitVec 4 := 8#4
/-- `C.NGLE` — not greater than, less than or equal (signaling `un`). -/
def ngle : BitVec 4 := 9#4
/-- `C.SEQ` — signaling equal. -/
def seq : BitVec 4 := 10#4
/-- `C.NGL` — not greater than or less than (signaling `ueq`). -/
def ngl : BitVec 4 := 11#4
/-- `C.LT` — less than (signaling `olt`). -/
def lt : BitVec 4 := 12#4
/-- `C.NGE` — not greater than or equal (signaling `ult`). -/
def nge : BitVec 4 := 13#4
/-- `C.LE` — less than or equal (signaling `ole`). -/
def le : BitVec 4 := 14#4
/-- `C.NGT` — not greater than (signaling `ule`). -/
def ngt : BitVec 4 := 15#4
/-- All sixteen, in code order. -/
def all : List (BitVec 4) :=
  [f, un, eq, ueq, olt, ult, ole, ule, sf, ngle, seq, ngl, lt, nge, le, ngt]
end Cond

/-! ## §9  FCSR and the `CFC1` / `CTC1` control-register views

The FCSR is modelled as a plain `BitVec 32` with the MD00082 Vol I layout:

```
 31..25   24  23   22..18   17..12    11..7     6..2    1..0
 FCC7..1  FS  FCC0   0      Cause     Enables   Flags   RM
                            E V Z O U I  V Z O U I  V Z O U I
                           17 …      12  11 …    7  6 …    2
```

Bits 22..18 are treated as reserved: they read as zero and ignore writes
(in Release 2 bits 22/21 are the optional implementation-dependent FN/FO
flush controls, and 20..18 are reserved). -/

/-- FCSR.RM field mask (bits 1..0). -/
def fcsrRMMask : BitVec 32 := 0x00000003#32
/-- FCSR.Flags field mask (bits 6..2). -/
def fcsrFlagsMask : BitVec 32 := 0x0000007C#32
/-- FCSR.Enables field mask (bits 11..7). -/
def fcsrEnablesMask : BitVec 32 := 0x00000F80#32
/-- FCSR.Cause field mask (bits 17..12, including E = bit 17). -/
def fcsrCauseMask : BitVec 32 := 0x0003F000#32
/-- FCSR reserved bits 22..18. -/
def fcsrReservedMask : BitVec 32 := 0x007C0000#32
/-- FCSR.FS (flush to zero), bit 24. -/
def fcsrFSMask : BitVec 32 := 0x01000000#32
/-- FCSR condition codes: FCC0 = bit 23, FCC1..7 = bits 25..31. -/
def fcsrFCCMask : BitVec 32 := 0xFE800000#32
/-- Every writable (non-reserved) FCSR bit. -/
def fcsrWritableMask : BitVec 32 := 0xFF83FFFF#32

/-- FCSR bit position of condition code `cc`: FCC0 is bit 23, FCC`n`
(1 ≤ n ≤ 7) is bit 24 + n. -/
def ccBit (cc : Fin 8) : Nat := if cc.val = 0 then 23 else 24 + cc.val

/-- Read floating-point condition code `cc`. -/
def getCC (fcsr : BitVec 32) (cc : Fin 8) : Bool := fcsr.getLsbD (ccBit cc)

/-- Write floating-point condition code `cc`. -/
def setCC (fcsr : BitVec 32) (cc : Fin 8) (b : Bool) : BitVec 32 :=
  if b then fcsr ||| (1#32 <<< ccBit cc) else fcsr &&& ~~~(1#32 <<< ccBit cc)

/-- Current rounding mode, FCSR.RM (bits 1..0). -/
def getRM (fcsr : BitVec 32) : RoundingMode :=
  RoundingMode.ofBits (fcsr.extractLsb' 0 2)

/-- Replace FCSR.RM. -/
def setRM (fcsr : BitVec 32) (rm : RoundingMode) : BitVec 32 :=
  (fcsr &&& ~~~fcsrRMMask) ||| rm.toBits.zeroExtend 32

/-- The sticky FCSR.Flags field (bits 6..2). -/
def getFlags (fcsr : BitVec 32) : Flags := Flags.ofBits (fcsr.extractLsb' 2 5)

/-- The FCSR.Enables field (bits 11..7). -/
def getEnables (fcsr : BitVec 32) : Flags := Flags.ofBits (fcsr.extractLsb' 7 5)

/-- The five IEEE bits of FCSR.Cause (bits 16..12). -/
def getCause (fcsr : BitVec 32) : Flags := Flags.ofBits (fcsr.extractLsb' 12 5)

/-- FCSR.Cause.E, Unimplemented Operation (bit 17). -/
def getCauseE (fcsr : BitVec 32) : Bool := fcsr.getLsbD 17

/-- FCSR.FS, flush-to-zero (bit 24). -/
def getFS (fcsr : BitVec 32) : Bool := fcsr.getLsbD 24

/-- Record the exceptions `f` raised by one FPU operation: FCSR.Cause becomes
*exactly* `f` (E cleared — so an operation raising nothing clears Cause), and
`f` is ORed into the sticky FCSR.Flags.  All other fields are unchanged.
Whether a trap must be taken is reported separately by `fpeEnabled`. -/
def raiseFlags (fcsr : BitVec 32) (f : Flags) : BitVec 32 :=
  let b : BitVec 32 := f.toBits.zeroExtend 32
  (fcsr &&& ~~~fcsrCauseMask) ||| (b <<< 12) ||| (b <<< 2)

/-- `true` iff one of the exceptions in `f` has its FCSR.Enables bit set, in
which case the instruction must take a Floating-Point exception
(Cause.ExcCode = `fpeExcCode`) instead of completing. -/
def fpeEnabled (fcsr : BitVec 32) (f : Flags) : Bool :=
  (f.toBits &&& fcsr.extractLsb' 7 5) != 0#5

/-- Cause.ExcCode of the Floating-Point exception (FPE). -/
def fpeExcCode : Nat := 15

/-- Hardware-precise variant of `raiseFlags` + `fpeEnabled`: Cause is set to
exactly `f`; if an enabled exception is among them the sticky Flags are left
untouched and `true` (trap) is returned — the destination register must then
not be written — otherwise `f` is ORed into Flags and `false` is returned. -/
def fpUpdate (fcsr : BitVec 32) (f : Flags) : BitVec 32 × Bool :=
  if fpeEnabled fcsr f then
    ((fcsr &&& ~~~fcsrCauseMask) ||| ((f.toBits.zeroExtend 32 : BitVec 32) <<< 12), true)
  else (raiseFlags fcsr f, false)

/-- FCSR.Cause set to *exactly* `f` (E cleared), every other bit unchanged — the
Cause write of one operation of an instruction made of several FP operations
(`MADD.fmt` … `NMSUB.fmt`), without the Flags update, which is made only when
the whole instruction completes ("The Cause bits are ORed into the Flag bits if
no exception is taken", MD00086 Vol II-A Rev 6.06, MADD.fmt p.256; "instructions
that trap do not update the Flag bits", MD00082 Vol I-A Rev 6.01 §6.7.1, p.99).
It is the FCSR `fpUpdate` gives when it traps. -/
def setCause (fcsr : BitVec 32) (f : Flags) : BitVec 32 :=
  (fcsr &&& ~~~fcsrCauseMask) ||| ((f.toBits.zeroExtend 32 : BitVec 32) <<< 12)

/-- The result of one operation of a multi-operation instruction with its
exceptions joined to those `acc` of the operations before it: FCSR.Cause
reports the conditions that arose "during the execution of an instruction"
(MD00082 Vol I-A Rev 6.01, Table 6.8 `Cause`, p.94), so after the operations
`o₁ … oₙ` it is the union of their exceptions. -/
def accFlags {α : Type} (acc : Flags) (r : α × Flags) : α × Flags := (r.1, acc.or r.2)

/-- After a `CTC1` write: a Floating-Point exception is taken if any Cause bit
is set whose Enable bit is also set, or if Cause.E (always enabled) is set
(MD00086 `CTC1`). -/
def fcsrTrapPending (fcsr : BitVec 32) : Bool :=
  getCauseE fcsr || (fcsr.extractLsb' 12 5 &&& fcsr.extractLsb' 7 5) != 0#5

/-- The value read from FIR (control register 0), a read-only constant
(MD00082 Vol I-A Rev 6.01 §6.5.1, Figure 6.11 / Table 6.5, p.88-90):
`0x00330000` = `S` (bit 16), `D` (bit 17), `W` (bit 20) and `L` (bit 21) implemented;
`F64` (22) = 0, a 32-bit FPU; `Has2008` (23) = 0, legacy NaN encoding and
arithmetic `ABS`/`NEG`; `PS` (18) = `3D` (19) = 0; `UFRP` = `FREP` = 0;
`Impl`, `ProcessorID` and `Revision` zero.

`L` = 1 is forced by the manual: every allowed pre-Release 6 FPU subset that has `D`
also has `L` (MD00086 Vol II-A Rev 6.06 §3.1, p.30: "FIR.S=FIR.L=FIR.D=FIR.L=1";
MD00082 Vol I-A Rev 6.01 Table 6.4, p.85: Release 2, 32-bit FPU: "FIRD=1 and FIRL=1
required"). The manual is inconsistent with itself here: the L-format instruction
pages (e.g. CVT.L.fmt, MD00086 p.154) say the result "is UNPREDICTABLE if the
processor is executing in the FR=0 32-bit FPU register model". The model's reading
(SPEC-NOTES, item `FIR.L`): `FIR.L = 1` as the subsets require, and the L-format
instructions (`CVT.L.fmt`, `CVT.fmt.L`, `ROUND/TRUNC/CEIL/FLOOR.L.fmt`) are
not implemented: they decode as Reserved Instruction, a pin of their UNPREDICTABLE
result with `FR` = 0. -/
def firValue : BitVec 32 := 0x00330000#32

/-- FCSR as read through register 31: reserved bits 22..18 read as zero. -/
def readFCSR (fcsr : BitVec 32) : BitVec 32 := fcsr &&& fcsrWritableMask

/-- `CTC1` to register 31: every non-reserved bit is replaced. -/
def writeFCSR (_fcsr v : BitVec 32) : BitVec 32 := v &&& fcsrWritableMask

/-- FCCR (register 25): the eight condition codes, FCC`n` in bit `n`. -/
def readFCCR (fcsr : BitVec 32) : BitVec 32 :=
  ((fcsr >>> 24) &&& 0xFE#32) ||| ((fcsr >>> 23) &&& 1#32)

/-- `CTC1` to FCCR: replaces the eight condition codes, nothing else. -/
def writeFCCR (fcsr v : BitVec 32) : BitVec 32 :=
  (fcsr &&& ~~~fcsrFCCMask) ||| ((v &&& 0xFE#32) <<< 24) ||| ((v &&& 1#32) <<< 23)

/-- FEXR (register 26): Cause (17..12) and Flags (6..2), in their FCSR
positions. -/
def readFEXR (fcsr : BitVec 32) : BitVec 32 := fcsr &&& (fcsrCauseMask ||| fcsrFlagsMask)

/-- `CTC1` to FEXR: replaces Cause and Flags, nothing else. -/
def writeFEXR (fcsr v : BitVec 32) : BitVec 32 :=
  (fcsr &&& ~~~(fcsrCauseMask ||| fcsrFlagsMask)) ||| (v &&& (fcsrCauseMask ||| fcsrFlagsMask))

/-- FENR (register 28): Enables (11..7) and RM (1..0) in their FCSR
positions, FS in bit 2. -/
def readFENR (fcsr : BitVec 32) : BitVec 32 :=
  (fcsr &&& (fcsrEnablesMask ||| fcsrRMMask)) ||| ((fcsr >>> 22) &&& 4#32)

/-- `CTC1` to FENR: replaces Enables, FS and RM, nothing else. -/
def writeFENR (fcsr v : BitVec 32) : BitVec 32 :=
  (fcsr &&& ~~~(fcsrEnablesMask ||| fcsrRMMask ||| fcsrFSMask)) |||
    (v &&& (fcsrEnablesMask ||| fcsrRMMask)) ||| ((v &&& 4#32) <<< 22)

/-- `CFC1 rt, fs`: the value of FPU control register `reg` (0 = FIR,
25 = FCCR, 26 = FEXR, 28 = FENR, 31 = FCSR).  `none` for every other register
number, which the manual leaves UNPREDICTABLE. -/
def readControl (fcsr : BitVec 32) (reg : Nat) : Option (BitVec 32) :=
  match reg with
  | 0 => some firValue
  | 25 => some (readFCCR fcsr)
  | 26 => some (readFEXR fcsr)
  | 28 => some (readFENR fcsr)
  | 31 => some (readFCSR fcsr)
  | _ => none

/-- `CTC1 rt, fs`: the new FCSR after writing `v` to FPU control register
`reg`.  FIR (0) is read-only, so the write is ignored; `none` for register
numbers the manual leaves UNPREDICTABLE.  After a successful write the caller
must check `fcsrTrapPending` on the result. -/
def writeControl (fcsr : BitVec 32) (reg : Nat) (v : BitVec 32) : Option (BitVec 32) :=
  match reg with
  | 0 => some fcsr
  | 25 => some (writeFCCR fcsr v)
  | 26 => some (writeFEXR fcsr v)
  | 28 => some (writeFENR fcsr v)
  | 31 => some (writeFCSR fcsr v)
  | _ => none

/-- The arithmetic environment selected by an FCSR value: `RM`, `Enables`
and `FS`. -/
def envOf (fcsr : BitVec 32) : Env :=
  { rm := getRM fcsr, enables := getEnables fcsr, flush := getFS fcsr }

/-! ## §9a  Arithmetic: add, subtract, multiply, divide, square root

Every operation computes the **exact** result as an `Exact` (a dyadic
rational; for division and square root a quotient/root with enough extra bits
plus a sticky bit, which rounds identically) and rounds it **once** with
`Format.roundEnv`. Special operands follow MD00082 Vol I-A Rev 6.01:

* §6.3.1.4 (p.81): "SNaN operands cause the Invalid Operation exception for
  arithmetic operations."
* §6.3.1.5 (p.82): "QNaN operands do not cause arithmetic operations to signal
  an exception. When a floating-point result is to be delivered, a QNaN
  operand causes an arithmetic operation to supply a QNaN result. When
  possible, this QNaN result is one of the operand QNaN values." and
  "Table 6.3 shows the QNaN value generated when no input operand QNaN value
  can be copied."
* §6.7.2.1 (p.100): the invalid operations (∞ − ∞, 0 × ∞, 0/0, ∞/∞, square
  root of a value less than 0); §6.7.2.2 (p.100): Division By Zero "if the
  divisor is zero and the dividend is a finite nonzero number", result "a
  correctly signed infinity".

`nanResult` implements the NaN rule: the result is the **first quiet NaN
operand, in the instruction's operand order** (`fs` before `ft`), returned
unchanged; if no operand is a quiet NaN (all NaN operands are signaling) the
default QNaN is created. The manual does not say which operand wins when two
are quiet NaNs; "first operand" is a model pin.

Subnormal *operands* are never flushed (with FCSR.FS = 1 this is
"implementation-dependent" before Release 5, §6.7.2.4 p.102; pinned: not
flushed). The model never raises Unimplemented Operation. -/

/-- Integer square root by binary digit recurrence, structural on the bit
index: `isqrtAux n i r` extends the partial root `r` with bits `i-1 … 0`. -/
def isqrtAux (n : Nat) : Nat → Nat → Nat
  | 0, r => r
  | i + 1, r =>
    let c := r + 2 ^ i
    if c * c ≤ n then isqrtAux n i c else isqrtAux n i r

/-- `⌊√n⌋` (the root has at most `⌈bitLen n / 2⌉` bits). -/
def isqrt (n : Nat) : Nat := isqrtAux n ((bitLen n + 1) / 2) 0

namespace Exact

/-- Exact sum. An exact zero sum of operands with opposite signs is `+0`,
except `−0` when rounding toward −∞; equal-signed zeros keep their sign
(IEEE-754 §6.3). -/
def add (rm : RoundingMode) (a b : Exact) : Exact :=
  let e : Int := if a.exp ≤ b.exp then a.exp else b.exp
  let ma : Int := ((a.sig * 2 ^ (a.exp - e).toNat : Nat) : Int)
  let mb : Int := ((b.sig * 2 ^ (b.exp - e).toNat : Nat) : Int)
  let s : Int := (if a.sign then -ma else ma) + (if b.sign then -mb else mb)
  if s = 0 then ⟨if a.sign == b.sign then a.sign else decide (rm = .RM), 0, e⟩
  else ⟨decide (s < 0), s.natAbs, e⟩

/-- Exact product. -/
def mul (a b : Exact) : Exact := ⟨a.sign != b.sign, a.sig * b.sig, a.exp + b.exp⟩

/-- Quotient `a / b` (`b.sig ≠ 0`) to at least `prec + 2` significant bits,
with a sticky least-significant bit recording a nonzero remainder: it rounds
to `prec` (or fewer) bits exactly as the true quotient does. -/
def div (prec : Nat) (a b : Exact) : Exact :=
  let k := prec + 2 + bitLen b.sig
  let n := a.sig * 2 ^ k
  ⟨a.sign != b.sign, 2 * (n / b.sig) + (if n % b.sig = 0 then 0 else 1),
    a.exp - b.exp - (k : Int) - 1⟩

/-- Square root of a positive value to at least `prec + 2` significant bits,
with a sticky least-significant bit recording inexactness of the integer
root. -/
def sqrt (prec : Nat) (a : Exact) : Exact :=
  let sh : Nat := 2 * (prec + 2) + (if a.exp % 2 = 0 then 0 else 1)
  let n := a.sig * 2 ^ sh
  let r := isqrt n
  ⟨false, 2 * r + (if r * r = n then 0 else 1), (a.exp - (sh : Int)) / 2 - 1⟩

end Exact

namespace Format

/-- The NaN delivered by an arithmetic operation with operands `ops` (in
operand order): the first quiet NaN operand, else the default QNaN. -/
def nanResult (f : Format) (ops : List Nat) : Nat :=
  match ops.find? (fun x => f.isQNaN x) with
  | some q => q
  | none => f.defaultQNaN

/-- Flags of an arithmetic operation with a NaN operand: Invalid iff some
operand is a signaling NaN. -/
def nanFlags (f : Format) (ops : List Nat) : Flags :=
  { invalid := ops.any (fun x => f.isSNaN x) }

/-- Flip the sign bit of an in-range bit pattern. -/
def negBits (f : Format) (n : Nat) : Nat :=
  if f.signBit n then n - 2 ^ (f.expBits + f.fracBits) else n + 2 ^ (f.expBits + f.fracBits)

/-- The pattern of `+1.0`. -/
def one (f : Format) : Nat := f.pack false f.bias 0

/-- Sum of two non-NaN operands. -/
def addCore (f : Format) (e : Env) (a b : Nat) : Nat × Flags :=
  if f.isInf a then
    if f.isInf b && (f.signBit a != f.signBit b) then (f.defaultQNaN, Flags.invalidOnly)
    else (a, Flags.none)
  else if f.isInf b then (b, Flags.none)
  else f.roundEnv e (Exact.add e.rm (f.toExact a) (f.toExact b))

/-- `ADD.fmt`: `a + b`. -/
def add (f : Format) (e : Env) (a b : Nat) : Nat × Flags :=
  if f.isNaN a || f.isNaN b then (f.nanResult [a, b], f.nanFlags [a, b])
  else f.addCore e a b

/-- `SUB.fmt`: `a − b`. -/
def sub (f : Format) (e : Env) (a b : Nat) : Nat × Flags :=
  if f.isNaN a || f.isNaN b then (f.nanResult [a, b], f.nanFlags [a, b])
  else f.addCore e a (f.negBits b)

/-- `MUL.fmt`: `a × b`. -/
def mul (f : Format) (e : Env) (a b : Nat) : Nat × Flags :=
  if f.isNaN a || f.isNaN b then (f.nanResult [a, b], f.nanFlags [a, b])
  else if (f.isInf a && f.isZero b) || (f.isZero a && f.isInf b) then
    (f.defaultQNaN, Flags.invalidOnly)
  else if f.isInf a || f.isInf b then (f.inf (f.signBit a != f.signBit b), Flags.none)
  else f.roundEnv e (Exact.mul (f.toExact a) (f.toExact b))

/-- `DIV.fmt`: `a / b`. -/
def div (f : Format) (e : Env) (a b : Nat) : Nat × Flags :=
  if f.isNaN a || f.isNaN b then (f.nanResult [a, b], f.nanFlags [a, b])
  else if (f.isInf a && f.isInf b) || (f.isZero a && f.isZero b) then
    (f.defaultQNaN, Flags.invalidOnly)
  else if f.isInf a then (f.inf (f.signBit a != f.signBit b), Flags.none)
  else if f.isInf b then (f.zero (f.signBit a != f.signBit b), Flags.none)
  else if f.isZero b then (f.inf (f.signBit a != f.signBit b), { divZero := true })
  else if f.isZero a then (f.zero (f.signBit a != f.signBit b), Flags.none)
  else f.roundEnv e (Exact.div (f.fracBits + 1) (f.toExact a) (f.toExact b))

/-- `SQRT.fmt`: `√a`. "If the value in FPR fs corresponds to −0, the result is
−0"; "If the value in FPR fs is less than 0, an Invalid Operation condition is
raised" (MD00086 Vol II-A Rev 6.06, SQRT.fmt, p.382). -/
def sqrt (f : Format) (e : Env) (a : Nat) : Nat × Flags :=
  if f.isNaN a then (f.nanResult [a], f.nanFlags [a])
  else if f.isZero a then (a, Flags.none)
  else if f.signBit a then (f.defaultQNaN, Flags.invalidOnly)
  else if f.isInf a then (a, Flags.none)
  else f.roundEnv e (Exact.sqrt (f.fracBits + 1) (f.toExact a))

end Format

/-! ### Single precision -/

/-- `ADD.S`. -/
def f32Add (e : Env) (a b : BitVec 32) : BitVec 32 × Flags :=
  let r := binary32.add e a.toNat b.toNat
  (BitVec.ofNat 32 r.1, r.2)
/-- `SUB.S`. -/
def f32Sub (e : Env) (a b : BitVec 32) : BitVec 32 × Flags :=
  let r := binary32.sub e a.toNat b.toNat
  (BitVec.ofNat 32 r.1, r.2)
/-- `MUL.S`. -/
def f32Mul (e : Env) (a b : BitVec 32) : BitVec 32 × Flags :=
  let r := binary32.mul e a.toNat b.toNat
  (BitVec.ofNat 32 r.1, r.2)
/-- `DIV.S`. -/
def f32Div (e : Env) (a b : BitVec 32) : BitVec 32 × Flags :=
  let r := binary32.div e a.toNat b.toNat
  (BitVec.ofNat 32 r.1, r.2)
/-- `SQRT.S`. -/
def f32Sqrt (e : Env) (a : BitVec 32) : BitVec 32 × Flags :=
  let r := binary32.sqrt e a.toNat
  (BitVec.ofNat 32 r.1, r.2)

/-! ### Double precision -/

/-- `ADD.D`. -/
def f64Add (e : Env) (a b : BitVec 64) : BitVec 64 × Flags :=
  let r := binary64.add e a.toNat b.toNat
  (BitVec.ofNat 64 r.1, r.2)
/-- `SUB.D`. -/
def f64Sub (e : Env) (a b : BitVec 64) : BitVec 64 × Flags :=
  let r := binary64.sub e a.toNat b.toNat
  (BitVec.ofNat 64 r.1, r.2)
/-- `MUL.D`. -/
def f64Mul (e : Env) (a b : BitVec 64) : BitVec 64 × Flags :=
  let r := binary64.mul e a.toNat b.toNat
  (BitVec.ofNat 64 r.1, r.2)
/-- `DIV.D`. -/
def f64Div (e : Env) (a b : BitVec 64) : BitVec 64 × Flags :=
  let r := binary64.div e a.toNat b.toNat
  (BitVec.ofNat 64 r.1, r.2)
/-- `SQRT.D`. -/
def f64Sqrt (e : Env) (a : BitVec 64) : BitVec 64 × Flags :=
  let r := binary64.sqrt e a.toNat
  (BitVec.ofNat 64 r.1, r.2)

/-! ### Multiply-add family, reciprocal, reciprocal square root

MD00086 Vol II-A Rev 6.06, MADD.fmt (p.256): "The intermediate product is
rounded according to the current rounding mode in FCSR. The value in FPR fr is
added to the product. The result sum is calculated to infinite precision,
rounded according to the current rounding mode in FCSR … The results and
flags are as if separate floating-point multiply and add instructions were
executed." — i.e. **unfused**, two roundings. NMADD.fmt (p.308) / NMSUB.fmt
(p.310): "… as if separate floating-point multiply and add and negate
instructions were executed", so the final negation is the (legacy, arithmetic)
`NEG.fmt`, which signals Invalid for a NaN. The functions below give the
result value and the union of the IEEE exceptions of the steps — the FCSR
Cause of an untrapped multiply-add (Table 6.8 `Cause`, MD00082 Vol I-A Rev 6.01
p.94: set "if the corresponding exception condition arises during the
execution of an instruction"). `step` runs the steps one after the other
(`Step.lean`, `fpStep`): each writes Cause with the union so far and is
trap-checked, so a trapping multiply stops the instruction with the multiply's
Cause; Flags are updated with the union only when no step traps.

RECIP.fmt (p.336) and RSQRT.fmt (p.343) leave the accuracy
implementation-dependent (within 1 resp. 2 ulp) and "it is implementation
dependent whether the result is affected by the current rounding mode". Model
pin: `recip x = 1.0 / x` by `DIV.fmt`, and `rsqrt x = 1.0 / sqrt x` by
`SQRT.fmt` then `DIV.fmt` (flags ORed), both under the current FCSR
environment. -/

/-- `MADD.S`: `(fs × ft) + fr`, unfused. -/
def f32Madd (e : Env) (fr fs ft : BitVec 32) : BitVec 32 × Flags :=
  let m := f32Mul e fs ft
  let r := f32Add e m.1 fr
  (r.1, m.2.or r.2)
/-- `MSUB.S`: `(fs × ft) − fr`, unfused. -/
def f32Msub (e : Env) (fr fs ft : BitVec 32) : BitVec 32 × Flags :=
  let m := f32Mul e fs ft
  let r := f32Sub e m.1 fr
  (r.1, m.2.or r.2)
/-- `NMADD.S`: `−(fr + (fs × ft))`, the printed operand order of NMADD.fmt
(p.308; it decides which QNaN is returned when `fr` and the product are both
QNaNs). -/
def f32Nmadd (e : Env) (fr fs ft : BitVec 32) : BitVec 32 × Flags :=
  let m := f32Mul e fs ft
  let r := f32Add e fr m.1
  let n := f32Neg r.1
  (n.1, (m.2.or r.2).or n.2)
/-- `NMSUB.S`: `−((fs × ft) − fr)`. -/
def f32Nmsub (e : Env) (fr fs ft : BitVec 32) : BitVec 32 × Flags :=
  let r := f32Msub e fr fs ft
  let n := f32Neg r.1
  (n.1, r.2.or n.2)
/-- `RECIP.S`: `1.0 / x`. -/
def f32Recip (e : Env) (x : BitVec 32) : BitVec 32 × Flags := f32Div e 0x3F800000#32 x
/-- `RSQRT.S`: `1.0 / sqrt x`. -/
def f32Rsqrt (e : Env) (x : BitVec 32) : BitVec 32 × Flags :=
  let q := f32Sqrt e x
  let r := f32Div e 0x3F800000#32 q.1
  (r.1, q.2.or r.2)

/-- `MADD.D`. -/
def f64Madd (e : Env) (fr fs ft : BitVec 64) : BitVec 64 × Flags :=
  let m := f64Mul e fs ft
  let r := f64Add e m.1 fr
  (r.1, m.2.or r.2)
/-- `MSUB.D`. -/
def f64Msub (e : Env) (fr fs ft : BitVec 64) : BitVec 64 × Flags :=
  let m := f64Mul e fs ft
  let r := f64Sub e m.1 fr
  (r.1, m.2.or r.2)
/-- `NMADD.D`: `−(fr + (fs × ft))` (printed operand order, p.308). -/
def f64Nmadd (e : Env) (fr fs ft : BitVec 64) : BitVec 64 × Flags :=
  let m := f64Mul e fs ft
  let r := f64Add e fr m.1
  let n := f64Neg r.1
  (n.1, (m.2.or r.2).or n.2)
/-- `NMSUB.D`. -/
def f64Nmsub (e : Env) (fr fs ft : BitVec 64) : BitVec 64 × Flags :=
  let r := f64Msub e fr fs ft
  let n := f64Neg r.1
  (n.1, r.2.or n.2)
/-- `RECIP.D`. -/
def f64Recip (e : Env) (x : BitVec 64) : BitVec 64 × Flags :=
  f64Div e 0x3FF0000000000000#64 x
/-- `RSQRT.D`. -/
def f64Rsqrt (e : Env) (x : BitVec 64) : BitVec 64 × Flags :=
  let q := f64Sqrt e x
  let r := f64Div e 0x3FF0000000000000#64 q.1
  (r.1, q.2.or r.2)

/-- `CVT.D.W` with flags (always exact: no flag is ever raised). -/
def w32ToF64F (x : BitVec 32) : BitVec 64 × Flags := (w32ToF64 x, Flags.none)

end Mips.Fp
