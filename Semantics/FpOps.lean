import Semantics.Word

/-!
# FpOps — pure bit-level IEEE-754 helpers for the MIPS32r2 FPU (COP1)

Everything in this file is a *total, kernel-reducible* function over
`BitVec 32` / `BitVec 64` (internally: over `Nat`/`Int`, whose arithmetic the
kernel evaluates natively).  No `Float`/`Float32` appears in any definition
(they appear only in the differential-test block at the very end, as an
oracle), so every fact below can be proved by `decide`/`rfl`/`simp`.

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
| §10 | kernel-checked theorems | |
| §11 | differential tests against Lean's `Float32`/`Float` | |

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
ABS.fmt, p.32). The untrapped default result of Invalid Operation is a quiet
NaN (MD00082 Vol I-A Rev 6.01 Table 6.14, p.100), and "when possible, this
QNaN result is one of the operand QNaN values" (§6.3.1.5, p.82): a quiet NaN
operand is returned unchanged, a signaling one gives the default QNaN.
Otherwise the sign bit is cleared. -/
def f32Abs (x : BitVec 32) : BitVec 32 × Flags :=
  if isNaN32 x then (if isQNaN32 x then x else defaultQNaN32, Flags.invalidOnly)
  else (x &&& 0x7FFFFFFF#32, Flags.none)

/-- `NEG.S` (arithmetic, as `f32Abs`; MD00086 Vol II-A Rev 6.06, NEG.fmt,
p.307): any NaN signals Invalid (quiet NaN operand returned unchanged,
signaling ↦ default QNaN); otherwise flip the sign bit. -/
def f32Neg (x : BitVec 32) : BitVec 32 × Flags :=
  if isNaN32 x then (if isQNaN32 x then x else defaultQNaN32, Flags.invalidOnly)
  else (x ^^^ 0x80000000#32, Flags.none)

/-- `ABS.D`: as `f32Abs`, for doubles. -/
def f64Abs (x : BitVec 64) : BitVec 64 × Flags :=
  if isNaN64 x then (if isQNaN64 x then x else defaultQNaN64, Flags.invalidOnly)
  else (x &&& 0x7FFFFFFFFFFFFFFF#64, Flags.none)

/-- `NEG.D`: as `f32Neg`, for doubles. -/
def f64Neg (x : BitVec 64) : BitVec 64 × Flags :=
  if isNaN64 x then (if isQNaN64 x then x else defaultQNaN64, Flags.invalidOnly)
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

/-- After a `CTC1` write: a Floating-Point exception is taken if any Cause bit
is set whose Enable bit is also set, or if Cause.E (always enabled) is set
(MD00086 `CTC1`). -/
def fcsrTrapPending (fcsr : BitVec 32) : Bool :=
  getCauseE fcsr || (fcsr.extractLsb' 12 5 &&& fcsr.extractLsb' 7 5) != 0#5

/-- The value read from FIR (control register 0), a read-only constant
(MD00082 Vol I-A Rev 6.01 §6.5.1, Figure 6.11 / Table 6.5, p.88-90):
`0x00130000` = `S` (bit 16), `D` (bit 17) and `W` (bit 20) implemented;
`F64` (22) = 0, a 32-bit FPU; `Has2008` (23) = 0, legacy NaN encoding and
arithmetic `ABS`/`NEG`; `PS` (18) = `3D` (19) = 0; `UFRP` = `FREP` = 0;
`Impl`, `ProcessorID` and `Revision` zero.

`L` (bit 21) is **0**. The manual is inconsistent here: Table 6.4 (p.85) says
a Release 2 32-bit FPU requires "FIR.D=1 and FIR.L=1", while every L-format
instruction page (e.g. MD00086 Vol II-A Rev 6.06, CVT.L.fmt, p.154) says the
result "is UNPREDICTABLE if the processor is executing in the FR=0 32-bit FPU
register model". The model does not implement the L format (no instruction
could have predictable results), so it reports `L = 0` rather than advertise a
data type it lacks. -/
def firValue : BitVec 32 := 0x00130000#32

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
executed." — i.e. **unfused**, two roundings; the flags of both steps are
ORed. NMADD.fmt (p.308) / NMSUB.fmt: "… as if separate floating-point multiply
and add and negate instructions were executed", so the final negation is the
(legacy, arithmetic) `NEG.fmt`, which signals Invalid for a NaN.

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
/-- `NMADD.S`: `−((fs × ft) + fr)`. -/
def f32Nmadd (e : Env) (fr fs ft : BitVec 32) : BitVec 32 × Flags :=
  let r := f32Madd e fr fs ft
  let n := f32Neg r.1
  (n.1, r.2.or n.2)
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
/-- `NMADD.D`. -/
def f64Nmadd (e : Env) (fr fs ft : BitVec 64) : BitVec 64 × Flags :=
  let r := f64Madd e fr fs ft
  let n := f64Neg r.1
  (n.1, r.2.or n.2)
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
