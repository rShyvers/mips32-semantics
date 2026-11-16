import Semantics.FpOps

/-!
# FpOpsSpec — the IEEE 754 reference the rounding core is proved against

Specification vocabulary only (definitions, no theorem): nothing in `Step.lean` or `FpOps.lean` uses
it. `Semantics/FpOpsCorrect*.lean` proves that the rounding core of `FpOps.lean`
(`Mips.Fp.Format.roundCore`) and the arithmetic built on it meet these definitions. The definitions
are written from the manual and the IEEE standard it references, **not** from `roundCore`. Where the text
below cites "IEEE Std 754-2019", the clause was looked up in the owner's licensed copy (local-only, see
`manuals/LOCAL-SOURCES.md`; `mipsdoc.py section ieee X`) and the behaviour checked against it
(table in SPEC-NOTES §9 item 30). The MIPS manual names IEEE 754-1985, whose text is not available here, so
the citations say "verified against 2019" and nothing about 1985:

* `Format.value` — the value of an encoding: MD00082 Vol I-A Rev 6.01 §6.3, Table 6.1 (p.78-79:
  `p`, `E_max`, `E_min`, the bias, the field widths), Table 6.2 (p.80-81: "Value V" of a normalized
  number `(-1)^s × 2^E × 1.f`, of a denormalized number `(-1)^s × 2^E_min × 0.f`, of `±0`; `E_max + 1`
  is ±∞ or a NaN, which have no value here), with `E = e - bias` the unbiased exponent (p.79: "Biased
  exponent, e=E + bias").
* The representable values and the rounding directions: MD00082 Vol I-A Rev 6.01 Table 6.10 (p.95):
  "RN - Round to Nearest. Rounds the result to the nearest representable value. When two
  representable values are equally near, the result is rounded to the value whose least significant
  bit is zero (that is, even)"; "RZ - Round Toward Zero. Rounds the result to the value closest to but
  not greater than in magnitude than the result"; "RP - Round Towards Plus Infinity. Rounds the result
  to the value closest to but not less than the result"; "RM - Round Towards Minus Infinity. Rounds the
  result to the value closest to but not greater than the result".
* Overflow: §6.7.2.5 (p.102): "An Overflow exception is signaled when the magnitude of a rounded
  floating point result, were the exponent range unbounded, is larger than the destination format's
  largest finite number"; the delivered value: Table 6.14 (p.100).
* Underflow: §6.7.2.3 (p.101): tininess "After rounding, when a nonzero result computed as though the
  exponent range were unbounded would lie strictly between ±2^E_min"; "The MIPS architecture specifies
  that tininess be detected after rounding"; "loss of accuracy is detected as inexact result". IEEE Std
  754-2019 §7.5 (p.53) permits either "after rounding" or "before rounding" ("The implementer shall choose
  how tininess is detected, but shall detect tininess in the same way for all operations in radix two"),
  so the MIPS pin is one of the allowed choices (verified against 2019).
* Inexact: §6.7.2.6 (p.102): "The rounded result of an operation is not exact".

**The exact result as a cut.** An exact result need not be rational (a square root), so it is given by
its order relation with the rationals (`Cut`: `le y` means `y ≤ v`, `ge y` means `v ≤ y`).
`Cut.ofRat v` is a rational `v`, `Cut.sqrt x` is `√x`. "Nearest" is phrased with midpoints, which
needs only these comparisons: for representable `y < r`, `r` is at least as near to `v` as `y` iff
`(y + r) / 2 ≤ v` (`Mips.Fp.nearest_ofRat_iff` in `FpOpsCorrectGrid.lean` proves this equals the
`|r - v| ≤ |y - v|` form for a rational `v`).

**"Even".** With the set of representable values of precision `p` and least exponent `qmin`, the
values whose least significant significand bit is zero are exactly those representable with
precision `p - 1` and least exponent `qmin + 1` (the sets `*Even` below): `j·2^q` with `j` even is
`(j/2)·2^(q+1)`.
-/

namespace Mips.Fp

/-! ## Exact values -/

/-- The rational value of an `Exact`: `(-1)^sign × sig × 2^exp`. -/
def Exact.toRat (v : Exact) : Rat := (if v.sign then -1 else 1) * (v.sig : Rat) * (2 : Rat) ^ v.exp

namespace Format

/-- Bits of mantissa precision `p` (Table 6.1, p.78: 24 / 53): the fraction bits and the hidden bit. -/
def prec (f : Format) : Nat := f.fracBits + 1

/-- Total format width (Table 6.1, p.79: 32 / 64). -/
def width (f : Format) : Nat := 1 + f.expBits + f.fracBits

/-- `E_min` (Table 6.1, p.79: -126 / -1022). -/
def emin (f : Format) : Int := 1 - (2 ^ (f.expBits - 1) - 1 : Nat)

/-- `E_max` (Table 6.1, p.78: +127 / +1023), equal to the bias. -/
def emax (f : Format) : Int := (2 ^ (f.expBits - 1) - 1 : Nat)

/-- **The value of an encoding** (Table 6.2, p.80-81), `none` for ±∞, the NaNs, and a number that is
not a `width`-bit pattern. Fields: sign `s` = bit `width - 1`, biased exponent `e` = the next
`expBits` bits, fraction `f` = the low `fracBits` bits (Figures 6.1, 6.2, p.80). -/
def value (f : Format) (n : Nat) : Option Rat :=
  if n < 2 ^ f.width then
    let s : Rat := if (n / 2 ^ (f.expBits + f.fracBits)) % 2 = 1 then -1 else 1
    let e : Nat := (n / 2 ^ f.fracBits) % 2 ^ f.expBits
    let fr : Rat := ((n % 2 ^ f.fracBits : Nat) : Rat) / (2 : Rat) ^ f.fracBits
    if e = 2 ^ f.expBits - 1 then none                 -- E_max + 1: ±∞, NaN
    else if e = 0 then some (s * (2 : Rat) ^ f.emin * fr)  -- E_min - 1: ±0, denormalized, 0.f
    else some (s * (2 : Rat) ^ ((e : Int) - f.emax) * (1 + fr)) -- normalized, 1.f
  else none

/-- The finite values of the format: the values of its encodings. -/
def Representable (f : Format) (x : Rat) : Prop := ∃ n, f.value n = some x

end Format

/-- **Precision-`p` binary values with exponent restricted by `P`**: `m × 2^e` with `|m| < 2^p`
and `P e`. -/
def Grid (p : Nat) (P : Int → Prop) (x : Rat) : Prop :=
  ∃ m : Int, ∃ e : Int, m.natAbs < 2 ^ p ∧ P e ∧ x = (m : Rat) * (2 : Rat) ^ e

namespace Format

/-- The exponent of the unit in the last place of the denormalized numbers: `E_min - (p - 1)`. -/
def ulpMin (f : Format) : Int := f.emin - f.fracBits

/-- **The values of the format with the exponent range unbounded above** (IEEE Std 754-2019 §7.4, p.53:
overflow is signaled when the largest finite number "is exceeded in magnitude by what would have been the
rounded floating-point result ... were the exponent range unbounded"; the rounding itself: §4.3, p.27):
precision `p`, the denormalized range kept. -/
def Unbounded (f : Format) : Rat → Prop := Grid f.prec (fun e => f.ulpMin ≤ e)

/-- The "even" values among `Unbounded` (least significant significand bit zero). -/
def UnboundedEven (f : Format) : Rat → Prop := Grid (f.prec - 1) (fun e => f.ulpMin + 1 ≤ e)

/-- **Precision `p`, exponent range unbounded both ways** (§6.7.2.3, p.101: tininess "after
rounding, when a nonzero result computed as though the exponent range were unbounded …"). -/
def UnboundedRange (f : Format) : Rat → Prop := Grid f.prec (fun _ => True)

/-- The "even" values among `UnboundedRange`. -/
def UnboundedRangeEven (f : Format) : Rat → Prop := Grid (f.prec - 1) (fun _ => True)

/-- The format's largest finite number `(2 - 2^(1-p)) × 2^E_max = (2^p - 1) × 2^(E_max - p + 1)`. -/
def maxValue (f : Format) : Rat := ((2 ^ f.prec - 1 : Nat) : Rat) * (2 : Rat) ^ (f.emax - f.fracBits)

/-- **The overflow result** (Table 6.14, p.100): RN "an infinity with the sign of the intermediate
result"; RZ "the format's largest finite number with the sign of the intermediate result"; RP
"For positive overflow values, supplies positive infinity. For negative overflow values, supplies
the format's most negative finite number"; RM "For positive overflow values, supplies the format's
largest finite number. For negative overflow values, supplies minus infinity". `neg` is the sign of
the intermediate result. The encodings: ±∞ = exponent all ones, fraction 0 (Table 6.2, p.80);
± the largest finite number = exponent `2^expBits - 2`, fraction all ones. -/
def overflowResult (f : Format) (rm : RoundingMode) (neg : Bool) : Nat :=
  let s : Nat := if neg then 2 ^ (f.expBits + f.fracBits) else 0
  let infinity : Nat := s + (2 ^ f.expBits - 1) * 2 ^ f.fracBits
  let largest : Nat := s + (2 ^ f.expBits - 2) * 2 ^ f.fracBits + (2 ^ f.fracBits - 1)
  match rm, neg with
  | .RN, _ => infinity
  | .RZ, _ => largest
  | .RP, false => infinity
  | .RP, true => largest
  | .RM, false => largest
  | .RM, true => infinity

end Format

/-! ## Exact results and correct rounding -/

/-- An exact (real) result `v`, given by its comparisons with the rationals: `le y` iff `y ≤ v`,
`ge y` iff `v ≤ y`. -/
structure Cut where
  /-- `y ≤ v`. -/
  le : Rat → Prop
  /-- `v ≤ y`. -/
  ge : Rat → Prop

namespace Cut

/-- A rational exact result. -/
def ofRat (v : Rat) : Cut := ⟨fun y => y ≤ v, fun y => v ≤ y⟩

/-- `√x` for `x ≥ 0`: `y ≤ √x` iff `y ≤ 0` or `y² ≤ x`; `√x ≤ y` iff `0 ≤ y` and `x ≤ y²`. -/
def sqrt (x : Rat) : Cut := ⟨fun y => y ≤ 0 ∨ y * y ≤ x, fun y => 0 ≤ y ∧ x ≤ y * y⟩

/-- `1/√x` for `x > 0`: `y ≤ 1/√x` iff `y ≤ 0` or `y²·x ≤ 1`; `1/√x ≤ y` iff `0 ≤ y` and `1 ≤ y²·x`. -/
def rsqrt (x : Rat) : Cut := ⟨fun y => y ≤ 0 ∨ y * y * x ≤ 1, fun y => 0 ≤ y ∧ 1 ≤ y * y * x⟩

end Cut

/-- `r` is the largest element of `S` not above `v` (round toward −∞). -/
def RoundDown (S : Rat → Prop) (c : Cut) (r : Rat) : Prop :=
  S r ∧ c.le r ∧ ∀ y, S y → c.le y → y ≤ r

/-- `r` is the least element of `S` not below `v` (round toward +∞). -/
def RoundUp (S : Rat → Prop) (c : Cut) (r : Rat) : Prop :=
  S r ∧ c.ge r ∧ ∀ y, S y → c.ge y → r ≤ y

/-- `r` is an element of `S` nearest to `v` and, when another element `y` is equally near (`v` is
their midpoint), `r` is even (`E r`). For `y < r`, `|r - v| ≤ |y - v|` iff `(y + r)/2 ≤ v`; for
`r < y`, iff `v ≤ (r + y)/2`. -/
def RoundNearestEven (S E : Rat → Prop) (c : Cut) (r : Rat) : Prop :=
  S r ∧ (∀ y, S y → y < r → c.le ((y + r) / 2)) ∧ (∀ y, S y → r < y → c.ge ((r + y) / 2)) ∧
    (∀ y, S y → y ≠ r → c.le ((y + r) / 2) → c.ge ((y + r) / 2) → E r)

/-- **`r` is `v` correctly rounded to `S` in direction `rm`** (Table 6.10, p.95; ties to the even
element of `E`). RZ rounds a nonnegative `v` down and a nonpositive one up. -/
def CorrectlyRounded (S E : Rat → Prop) (rm : RoundingMode) (c : Cut) (r : Rat) : Prop :=
  match rm with
  | .RN => RoundNearestEven S E c r
  | .RZ => (c.le 0 → RoundDown S c r) ∧ (c.ge 0 → RoundUp S c r)
  | .RP => RoundUp S c r
  | .RM => RoundDown S c r

namespace Format

/-- **What rounding a nonzero exact result `v` to format `f` in direction `rm` must deliver**
(no flushing, FCSR.FS = 0), as the `Rounded` record of the core (`bits`, `overflow`, `tiny`,
`inexact`, from which `Rounded.flags` derives the IEEE flags). With `r` the correctly rounded
value of `v` with the exponent range unbounded above:

* `overflow` iff `|r|` exceeds the largest finite number (§6.7.2.5, p.102);
* without overflow, `bits` encodes `r` (its value is `r`); with overflow, `bits` is the overflow
  result of Table 6.14 (p.100) for the sign of `v`;
* the sign bit of `bits` is the sign of `v` (also for a zero result);
* `inexact` iff `r ≠ v` (§6.7.2.6, p.102);
* `tiny` iff `v` rounded with the exponent range unbounded both ways is strictly between
  `±2^E_min` (§6.7.2.3, p.101, after rounding). -/
def RoundSpec (f : Format) (rm : RoundingMode) (c : Cut) (R : Rounded) : Prop :=
  ∃ r : Rat, CorrectlyRounded f.Unbounded f.UnboundedEven rm c r ∧
    (R.overflow = true ↔ f.maxValue < r.abs) ∧
    (R.overflow = false → f.value R.bits = some r) ∧
    (R.overflow = true → ∃ neg : Bool, (neg = true ↔ c.ge 0) ∧ R.bits = f.overflowResult rm neg) ∧
    ((R.bits / 2 ^ (f.expBits + f.fracBits)) % 2 = 1 ↔ c.ge 0) ∧
    (R.inexact = true ↔ ¬ (c.le r ∧ c.ge r)) ∧
    (R.tiny = true ↔ ∃ u : Rat, CorrectlyRounded f.UnboundedRange f.UnboundedRangeEven rm c u ∧
      u.abs < (2 : Rat) ^ f.emin)

end Format

/-! ## Wave 11: every operand, the conversions, the compares, the FCSR

The definitions below extend the rounding reference to the whole of each operation: special operands
(NaN, ±∞, ±0), the conversions, `C.cond.fmt`, `ABS`/`NEG`, and the FCSR bookkeeping. They are written
from MD00082 Vol I-A Rev 6.01 ch.6 (the FPU programming model, read with `FIR.Has2008 = 0`, the legacy
NaN encoding) and the MD00086 Vol II-A Rev 6.06 instruction pages, **not** from `FpOps.lean`; where the
manual leaves a choice, the definition either allows every choice (a relation) or names the pin.
Operands are taken at their encoded values, never flushed: with FCSR.FS = 1, "Prior to Release 5, it
is implementation-dependent whether subnormal operand values are flushed to zero" (§6.7.2.4, p.102;
pin SPEC-NOTES §9 item 13). `Semantics/FpOpsCorrectSpecial.lean` … `FpOpsCorrectStep.lean` prove the
model meets them. -/

namespace Format

/-! ### Fields and classes of an encoding (Table 6.2, p.80-81; Figures 6.1, 6.2, p.80) -/

/-- The sign field `s` (bit `width - 1`); `true` = 1 = negative. -/
def signOf (f : Format) (n : Nat) : Bool := (n / 2 ^ (f.expBits + f.fracBits)) % 2 = 1

/-- The biased exponent field. -/
def expOf (f : Format) (n : Nat) : Nat := (n / 2 ^ f.fracBits) % 2 ^ f.expBits

/-- The fraction field `f`. -/
def fracOf (f : Format) (n : Nat) : Nat := n % 2 ^ f.fracBits

/-- A NaN: unbiased exponent `E_max + 1` (biased exponent all ones), fraction `≠ 0` (Table 6.2). -/
def IsNaN (f : Format) (n : Nat) : Prop := f.expOf n = 2 ^ f.expBits - 1 ∧ f.fracOf n ≠ 0

/-- A signaling NaN with `FIR.Has2008 = 0`: a NaN whose high-order fraction bit `b1` is 1 (Table 6.2,
p.80: "E_max + 1, ≠0, b1 = 1, SNaN, Signaling NaN (FIR.Has2008=0 or FCSR.NAN2008=0)"). -/
def IsSNaN (f : Format) (n : Nat) : Prop := f.IsNaN n ∧ f.fracOf n / 2 ^ (f.fracBits - 1) = 1

/-- A quiet NaN with `FIR.Has2008 = 0`: a NaN with `b1 = 0` (Table 6.2, p.80). -/
def IsQNaN (f : Format) (n : Nat) : Prop := f.IsNaN n ∧ f.fracOf n / 2 ^ (f.fracBits - 1) = 0

instance (f : Format) (n : Nat) : Decidable (f.IsNaN n) := inferInstanceAs (Decidable (_ ∧ _))
instance (f : Format) (n : Nat) : Decidable (f.IsSNaN n) := inferInstanceAs (Decidable (_ ∧ _))
instance (f : Format) (n : Nat) : Decidable (f.IsQNaN n) := inferInstanceAs (Decidable (_ ∧ _))

/-- The encoding of `±∞` (Table 6.2, p.80: `E_max + 1`, fraction 0, sign `s`). -/
def infBits (f : Format) (neg : Bool) : Nat :=
  (if neg then 2 ^ (f.expBits + f.fracBits) else 0) + (2 ^ f.expBits - 1) * 2 ^ f.fracBits

/-- The encoding of `±0` (Table 6.2, p.81: `E_min - 1`, fraction 0, sign `s`). -/
def zeroBits (f : Format) (neg : Bool) : Nat := if neg then 2 ^ (f.expBits + f.fracBits) else 0

/-- **The new quiet NaN** (Table 6.3, p.82, "Value Supplied When a New Quiet NaN Is Created",
`FIR.Has2008 = 0`): sign 0, biased exponent all ones, `b1 = 0` and every other fraction bit 1 —
`0x7fbf ffff` (single), `0x7ff7 ffff ffff ffff` (double); `newQNaN_binary32/64` check the two values. -/
def newQNaN (f : Format) : Nat := (2 ^ f.expBits - 1) * 2 ^ f.fracBits + (2 ^ (f.fracBits - 1) - 1)

end Format

/-- **What an encoding denotes** (Table 6.2, p.80-81): a NaN, a signed infinity, or a finite number
with its sign bit (the sign matters for `±0`). -/
inductive Datum where
  /-- A NaN (quiet or signaling). -/
  | nan
  /-- `+∞` (`neg = false`) or `−∞`. -/
  | inf (neg : Bool)
  /-- A finite number of value `x` and sign bit `neg` (`x = 0` for `±0`). -/
  | num (neg : Bool) (x : Rat)

namespace Format

/-- The datum of a `width`-bit encoding: finite with its `value`, else `±∞` (fraction 0) or a NaN. -/
def datum (f : Format) (n : Nat) : Datum :=
  match f.value n with
  | some x => .num (f.signOf n) x
  | none => if f.fracOf n = 0 then .inf (f.signOf n) else .nan

/-! ### Signaled exceptions of a rounded result, and rounding under the FCSR -/

/-- **The IEEE exceptions a rounding outcome `R` signals** with FCSR.Enables `en` (MD00082 Vol I-A Rev
6.01): Overflow iff `R.overflow` (§6.7.2.5, p.102); Underflow, "When an underflow trap is not enabled
... only when both tininess and loss of accuracy have been detected", "When an underflow trap is
enabled ... when tininess is detected regardless of loss of accuracy" (§6.7.2.3, p.101); Inexact if
"The rounded result of an operation is not exact" or "overflows without an overflow trap" (§6.7.2.6,
p.102). No Invalid, no Division by Zero. -/
def Signaled (en : Flags) (R : Rounded) (fl : Flags) : Prop :=
  fl.invalid = false ∧ fl.divZero = false ∧
  (fl.overflow = true ↔ R.overflow = true) ∧
  (fl.underflow = true ↔ R.tiny = true ∧ (R.inexact = true ∨ en.underflow = true)) ∧
  (fl.inexact = true ↔ R.inexact = true ∨ (R.overflow = true ∧ en.overflow = false))

/-- **Tiny before rounding** (§6.7.2.3, p.101: "computed as though both the exponent range and the
precision were unbounded would lie strictly between ±2^E_min"). -/
def TinyBefore (f : Format) (c : Cut) : Prop :=
  ¬ c.le ((2 : Rat) ^ f.emin) ∧ ¬ c.ge (-((2 : Rat) ^ f.emin))

/-- **A nonzero exact result `c` delivered under the FCSR environment `e`** (result encoding and the
exceptions signaled):

* FCSR.FS = 1 and `c` tiny before rounding (§6.7.2.4, p.102: "Every tiny non-zero result is replaced
  with zero of the same sign"; "Tiny non-zero results are detected before rounding"; "Flushing of tiny
  non-zero results causes Inexact and Underflow exceptions to be signaled"): the zero of the sign of
  `c`, Underflow and Inexact;
* otherwise the result of a rounding outcome `R` meeting `RoundSpec` (correct rounding in FCSR.RM,
  overflow, tininess after rounding, inexact), with the exceptions `Signaled`. -/
def RoundEnvSpec (f : Format) (e : Env) (c : Cut) (res : Nat × Flags) : Prop :=
  (e.flush = true → f.TinyBefore c →
    ∃ neg : Bool, (neg = true ↔ c.ge 0) ∧ res = (f.zeroBits neg, { underflow := true, inexact := true })) ∧
  (¬ (e.flush = true ∧ f.TinyBefore c) →
    ∃ R : Rounded, f.RoundSpec e.rm c R ∧ res.1 = R.bits ∧ Signaled e.enables R res.2)

/-! ### NaN operands (§6.3.1.4, p.81; §6.3.1.5, p.82; §6.7.2.1, p.100) -/

/-- **The result of an arithmetic operation with a NaN among its operands `ops`**: "SNaN operands
cause the Invalid Operation exception for arithmetic operations" (§6.3.1.4) and nothing else is
signaled ("QNaN operands do not cause arithmetic operations to signal an exception", §6.3.1.5); the
result is a quiet NaN ("An SNaN is never produced as a result value"; §6.7.2.1: "The result ... is a
quiet NaN"); "When possible, this QNaN result is one of the operand QNaN values" — so it is an operand
when some operand is a QNaN — and otherwise it is the new QNaN of Table 6.3. *Which* operand QNaN is
not fixed by the manual: any is allowed here (the model's choice, the first in operand order, is the
pin SPEC-NOTES §9 item 13, `nanResult_first`). -/
def NaNResult (f : Format) (ops : List Nat) (res : Nat × Flags) : Prop :=
  (res.2.invalid = true ↔ ∃ x ∈ ops, f.IsSNaN x) ∧
  res.2.divZero = false ∧ res.2.overflow = false ∧ res.2.underflow = false ∧ res.2.inexact = false ∧
  f.IsQNaN res.1 ∧
  ((∃ x ∈ ops, f.IsQNaN x) → res.1 ∈ ops) ∧
  ((∀ x ∈ ops, ¬ f.IsQNaN x) → res.1 = f.newQNaN)

/-- The Invalid Operation default result: the new QNaN, Invalid only (§6.7.2.1, p.100; Table 6.3). -/
def invalidResult (f : Format) : Nat × Flags := (f.newQNaN, { invalid := true })

/-! ### The arithmetic operations -/

/-- **`ADD.fmt` (`isSub = false`, MD00086 p.34) and `SUB.fmt` (`isSub = true`, p.389)**, `a ± b` under
`e`. NaN: `NaNResult`. `∞ - ∞` ("magnitude subtraction of infinities", §6.7.2.1, p.100): Invalid.
Other infinite cases: the infinity, exactly, no exception (§6.3.1.3, p.81: "Arithmetic with ∞ is the
limiting case of real arithmetic ... regarded as exact and exception conditions do not arise").
Finite: an exactly zero result is `+0`, or `−0` in RM, when the operands' (effective) signs differ,
and the common sign when they agree — the manual is silent; this is IEEE Std 754-2019 §6.3, p.50 ("the sign
of that sum (or difference) shall be +0 under all rounding-direction attributes except
roundTowardNegative"; "when x is zero, x + x and x − (−x) have the sign of x"; verified against 2019;
MD00082 p.77 names the 1985 standard) (pin, SPEC-NOTES §9 item 30) — no exception; a nonzero one
is `RoundEnvSpec` of the exact sum. -/
def AddSpec (f : Format) (e : Env) (isSub : Bool) (a b : Nat) (res : Nat × Flags) : Prop :=
  match f.datum a, f.datum b with
  | .nan, _ => f.NaNResult [a, b] res
  | _, .nan => f.NaNResult [a, b] res
  | .inf s, .inf t => if s = (t ^^ isSub) then res = (f.infBits s, {}) else res = f.invalidResult
  | .inf s, .num _ _ => res = (f.infBits s, {})
  | .num _ _, .inf t => res = (f.infBits (t ^^ isSub), {})
  | .num s x, .num t y =>
    let v := if isSub then x - y else x + y
    if v = 0 then
      res = (f.zeroBits (if s = (t ^^ isSub) then s else decide (e.rm = .RM)), {})
    else f.RoundEnvSpec e (Cut.ofRat v) res

/-- **`MUL.fmt`** (MD00086 p.302), `a × b`. NaN: `NaNResult`. `0 × ∞` (§6.7.2.1, p.100): Invalid.
`∞ × ∞`, `∞ × y` (`y ≠ 0`): the infinity of sign `s xor t`, exactly (§6.3.1.3, p.81). Finite: a zero
product is the zero of sign `s xor t` (IEEE Std 754-2019 §6.3, p.50: the sign of a product "is the
exclusive OR of the operands' signs", also for zero operands or results; verified against 2019; pin,
SPEC-NOTES §9 item 30), else `RoundEnvSpec` of the exact product. -/
def MulSpec (f : Format) (e : Env) (a b : Nat) (res : Nat × Flags) : Prop :=
  match f.datum a, f.datum b with
  | .nan, _ => f.NaNResult [a, b] res
  | _, .nan => f.NaNResult [a, b] res
  | .inf s, .inf t => res = (f.infBits (s ^^ t), {})
  | .inf s, .num t y => if y = 0 then res = f.invalidResult else res = (f.infBits (s ^^ t), {})
  | .num s x, .inf t => if x = 0 then res = f.invalidResult else res = (f.infBits (s ^^ t), {})
  | .num s x, .num t y =>
    if x * y = 0 then res = (f.zeroBits (s ^^ t), {}) else f.RoundEnvSpec e (Cut.ofRat (x * y)) res

/-- **`DIV.fmt`** (MD00086 p.170), `a / b`. NaN: `NaNResult`. `0/0`, `∞/∞` (§6.7.2.1, p.100):
Invalid. "if the divisor is zero and the dividend is a finite nonzero number": Division by Zero, "a
correctly signed infinity" (§6.7.2.2, p.100); "The result of (∞/0) is a correctly signed infinity"
(no exception); `∞ / y`: the infinity, `x / ∞`: the zero, of sign `s xor t`, exactly (§6.3.1.3, p.81);
`0 / y` (`y ≠ 0`): the zero of sign `s xor t` (IEEE Std 754-2019 §6.3, p.50, verified against 2019; pin
SPEC-NOTES §9 item 30); else `RoundEnvSpec`
of the exact quotient. -/
def DivSpec (f : Format) (e : Env) (a b : Nat) (res : Nat × Flags) : Prop :=
  match f.datum a, f.datum b with
  | .nan, _ => f.NaNResult [a, b] res
  | _, .nan => f.NaNResult [a, b] res
  | .inf _, .inf _ => res = f.invalidResult
  | .inf s, .num t _ => res = (f.infBits (s ^^ t), {})
  | .num s _, .inf t => res = (f.zeroBits (s ^^ t), {})
  | .num s x, .num t y =>
    if y = 0 then
      (if x = 0 then res = f.invalidResult else res = (f.infBits (s ^^ t), { divZero := true }))
    else if x = 0 then res = (f.zeroBits (s ^^ t), {})
    else f.RoundEnvSpec e (Cut.ofRat (x / y)) res

/-- **`SQRT.fmt`** (MD00086 p.382), `√a`. NaN: `NaNResult`. "If the value in FPR fs corresponds to
– 0, the result is – 0" (and `+0` gives `+0`); "An operand of less than 0 (-0 is a valid operand
value)" is invalid (§6.7.2.1, p.100), `−∞` included; `√+∞ = +∞` exactly (§6.3.1.3); a positive
finite operand: `RoundEnvSpec` of `√x` ("calculated to infinite precision, rounded according to the
current rounding mode in FCSR"). IEEE Std 754-2019 §6.3, p.50: "Except that squareRoot(−0) shall be −0,
every numeric squareRoot result shall have a positive sign"; §7.2 g), p.52: Invalid "if the operand is less
than zero" (verified against 2019). -/
def SqrtSpec (f : Format) (e : Env) (a : Nat) (res : Nat × Flags) : Prop :=
  match f.datum a with
  | .nan => f.NaNResult [a] res
  | .inf false => res = (f.infBits false, {})
  | .inf true => res = f.invalidResult
  | .num s x =>
    if x = 0 then res = (f.zeroBits s, {})
    else if x < 0 then res = f.invalidResult
    else f.RoundEnvSpec e (Cut.sqrt x) res

/-! ### `ABS.fmt`, `NEG.fmt` -/

/-- The operand with its sign bit cleared (`clear = true`, `ABS`) or flipped (`NEG`). -/
def signChanged (f : Format) (clear : Bool) (a : Nat) : Nat :=
  if f.signOf a then a - 2 ^ (f.expBits + f.fracBits)
  else if clear then a else a + 2 ^ (f.expBits + f.fracBits)

/-- **`ABS.fmt` (`clear = true`, MD00086 p.32) and `NEG.fmt` (p.307)** with `FIR.Has2008 = 0`: "this
operation is arithmetic. For this case, any NaN operand signals invalid operation"; the value is
obtained by "changing the sign bit". A signaling NaN gives the new QNaN (§6.3.1.4, p.81: "An SNaN is
never produced as a result value"; Table 6.3). A quiet NaN: Invalid, and the delivered value is the
operand with its sign bit changed — reading A′ (SPEC-NOTES §9 item 21; the manual does not say which
QNaN an untrapped `ABS`/`NEG` of a QNaN delivers, §6.3.1.5 only that "When possible, this QNaN result
is one of the operand QNaN values"). Otherwise: the sign bit changed, no exception. Note IEEE Std 754-2019
§5.5.1, p.35, makes negate/abs quiet ("signal no exception", NaNs treated "alike"); with `FIR.Has2008 = 0` the
MIPS pages say the operation "is arithmetic", and the model follows MIPS (SPEC-NOTES §9 item 21). -/
def SignOpSpec (f : Format) (clear : Bool) (a : Nat) (res : Nat × Flags) : Prop :=
  if f.IsSNaN a then res = f.invalidResult
  else if f.IsQNaN a then res = (f.signChanged clear a, { invalid := true })
  else res = (f.signChanged clear a, {})

/-! ### Conversions -/

/-- **`ConvertFmt` between floating-point formats** (`CVT.S.D`, MD00086 p.159: "converted ... and
rounded according to the current rounding mode in FCSR"; `CVT.D.S`, p.153). A signaling NaN: Invalid,
the new QNaN (§6.3.1.4, §6.7.2.1). A quiet NaN: a quiet NaN of the destination format, no exception
(§6.3.1.5, p.82: "information contained in a QNaN to be preserved through ... floating-point format
conversions"; which QNaN is not fixed — the model keeps the sign and the leading fraction bits, pin
SPEC-NOTES §9 item 22, `Oracle.cvtQNaNToD/ToS`). `±∞`: `±∞`. `±0`: `±0`. Otherwise `RoundEnvSpec` of the
value. (IEEE Std 754-2019 §5.4.2, p.34: a conversion to a narrower precision "shall be rounded as specified
in Clause 4", to a wider one "is always exact"; §6.2.3, p.49: a quiet NaN converted wider and back "should
not change the quiet NaN payload in any way except to make it canonical".) -/
def ConvertSpec (src dst : Format) (e : Env) (a : Nat) (res : Nat × Flags) : Prop :=
  match src.datum a with
  | .nan => (src.IsSNaN a → res = dst.invalidResult) ∧ (src.IsQNaN a → dst.IsQNaN res.1 ∧ res.2 = {})
  | .inf s => res = (dst.infBits s, {})
  | .num s x => if x = 0 then res = (dst.zeroBits s, {}) else dst.RoundEnvSpec e (Cut.ofRat x) res

/-- **An exact conversion**: the result encodes the value `x` with sign bit `s`, no exception
(CVT.D.fmt, MD00086 p.153: "If fmt is S or W, then the operation is always exact"). -/
def ExactSpec (f : Format) (s : Bool) (x : Rat) (res : Nat × Flags) : Prop :=
  f.value res.1 = some x ∧ f.signOf res.1 = s ∧ res.2 = {}

/-- **`CVT.D.S`** (MD00086 p.153): as `ConvertSpec`, the finite case exact (`ExactSpec`). -/
def WidenSpec (src dst : Format) (a : Nat) (res : Nat × Flags) : Prop :=
  match src.datum a with
  | .nan => (src.IsSNaN a → res = dst.invalidResult) ∧ (src.IsQNaN a → dst.IsQNaN res.1 ∧ res.2 = {})
  | .inf s => res = (dst.infBits s, {})
  | .num s x => dst.ExactSpec s x res

/-- **`CVT.S.W` / `CVT.D.W` of the word integer `i`** (MD00086 p.159, p.153): `0` gives `+0` (the
manual does not give the sign; IEEE Std 754-2019 §5.4.1, p.33: "Integer zeros without signs are converted to
+0", verified against 2019; pin SPEC-NOTES §9 item 30), otherwise `RoundEnvSpec` of `i`. -/
def FromIntSpec (f : Format) (e : Env) (i : Int) (res : Nat × Flags) : Prop :=
  if i = 0 then res = (f.zeroBits false, {}) else f.RoundEnvSpec e (Cut.ofRat i) res

end Format

/-- The integers, as rationals. -/
def IsInt (y : Rat) : Prop := ∃ i : Int, y = i

/-- The even integers. -/
def IsEvenInt (y : Rat) : Prop := ∃ i : Int, y = 2 * i

namespace Format

/-- **`ConvertFmt(fs, fmt, W)` rounding in mode `rm`** (`CVT.W.fmt` with FCSR.RM, MD00086 p.160;
`ROUND.W.fmt` mode 0, p.342; `TRUNC.W.fmt` mode 1, p.441; `CEIL.W.fmt` mode 2, p.128; `FLOOR.W.fmt`
mode 3, p.186): "When the source value is Infinity, NaN, or rounds to an integer outside the range
-2^31 to 2^31-1, the result cannot be represented correctly, an IEEE Invalid Operation condition
exists"; the default result with `FCSR.NAN2008 = 0` is `2^31–1` (ROUND/TRUNC/CEIL/FLOOR.W pages and
Table 6.3, p.82: `0x7fff ffff`; the CVT.W.fmt page prints "2^63–1", a misprint for a word result,
SPEC-NOTES). Only Invalid is signaled then (§6.7.2, p.99: only Inexact with Overflow or Underflow can
occur together). Otherwise the result is `x` rounded to an integer `i` in direction `rm` (Table 6.10,
p.95, over the integers), as a two's complement word, with Inexact iff `i ≠ x` (§6.7.2.6). -/
def ToWordSpec (f : Format) (rm : RoundingMode) (a : Nat) (res : BitVec 32 × Flags) : Prop :=
  match f.datum a with
  | .nan => res = (0x7FFFFFFF#32, { invalid := true })
  | .inf _ => res = (0x7FFFFFFF#32, { invalid := true })
  | .num _ x => ∃ i : Int, CorrectlyRounded IsInt IsEvenInt rm (Cut.ofRat x) (i : Rat) ∧
      (-2 ^ 31 ≤ i ∧ i ≤ 2 ^ 31 - 1 →
        res.1.toInt = i ∧ res.2 = (if (i : Rat) = x then {} else { inexact := true })) ∧
      (¬ (-2 ^ 31 ≤ i ∧ i ≤ 2 ^ 31 - 1) → res = (0x7FFFFFFF#32, { invalid := true }))

/-! ### `C.cond.fmt` (MD00086 Vol II-A Rev 6.06, p.110-113) -/

/-- The four "mutually exclusive ordering relations" (p.110): greater than, less than, equal,
unordered. -/
inductive Relation where
  | gt | lt | eq | un
  deriving DecidableEq

/-- **The ordering relation of two encodings**: "unordered, which is true when at least one operand
value is NaN"; otherwise less / equal / greater of the values, with "-∞ < (every finite number) < +∞"
(MD00082 Vol I-A Rev 6.01 §6.3.1.3, p.81) and "Comparisons ignore the sign of zero, so +0 equals -0"
(p.110; the values of `±0` are both 0). -/
def cmpRel (f : Format) (a b : Nat) : Relation :=
  match f.datum a, f.datum b with
  | .nan, _ => .un
  | _, .nan => .un
  | .inf s, .inf t => if s = t then .eq else if s then .lt else .gt
  | .inf s, .num _ _ => if s then .lt else .gt
  | .num _ _, .inf t => if t then .gt else .lt
  | .num _ x, .num _ y => if x < y then .lt else if x = y then .eq else .gt

end Format

/-- **The 16 compare predicates**, the "If Predicate Is True" columns `> < = ?` of Table 3.1 (cond3 = 0,
p.111) and Table 3.2 (cond3 = 1, p.112), by the condition field `cond3..0`, and the "Inv Op Excp. if
QNaN?" column (No for cond3 = 0, Yes for cond3 = 1). Returns `(>, <, =, ?, invalid-if-QNaN)`. -/
def condTable : Nat → Bool × Bool × Bool × Bool × Bool
  | 0 => (false, false, false, false, false)   -- F
  | 1 => (false, false, false, true, false)    -- UN
  | 2 => (false, false, true, false, false)    -- EQ
  | 3 => (false, false, true, true, false)     -- UEQ
  | 4 => (false, true, false, false, false)    -- OLT
  | 5 => (false, true, false, true, false)     -- ULT
  | 6 => (false, true, true, false, false)     -- OLE
  | 7 => (false, true, true, true, false)      -- ULE
  | 8 => (false, false, false, false, true)    -- SF
  | 9 => (false, false, false, true, true)     -- NGLE
  | 10 => (false, false, true, false, true)    -- SEQ
  | 11 => (false, false, true, true, true)     -- NGL
  | 12 => (false, true, false, false, true)    -- LT
  | 13 => (false, true, false, true, true)     -- NGE
  | 14 => (false, true, true, false, true)     -- LE
  | _ => (false, true, true, true, true)       -- 15: NGT

/-- The table entry for a relation. -/
def condHolds (cond : Nat) : Format.Relation → Bool
  | .gt => (condTable cond).1
  | .lt => (condTable cond).2.1
  | .eq => (condTable cond).2.2.1
  | .un => (condTable cond).2.2.2.1

namespace Format

/-- **`C.cond.fmt`** on the encodings `a` (`fs`), `b` (`ft`) with condition field `cond`: the
condition-code value is the table entry of the operands' relation (Tables 3.1, 3.2); "If one of the
values is an SNaN, or cond3 is set and at least one of the values is a QNaN, an Invalid Operation
condition is raised" (p.110); nothing else is signaled ("The comparison is exact and neither
overflows nor underflows", p.110). -/
def CompareSpec (f : Format) (cond : BitVec 4) (a b : Nat) (res : Bool × Flags) : Prop :=
  res.1 = condHolds cond.toNat (f.cmpRel a b) ∧
  (res.2.invalid = true ↔
    (f.IsSNaN a ∨ f.IsSNaN b ∨ ((condTable cond.toNat).2.2.2.2 = true ∧ (f.IsQNaN a ∨ f.IsQNaN b)))) ∧
  res.2.divZero = false ∧ res.2.overflow = false ∧ res.2.underflow = false ∧ res.2.inexact = false

end Format

/-! ### The FCSR after an FP operation (§6.7.1, p.98-99; CheckFPException, Vol II-A §2.2.2.3.3, p.23) -/

/-- The five IEEE bits of a `Flags` value in FCSR order, `k = 0 … 4` = I, U, O, Z, V (MD00082 Vol I-A
Rev 6.01 Figure 6.14 / Table 6.8, p.92-95: Cause 16..12, Enables 11..7, Flags 6..2 are `V Z O U I`). -/
def flagBit (fl : Flags) : Nat → Bool
  | 0 => fl.inexact
  | 1 => fl.underflow
  | 2 => fl.overflow
  | 3 => fl.divZero
  | _ => fl.invalid

/-- **The FCSR `new` and the trap decision `trap` after an FP arithmetic operation that raised the
IEEE exceptions `fl`, from the FCSR `old`** (MD00082 Vol I-A Rev 6.01 §6.7.1, p.99):

* "The Cause bits are written during each floating point arithmetic operation ... The bit is set to 1
  if the corresponding exception condition arises; otherwise it is set to 0": Cause.E (bit 17) = 0
  (the model never raises Unimplemented Operation), Cause bit `12 + k` = exception `k`;
* the trap is CheckFPException (MD00086 Vol II-A Rev 6.06 §2.2.2.3.3, Figure 2.24, p.23) on the new
  FCSR: "if ( (FCSR17 = 1) or ((FCSR16..12 and FCSR11..7) ≠ 0) ) then SignalException";
* "The Flag bits are set to 1 if the corresponding IEEE exception is raised, otherwise the bits are
  unchanged"; "instructions that trap do not update the Flag bits": Flags bit `2 + k`;
* every other bit is unchanged. -/
def FcsrSpec (old : BitVec 32) (fl : Flags) (new : BitVec 32) (trap : Bool) : Prop :=
  new.getLsbD 17 = false ∧
  (∀ k, k < 5 → new.getLsbD (12 + k) = flagBit fl k) ∧
  (trap = true ↔ new.getLsbD 17 = true ∨ ∃ k, k < 5 ∧ new.getLsbD (12 + k) = true ∧ new.getLsbD (7 + k) = true) ∧
  (∀ k, k < 5 → new.getLsbD (2 + k) = (old.getLsbD (2 + k) || (!trap && flagBit fl k))) ∧
  (∀ i, i < 32 → ¬ (2 ≤ i ∧ i ≤ 6) → ¬ (12 ≤ i ∧ i ≤ 17) → new.getLsbD i = old.getLsbD i)

/-- The outcome of one FP operation at the FCSR level: it traps with the FCSR `fcsr`, or it completes
with the FCSR `fcsr` and the value `v`. -/
inductive FpOutcome (α : Type) where
  | trap (fcsr : BitVec 32)
  | done (fcsr : BitVec 32) (v : α)

/-- **One FP operation as a separate instruction**: some result `r` allowed by the operation's spec
`Op`, the FCSR updated per `FcsrSpec`, trapping or completing with `r.1`. -/
def OpStep {α : Type} (Op : α × Flags → Prop) (fcsr : BitVec 32) (o : FpOutcome α) : Prop :=
  ∃ r : α × Flags, Op r ∧ ∃ new trap, FcsrSpec fcsr r.2 new trap ∧
    (trap = true → o = .trap new) ∧ (trap = false → o = .done new r.1)

/-- **One operation of an instruction made of several FP operations** (the multiply-add family):
some result `r` allowed by the operation's spec `Op`; the exceptions so far are `acc.or r.2` (`acc`
those of the instruction's earlier operations), and the FCSR `fcsr` *before the instruction* is
updated with them per `FcsrSpec`: Cause ← the exceptions so far ("A bit is set to 1 if the
corresponding exception condition arises during the execution of an instruction and is set to 0
otherwise", MD00082 Vol I-A Rev 6.01, Table 6.8 `Cause`, p.94), the trap check, and — only when
nothing traps — Flags (`FcsrSpec` sets Flags only for `trap = false`; "instructions that trap do not
update the Flag bits", §6.7.1, p.99). If it traps the instruction ends with that FCSR; otherwise
`next` continues with the exceptions so far, the value `r.1` and the FCSR `new` it would complete
with. -/
def OpAcc {α β : Type} (Op : α × Flags → Prop) (fcsr : BitVec 32) (acc : Flags)
    (next : Flags → α → BitVec 32 → FpOutcome β → Prop) (out : FpOutcome β) : Prop :=
  ∃ r : α × Flags, Op r ∧ ∃ new trap, FcsrSpec fcsr (acc.or r.2) new trap ∧
    (trap = true → out = .trap new) ∧ (trap = false → next (acc.or r.2) r.1 new out)

/-- The instruction's last operation completes with its FCSR and value. -/
def OpDone {α : Type} (_acc : Flags) (v : α) (new : BitVec 32) (out : FpOutcome α) : Prop :=
  out = .done new v

/-- **`MADD.fmt` / `MSUB.fmt` / `NMADD.fmt` / `NMSUB.fmt` "as if separate floating-point multiply and add
[subtract] [and negate] instructions were executed ... The Cause bits are ORed into the Flag bits if no
exception is taken"** (MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308,
NMSUB.fmt p.310): the multiply `fs × ft` (`MulSpec`), rounded, then the add/subtract of the rounded
product `p` and `fr` (`AddSpec`, operand order as printed: MADD `p + fr`, MSUB `p − fr`, NMADD
`fr + p`, NMSUB `p − fr`), rounded, then for NMADD/NMSUB the negate (`SignOpSpec`, NEG.fmt) — each
operation's result and exceptions as the separate instruction's. FCSR, per instruction (`OpAcc`):
after each operation Cause holds the union of the exceptions of the operations so far (MD00082 Vol I-A
Rev 6.01, Table 6.8 `Cause`, p.94: the conditions that arise "during the execution of an
instruction") and the trap check is made; a trap ends the instruction there (the later operations
are not executed, as a separate instruction after a trapping one would not be) with Flags
unchanged (§6.7.1, p.99); otherwise, after the last operation, Flags |= the union. The operations
read FCSR.RM, Enables and FS (`e`), which the operations do not change. `kind`: 0 MADD, 1 MSUB,
2 NMADD, 3 NMSUB. -/
def MaddSpec (f : Format) (e : Env) (kind : Nat) (fcsr : BitVec 32) (fr fs ft : Nat)
    (out : FpOutcome Nat) : Prop :=
  OpAcc (f.MulSpec e fs ft) fcsr Flags.none (fun acc p _ out1 =>
    if kind < 2 then
      OpAcc (if kind = 0 then f.AddSpec e false p fr else f.AddSpec e true p fr) fcsr acc OpDone out1
    else
      OpAcc (if kind = 2 then f.AddSpec e false fr p else f.AddSpec e true p fr) fcsr acc
        (fun acc2 q _ out2 => OpAcc (f.SignOpSpec false q) fcsr acc2 OpDone out2) out1) out

end Mips.Fp
