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
from MD00082 Vol I-A Rev 6.01 ch.6 (the FPU programming model, read for Release 6: `FIR.Has2008 = 1`,
`FCSR.NAN2008 = ABS2008 = 1`, the IEEE 754-2008 NaN encoding) and the MD00086 Vol II-A Rev 6.06
instruction pages, **not** from `FpOps.lean`; where the manual leaves a choice, the definition either
allows every choice (a relation) or names the pin. The definitions below take each operand as the
operation sees it: with FCSR.FS = 1 "every input subnormal value is replaced with zero of the same
sign" (Table 6.8, `FS`, p.93, "As of Release 5"), which `FlushedIn` states and the statements about
the model's operations apply to its operands; and "Flushing of subnormal input operands in all
instructions except comparisons causes Inexact exception to be signaled" (§6.7.2.4, p.102), which
`WithFlushInexact` adds to the exceptions of every non-comparison operation. `Semantics/FpOpsCorrectSpecial.lean` …
`FpOpsCorrectIEEE.lean` prove the model meets them. -/

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

/-- A signaling NaN with `FCSR.NAN2008 = 1`: a NaN whose high-order fraction bit `b1` is 0 (Table 6.2,
p.80: "E_max + 1, ≠0, b1 = 0, SNaN, Signaling NaN (FCSRNAN2008=1)"; the `FIR.Has2008 = 0` rows are "Not
applicable to Release 6"). -/
def IsSNaN (f : Format) (n : Nat) : Prop := f.IsNaN n ∧ f.fracOf n / 2 ^ (f.fracBits - 1) = 0

/-- A quiet NaN with `FCSR.NAN2008 = 1`: a NaN with `b1 = 1` (Table 6.2, p.80). -/
def IsQNaN (f : Format) (n : Nat) : Prop := f.IsNaN n ∧ f.fracOf n / 2 ^ (f.fracBits - 1) = 1

instance (f : Format) (n : Nat) : Decidable (f.IsNaN n) := inferInstanceAs (Decidable (_ ∧ _))
instance (f : Format) (n : Nat) : Decidable (f.IsSNaN n) := inferInstanceAs (Decidable (_ ∧ _))
instance (f : Format) (n : Nat) : Decidable (f.IsQNaN n) := inferInstanceAs (Decidable (_ ∧ _))

/-- The encoding of `±∞` (Table 6.2, p.80: `E_max + 1`, fraction 0, sign `s`). -/
def infBits (f : Format) (neg : Bool) : Nat :=
  (if neg then 2 ^ (f.expBits + f.fracBits) else 0) + (2 ^ f.expBits - 1) * 2 ^ f.fracBits

/-- The encoding of `±0` (Table 6.2, p.81: `E_min - 1`, fraction 0, sign `s`). -/
def zeroBits (f : Format) (neg : Bool) : Nat := if neg then 2 ^ (f.expBits + f.fracBits) else 0

/-- **The new quiet NaN** (Table 6.3, p.82, "Value Supplied When a New Quiet NaN Is Created", column
`FCSR.NAN2008 = 1`): sign 0, biased exponent all ones, `b1 = 1` and every other fraction bit 0 —
`0x7fc0 0000` (single), `0x7ff8 0000 0000 0000` (double); `newQNaN_binary32/64` check the two values. -/
def newQNaN (f : Format) : Nat := (2 ^ f.expBits - 1) * 2 ^ f.fracBits + 2 ^ (f.fracBits - 1)

/-- **A NaN passed to the output** with `FCSR.NAN2008 = 1` (§6.3.1.5, p.82-83): "If the chosen input
is a QNAN, the entire mantissa is passed to the output without change. If the chosen input is a SNAN,
the only change is to set the leftmost/most-significant mantissa bit" — the encoding with `b1` set. -/
def passedNaN (f : Format) (n : Nat) : Nat := n ||| 2 ^ (f.fracBits - 1)

/-- **An input operand under FCSR.FS** (`fl`; MD00082 Vol I-A Rev 6.01 Table 6.8, `FS`, p.93): "When FS
is one ... As of Release 5, every input subnormal value is replaced with zero of the same sign"; when
FS is zero "Input subnormal values ... are not altered". A subnormal encoding is one with biased
exponent 0 and fraction `≠ 0` (Table 6.2, p.80, "E_min -1, ≠0"). -/
def FlushedIn (f : Format) (fl : Bool) (n : Nat) : Nat :=
  if fl = true ∧ f.expOf n = 0 ∧ f.fracOf n ≠ 0 then f.zeroBits (f.signOf n) else n

/-- **Some input operand among `ops` is flushed** under FCSR.FS (`fl`): FS is one and some operand is
subnormal (biased exponent 0, fraction `≠ 0`, Table 6.2, p.80), so `FlushedIn` replaces it. -/
def FlushInexact (f : Format) (fl : Bool) (ops : List Nat) : Prop :=
  fl = true ∧ ∃ n ∈ ops, f.expOf n = 0 ∧ f.fracOf n ≠ 0

instance (f : Format) (fl : Bool) (ops : List Nat) : Decidable (f.FlushInexact fl ops) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **A non-comparison operation with input flushing** (MD00082 Vol I-A Rev 6.01 §6.7.2.4, p.102:
"Flushing of subnormal input operands in all instructions except comparisons causes Inexact exception
to be signaled"; MADDF.fmt, MD00086 Vol II-A Rev 6.06 p.260: "Inexact may be signaled both by input
flushing and/or by the fused-multiply-add: the conditions or ORed"): `P` (the operation's reference
definition, on the flushed operands) holds of the delivered result with some exceptions `g`, and the
exceptions signaled are `g` with Inexact added iff an operand among `ops` (as encoded) was flushed
(`FlushInexact`). -/
def WithFlushInexact {α : Type} (f : Format) (fl : Bool) (ops : List Nat) (P : α × Flags → Prop)
    (res : α × Flags) : Prop :=
  ∃ g : Flags, P (res.1, g) ∧ res.2 = { g with inexact := g.inexact || decide (f.FlushInexact fl ops) }

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
quiet NaN"). It is a NaN operand passed to the output (`passedNaN`: "If a CPU implements passing an
input NAN operand to the output ... and FCSRNAN2008=1", p.82-83) or the new QNaN of Table 6.3; "When
possible, this QNaN result is one of the operand QNaN values", so it is a passed operand when some
operand is a QNaN. *Which* operand is passed is not fixed by the manual: any is allowed here (the
model's choice — the first signaling NaN, else the first quiet NaN, in operand order — is the pin
SPEC-NOTES §9 item 13, `nanResult_first`, `nanResult_first_snan`). -/
def NaNResult (f : Format) (ops : List Nat) (res : Nat × Flags) : Prop :=
  (res.2.invalid = true ↔ ∃ x ∈ ops, f.IsSNaN x) ∧
  res.2.divZero = false ∧ res.2.overflow = false ∧ res.2.underflow = false ∧ res.2.inexact = false ∧
  f.IsQNaN res.1 ∧
  (res.1 = f.newQNaN ∨ ∃ x ∈ ops, f.IsNaN x ∧ res.1 = f.passedNaN x) ∧
  ((∃ x ∈ ops, f.IsQNaN x) → ∃ x ∈ ops, f.IsNaN x ∧ res.1 = f.passedNaN x)

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

/-- **`ABS.fmt` (`clear = true`, MD00086 p.32) and `NEG.fmt` (p.307)** with `FCSR.ABS2008 = 1` (read-only
1 in Release 6, MD00082 Vol I-A Rev 6.01 Table 6.8, p.93): "this operation is non-arithmetic. For this
case, both regular floating point numbers and NAN values are treated alike, only the sign bit is
affected by this instruction. No IEEE exception can be generated for this case": the operand with its
sign bit changed, whatever it encodes. (IEEE Std 754-2019 §5.5.1, p.35, agrees: negate/abs are quiet
operations that "signal no exception", NaNs treated "alike"; verified against 2019.) -/
def SignOpSpec (f : Format) (clear : Bool) (a : Nat) (res : Nat) : Prop :=
  res = f.signChanged clear a

/-! ### Conversions -/

/-- **The result of a format conversion of a NaN** `a`: a quiet NaN of the destination format
(§6.3.1.4, p.81: "An SNaN is never produced as a result value"; §6.3.1.5, p.82: "information contained
in a QNaN to be preserved through ... floating-point format conversions"; which QNaN is not fixed —
the model keeps the sign and the leading fraction bits and sets `b1`, pin SPEC-NOTES §9 item 22,
`Oracle.cvtQNaNToD/ToS`), with Invalid exactly for a signaling NaN (§6.3.1.4: "SNaN operands cause the
Invalid Operation exception for arithmetic operations"; §6.3.1.5: "QNaN operands do not cause
arithmetic operations to signal an exception") and no other exception. -/
def ConvertNaNSpec (src dst : Format) (a : Nat) (res : Nat × Flags) : Prop :=
  dst.IsQNaN res.1 ∧ res.2 = (if src.IsSNaN a then { invalid := true } else {})

/-- **`ConvertFmt` between floating-point formats** (`CVT.S.D`, MD00086 p.159: "converted ... and
rounded according to the current rounding mode in FCSR"; `CVT.D.S`, p.153). A NaN: `ConvertNaNSpec`.
`±∞`: `±∞`. `±0`: `±0`. Otherwise `RoundEnvSpec` of the value. (IEEE Std 754-2019 §5.4.2, p.34: a
conversion to a narrower precision "shall be rounded as specified in Clause 4", to a wider one "is
always exact"; §6.2.3, p.49: a quiet NaN converted wider and back "should not change the quiet NaN
payload in any way except to make it canonical".) -/
def ConvertSpec (src dst : Format) (e : Env) (a : Nat) (res : Nat × Flags) : Prop :=
  match src.datum a with
  | .nan => ConvertNaNSpec src dst a res
  | .inf s => res = (dst.infBits s, {})
  | .num s x => if x = 0 then res = (dst.zeroBits s, {}) else dst.RoundEnvSpec e (Cut.ofRat x) res

/-- **An exact conversion**: the result encodes the value `x` with sign bit `s`, no exception
(CVT.D.fmt, MD00086 p.153: "If fmt is S or W, then the operation is always exact"). -/
def ExactSpec (f : Format) (s : Bool) (x : Rat) (res : Nat × Flags) : Prop :=
  f.value res.1 = some x ∧ f.signOf res.1 = s ∧ res.2 = {}

/-- **`CVT.D.S`** (MD00086 p.153): as `ConvertSpec`, the finite case exact (`ExactSpec`). -/
def WidenSpec (src dst : Format) (a : Nat) (res : Nat × Flags) : Prop :=
  match src.datum a with
  | .nan => ConvertNaNSpec src dst a res
  | .inf s => res = (dst.infBits s, {})
  | .num s x => dst.ExactSpec s x res

/-- **`CVT.S.W` / `CVT.D.W` / `CVT.S.L` / `CVT.D.L` of the integer `i`** (MD00086 p.159, p.153): `0` gives `+0` (the
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

/-- **`ConvertFmt(fs, fmt, W)` / `ConvertFmt(fs, fmt, L)` rounding in mode `rm`**, to a `w`-bit fixed
point integer (`w` = 32 for W, 64 for L): `CVT.W.fmt`/`CVT.L.fmt` with FCSR.RM (MD00086 p.160, p.154);
`ROUND` mode 0 (p.342, p.341), `TRUNC` mode 1 (p.441, p.440), `CEIL` mode 2 (p.128, p.127), `FLOOR`
mode 3 (p.186, p.185): "When the source value is Infinity, NaN, or rounds to an integer outside the
range -2^31 to 2^31-1, the result cannot be represented correctly, an IEEE Invalid Operation condition
exists" (`-2^63` to `2^63-1` for L). The default result with `FCSR.NAN2008 = 1` (MD00082 Vol I-A Rev
6.01 §6.3.1.5, Table 6.3, p.82): "result from converting any FP NAN" `0`; "any FP number too big to
represent as a 32-bit positive integer" `2^31-1`; "too small to represent as a 32-bit negative integer"
`-2^31` (the longword rows: `2^63-1`, `0`, `-2^63`); `+∞` is too big, `-∞` too small. Only Invalid is
signaled then (§6.7.2, p.99: only Inexact with Overflow or Underflow can occur together). Otherwise the
result is `x` rounded to an integer `i` in direction `rm` (Table 6.10, p.95, over the integers), as a
two's complement integer, with Inexact iff `i ≠ x` (§6.7.2.6). -/
def ToFixedSpec (f : Format) (w : Nat) (rm : RoundingMode) (a : Nat) (res : BitVec w × Flags) : Prop :=
  match f.datum a with
  | .nan => res = (0#w, { invalid := true })
  | .inf s => res = (if s then BitVec.ofInt w (-2 ^ (w - 1)) else BitVec.ofInt w (2 ^ (w - 1) - 1),
      { invalid := true })
  | .num _ x => ∃ i : Int, CorrectlyRounded IsInt IsEvenInt rm (Cut.ofRat x) (i : Rat) ∧
      (-2 ^ (w - 1) ≤ i ∧ i ≤ 2 ^ (w - 1) - 1 →
        res.1.toInt = i ∧ res.2 = (if (i : Rat) = x then {} else { inexact := true })) ∧
      (i < -2 ^ (w - 1) → res = (BitVec.ofInt w (-2 ^ (w - 1)), { invalid := true })) ∧
      (2 ^ (w - 1) - 1 < i → res = (BitVec.ofInt w (2 ^ (w - 1) - 1), { invalid := true }))

/-- `ToFixedSpec` for a word (`CVT/ROUND/TRUNC/CEIL/FLOOR.W.fmt`). -/
def ToWordSpec (f : Format) (rm : RoundingMode) (a : Nat) (res : BitVec 32 × Flags) : Prop :=
  f.ToFixedSpec 32 rm a res

/-- `ToFixedSpec` for a longword (`CVT/ROUND/TRUNC/CEIL/FLOOR.L.fmt`). -/
def ToLongSpec (f : Format) (rm : RoundingMode) (a : Nat) (res : BitVec 64 × Flags) : Prop :=
  f.ToFixedSpec 64 rm a res

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

/-! ### `CMP.condn.fmt` (MD00086 Vol II-A Rev 6.06, p.136-140) -/

/-- **The 32 `CMP.condn.fmt` predicates**, by the 5-bit `condn` field: the "Relation `> < = ?`"
columns of Table 3.9 (p.138-139; the left half "Predicates" is `condn` = `cccc` = 0..15, the right
half "Negated Predicates" is `condn` = 16 + `cccc`), and the "Invalid Operand Exception" column
("no (non-signalling)" for `cccc` = 0..7, "yes (signalling)" for 8..15). Returns
`(>, <, =, ?, signalling)`. The comment names the CMP mnemonic; the shaded (reserved) rows 16, 20..24,
28..31 are listed too (their decoding is not this definition's business). -/
def cmpTable : Nat → Bool × Bool × Bool × Bool × Bool
  | 0 => (false, false, false, false, false)   -- AF
  | 1 => (false, false, false, true, false)    -- UN
  | 2 => (false, false, true, false, false)    -- EQ
  | 3 => (false, false, true, true, false)     -- UEQ
  | 4 => (false, true, false, false, false)    -- LT
  | 5 => (false, true, false, true, false)     -- ULT
  | 6 => (false, true, true, false, false)     -- LE
  | 7 => (false, true, true, true, false)      -- ULE
  | 8 => (false, false, false, false, true)    -- SAF
  | 9 => (false, false, false, true, true)     -- SUN
  | 10 => (false, false, true, false, true)    -- SEQ
  | 11 => (false, false, true, true, true)     -- SUEQ
  | 12 => (false, true, false, false, true)    -- SLT
  | 13 => (false, true, false, true, true)     -- SULT
  | 14 => (false, true, true, false, true)     -- SLE
  | 15 => (false, true, true, true, true)      -- SULE
  | 16 => (true, true, true, true, false)      -- AT (reserved)
  | 17 => (true, true, true, false, false)     -- OR
  | 18 => (true, true, false, true, false)     -- UNE
  | 19 => (true, true, false, false, false)    -- NE
  | 20 => (true, false, true, true, false)     -- UGE (reserved)
  | 21 => (true, false, true, false, false)    -- OGE (reserved)
  | 22 => (true, false, false, true, false)    -- UGT (reserved)
  | 23 => (true, false, false, false, false)   -- OGT (reserved)
  | 24 => (true, true, true, true, true)       -- SAT (reserved)
  | 25 => (true, true, true, false, true)      -- SOR
  | 26 => (true, true, false, true, true)      -- SUNE
  | 27 => (true, true, false, false, true)     -- SNE
  | 28 => (true, false, true, true, true)      -- SUGE (reserved)
  | 29 => (true, false, true, false, true)     -- SOGE (reserved)
  | 30 => (true, false, false, true, true)     -- SUGT (reserved)
  | _ => (true, false, false, false, true)     -- 31: SOGT (reserved)

/-- The `cmpTable` entry for a relation. -/
def cmpHolds (condn : Nat) : Format.Relation → Bool
  | .gt => (cmpTable condn).1
  | .lt => (cmpTable condn).2.1
  | .eq => (cmpTable condn).2.2.1
  | .un => (cmpTable condn).2.2.2.1

namespace Format

/-- **`CMP.condn.fmt`** on the encodings `a` (`fs`), `b` (`ft`) with the 5-bit `condn`: the predicate
value is the Table 3.9 entry of the operands' ordering relation (`cmpRel`: "unordered ... when at
least one operand value is NaN", "Comparisons ignore the sign of zero, so +0 equals -0", p.136);
"If one of the values is an SNaN, or if a signalling comparison is specified and at least one of the
values is a QNaN, an Invalid Operation condition is raised" (p.136; Operation p.140: `SNaN(fs) or
SNaN(ft) or (cond3 and (QNaN(fs) or QNaN(ft)))`); nothing else is signaled ("The comparison is exact
and neither overflows nor underflows", p.136). Writing the mask into `fd` is the instruction's. -/
def CmpSpec (f : Format) (condn : BitVec 5) (a b : Nat) (res : Bool × Flags) : Prop :=
  res.1 = cmpHolds condn.toNat (f.cmpRel a b) ∧
  (res.2.invalid = true ↔
    (f.IsSNaN a ∨ f.IsSNaN b ∨ ((cmpTable condn.toNat).2.2.2.2 = true ∧ (f.IsQNaN a ∨ f.IsQNaN b)))) ∧
  res.2.divZero = false ∧ res.2.overflow = false ∧ res.2.underflow = false ∧ res.2.inexact = false

/-! ### `MAX.fmt`, `MIN.fmt`, `MAXA.fmt`, `MINA.fmt` (MD00086 Vol II-A Rev 6.06, p.262-265) -/

/-- **The signed order of MAX/MIN**: `a < b` as values (`cmpRel`, `-∞ < finite < +∞`), and among
equal values `-0.0 < 0.0` (Table 4.1, p.264: `MAX(-0.0, 0.0) = 0.0`, `MIN(-0.0, 0.0) = -0.0`, either
operand order). For non-NaN operands only. -/
def SignedLt (f : Format) (a b : Nat) : Prop :=
  f.cmpRel a b = .lt ∨ (f.cmpRel a b = .eq ∧ f.signOf a = true ∧ f.signOf b = false)

/-- **The relation of the absolute values** `|a|`, `|b|`: the ordering relation of the operands
with their sign bits cleared (`signChanged true`, the `ABS.fmt` encoding). -/
def magRel (f : Format) (a b : Nat) : Relation :=
  f.cmpRel (f.signChanged true a) (f.signChanged true b)

/-- **When the result of MAX/MIN/MAXA/MINA on two non-NaN operands is `fs` (`a`)**, from the
Operation's functions (p.264): `MaxFP` "Returns the largest argument", `MinFP` "Returns the smallest
argument", `MaxAbsoluteFP` "Returns the argument with largest absolute value. For equal absolute
values, returns the largest argument", `MinAbsoluteFP` "Returns the argument with smallest absolute
value. For equal absolute values, returns the smallest argument"; "largest"/"smallest" in the
signed order `SignedLt` (Table 4.1). When neither operand is larger, they are the same encoding
(equal value and sign), and `a` is chosen. -/
def MinMaxPicksA (f : Format) : MinMaxOp → Nat → Nat → Prop
  | .max, a, b => ¬ f.SignedLt a b
  | .min, a, b => ¬ f.SignedLt b a
  | .maxa, a, b => f.magRel a b = .gt ∨ (f.magRel a b = .eq ∧ ¬ f.SignedLt a b)
  | .mina, a, b => f.magRel a b = .lt ∨ (f.magRel a b = .eq ∧ ¬ f.SignedLt b a)

/-- **`MAX.fmt`/`MIN.fmt`/`MAXA.fmt`/`MINA.fmt`** (`op`) on `a` (`fs`), `b` (`ft`) (p.262-265,
IEEE 754-2008 maxNum/minNum/maxNumMag/minNumMag): Invalid Operation exactly when an operand is an
SNaN (`if SNaN(v1) or SNaN(v2) then SignalException(InvalidOperand)`, p.263), nothing else signaled;
"Numbers are preferred to NaNs: if one input is a NaN, but not both, the value of the numeric input
is returned. If both are NaNs, the NaN in fs is returned" (p.263; Operation: `if NaN(v1) and NaN(v2)
then ftmp ← v1 elseif NaN(v1) then ftmp ← v2 elseif NaN(v2) then ftmp ← v1`), the NaN not made quiet
(Table 4.1, p.265: "Treat as if the SNaN were a QNaN (do not quieten the result)"); otherwise `a` or
`b` as `MinMaxPicksA` says. The result is an operand encoding, unchanged. Under FCSR.FS = 1 the
statements apply this to the flushed operands (`FlushedIn`, Table 6.8, `FS`, p.93) with no Inexact
for the flushing: MAX/MIN/MAXA/MINA are "Floating Point Comparison Instructions" (MD00082 Vol I-A Rev
6.01 Table 7.9, p.110) and "For floating-point comparisons, the Inexact exception is not signaled when
subnormal input operands are flushed" (§6.7.2.4, p.102). -/
def MinMaxSpec (f : Format) (op : MinMaxOp) (a b : Nat) (res : Nat × Flags) : Prop :=
  res.2 = (if f.IsSNaN a ∨ f.IsSNaN b then { invalid := true } else {}) ∧
  (f.IsNaN a → f.IsNaN b → res.1 = a) ∧
  (f.IsNaN a → ¬ f.IsNaN b → res.1 = b) ∧
  (¬ f.IsNaN a → f.IsNaN b → res.1 = a) ∧
  (¬ f.IsNaN a → ¬ f.IsNaN b → (f.MinMaxPicksA op a b → res.1 = a) ∧ (¬ f.MinMaxPicksA op a b → res.1 = b))

/-! ### `CLASS.fmt` (MD00086 Vol II-A Rev 6.06, p.132) -/

/-- **The class bit of an encoding** (p.132): "Bits 0 and 1 indicate NaN values: signaling NaN (bit 0)
and quiet NaN (bit 1). Bits 2, 3, 4, 5 classify negative values: infinity (bit 2), normal (bit 3),
subnormal (bit 4), and zero (bit 5). Bits 6, 7, 8, 9 classify positive values: infinity (bit 6),
normal (bit 7), subnormal (bit 8), and zero (bit 9)." A finite nonzero encoding is subnormal iff its
biased exponent is 0 (MD00082 Vol I-A Rev 6.01 Table 6.2, p.80, "E_min -1, ≠0"). -/
def classBit (f : Format) (a : Nat) : Nat :=
  match f.datum a with
  | .nan => if f.IsSNaN a then 0 else 1
  | .inf neg => if neg then 2 else 6
  | .num neg x => (if neg then 2 else 6) + (if x = 0 then 3 else if f.expOf a = 0 then 2 else 1)

/-- **`CLASS.fmt`**: the 10-bit mask with the one class bit of the operand set, "zero extended to
fmt-width bits"; the operand as encoded ("The input values and generated bit masks are not affected
by the flush-subnormal-to-zero mode FCSR.FS"); "No data-dependent exceptions are possible" (p.132). -/
def ClassSpec (f : Format) (a : Nat) (res : Nat) : Prop :=
  res = 2 ^ f.classBit a

/-! ### `RINT.fmt` (MD00086 Vol II-A Rev 6.06, p.337) -/

/-- **`RINT.fmt`** of `a` under `e` (p.337): "rounded to an integral valued floating-point number in
the same format based on the rounding mode bits RM"; it "corresponds to the roundToIntegralExact
operation" and "The Inexact exception is signaled if the result does not have the same numerical
value as the input operand". A NaN: `NaNResult` (the arithmetic-operation rule; IEEE Std 754-2019
§5.9, p.41: roundToIntegralExact "signals the invalid operation exception for a signaling NaN
operand"). `±∞`: `±∞`, no exception (§5.9: "infinite operands to infinite results of the same sign").
A finite `x` with sign bit `s`: the encoding of the integer `i` that is `x` correctly rounded to the
integers in FCSR.RM (Table 6.10, MD00082 Vol I-A Rev 6.01 p.95, over the integers), with sign bit `s`
(also for a zero result: IEEE Std 754-2019 §6.3, p.50, "the sign of the result of ... the
roundToIntegralExact ... is the sign of the first or only operand"; §5.9: "zero operands to zero
results of the same sign"; verified against 2019), Inexact iff `i ≠ x`, nothing else.
The operand is taken as encoded and FCSR.FS handled here: with FS = 1 a subnormal operand (biased
exponent 0, fraction `≠ 0`, Table 6.2, p.80) "is replaced with zero of the same sign" (MD00082 Vol I-A
Rev 6.01 Table 6.8, `FS`, p.93), the rounding of that zero is exact, and "Flushing of subnormal input
operands in all instructions except comparisons causes Inexact exception to be signaled" (§6.7.2.4,
p.102; RINT.fmt is a conversion instruction, Table 7.10, p.110): the zero of the operand's sign,
Inexact only. -/
def RintSpec (f : Format) (e : Env) (a : Nat) (res : Nat × Flags) : Prop :=
  if e.flush = true ∧ f.expOf a = 0 ∧ f.fracOf a ≠ 0 then
    res = (f.zeroBits (f.signOf a), { inexact := true })
  else
  match f.datum a with
  | .nan => f.NaNResult [a] res
  | .inf s => res = (f.infBits s, {})
  | .num s x => ∃ i : Int, CorrectlyRounded IsInt IsEvenInt e.rm (Cut.ofRat x) (i : Rat) ∧
      f.value res.1 = some (i : Rat) ∧ f.signOf res.1 = s ∧
      res.2 = (if (i : Rat) = x then {} else { inexact := true })

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

/-! ### `MADDF.fmt`, `MSUBF.fmt`: fused multiply-add (MD00086 Vol II-A Rev 6.06, p.259-260) -/

namespace Format

/-- `a × b` is `0 × ∞` or `∞ × 0`, with any signs. -/
def InfTimesZero (f : Format) (a b : Nat) : Prop :=
  match f.datum a, f.datum b with
  | .inf _, .num _ y => y = 0
  | .num _ x, .inf _ => x = 0
  | _, _ => False

/-- **A NaN among the operands `c`, `a`, `b` of `MADDF`/`MSUBF`**: the result value is as for the
other arithmetic operations (`NaNResult` over `[c, a, b]`: a quiet NaN, a passed operand when one is a
QNaN, no exception but Invalid), and Invalid is signaled iff an operand is a signaling NaN **or `a × b` is
`0 × ∞`**. MD00082 Vol I-A Rev 6.01 §6.7.2.1, p.100 lists "Multiplication: 0 × ∞, with any signs" as
invalid without exception; IEEE Std 754-2019 §7.2 c), p.52: invalid for `fusedMultiplyAdd(0, ∞, c)`
"unless c is a quiet NaN; if c is a quiet NaN then it is implementation defined whether the invalid
operation exception is signaled" (verified against 2019). Pin: signaled (QEMU `mips32r6-generic`
does the same). -/
def FmaNaNResult (f : Format) (c a b : Nat) (res : Nat × Flags) : Prop :=
  (∃ inv : Bool, f.NaNResult [c, a, b] (res.1, { res.2 with invalid := inv })) ∧
  (res.2.invalid = true ↔ (∃ x ∈ [c, a, b], f.IsSNaN x) ∨ f.InfTimesZero a b)

/-- The result when the exact product (negated for `MSUBF`) is the infinity of sign `p` and the
addend has datum `d`: the sum `(±∞) + (∓∞)` is invalid ("magnitude subtraction of infinities",
§6.7.2.1, p.100; IEEE Std 754-2019 §7.2 d), p.52, "addition or subtraction or fusedMultiplyAdd"),
otherwise the infinity, exactly (§6.3.1.3, p.81: "Arithmetic with ∞ is the limiting case of real
arithmetic ... regarded as exact and exception conditions do not arise"). -/
def FmaInfProduct (f : Format) (d : Datum) (p : Bool) (res : Nat × Flags) : Prop :=
  match d with
  | .inf r => if r = p then res = (f.infBits p, {}) else res = f.invalidResult
  | _ => res = (f.infBits p, {})

/-- **`MADDF.fmt` (`sub = false`) and `MSUBF.fmt` (`sub = true`)** (MD00086 Vol II-A Rev 6.06,
p.259-260): `c + a × b` resp. `c − a × b` with `c` = FPR fd, `a` = FPR fs, `b` = FPR ft, under `e`.
"The intermediate product is calculated to infinite precision. The product is added to the value in
FPR fd. The result sum is calculated to infinite precision, rounded according to the current rounding
mode in FCSR" (p.259); it "signals Inexact, Overflow, or Underflow if and only if the final result
differs from the infinite precision result in the appropriate manner" (p.260). IEEE Std 754-2019
§5.4.1, p.33: fusedMultiplyAdd "computes (x × y) + z as if with unbounded range and precision, rounding
only once to the destination format" (verified against 2019).

* A NaN operand: `FmaNaNResult`.
* `a × b` = `0 × ∞` (no NaN operand): Invalid (§6.7.2.1, p.100; IEEE §7.2 c)).
* An infinite product, of sign `s xor t` (negated for `MSUBF`): `FmaInfProduct`.
* A finite product and `c = ±∞`: `c`, exactly (§6.3.1.3, p.81).
* All finite: with `v` the exact `x ± y·z`, an exactly zero `v` is the zero of the common sign of the
  two terms `c` and `±a × b` (the product's sign is `s xor t`, negated for `MSUBF`) when they agree, else
  `+0`, or `−0` in RM — the manual is silent; IEEE Std 754-2019 §6.3, p.50: "When (a × b) + c is exactly
  zero, the sign of fusedMultiplyAdd(a, b, c) shall be determined by the rules above for a sum of
  operands" (as `AddSpec`; verified against 2019) — no exception; a nonzero `v` is `RoundEnvSpec` of
  `v` (one rounding; a result that rounds to zero keeps the sign of `v`, §6.3, p.50). -/
def FmaSpec (f : Format) (e : Env) (sub : Bool) (c a b : Nat) (res : Nat × Flags) : Prop :=
  match f.datum c, f.datum a, f.datum b with
  | .nan, _, _ => f.FmaNaNResult c a b res
  | _, .nan, _ => f.FmaNaNResult c a b res
  | _, _, .nan => f.FmaNaNResult c a b res
  | d, .inf s, .inf t => f.FmaInfProduct d (s ^^ t ^^ sub) res
  | d, .inf s, .num t y => if y = 0 then res = f.invalidResult else f.FmaInfProduct d (s ^^ t ^^ sub) res
  | d, .num s x, .inf t => if x = 0 then res = f.invalidResult else f.FmaInfProduct d (s ^^ t ^^ sub) res
  | .inf r, .num _ _, .num _ _ => res = (f.infBits r, {})
  | .num r w, .num s x, .num t y =>
    let v := if sub then w - x * y else w + x * y
    if v = 0 then
      res = (f.zeroBits (if r = (s ^^ t ^^ sub) then r else decide (e.rm = .RM)), {})
    else f.RoundEnvSpec e (Cut.ofRat v) res

end Format

end Mips.Fp
