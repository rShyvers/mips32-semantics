import Semantics.FpOps

/-!
# FpOpsSpec — the IEEE 754 reference the rounding core is proved against

Specification vocabulary only (definitions, no theorem): nothing in `Step.lean` or `FpOps.lean` uses
it. `Semantics/FpOpsCorrect*.lean` proves that the rounding core of `FpOps.lean`
(`Mips.Fp.Format.roundCore`) and the arithmetic built on it meet these definitions. The definitions
are written from the manual and the IEEE standard it references, **not** from `roundCore`:

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
  that tininess be detected after rounding"; "loss of accuracy is detected as inexact result".
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

/-- **The values of the format with the exponent range unbounded above** (IEEE 754-2008 §7.4: "the
magnitude of a rounded floating point result, were the exponent range unbounded"): precision `p`,
the denormalized range kept. -/
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

end Mips.Fp
