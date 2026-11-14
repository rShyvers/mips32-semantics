import Semantics.Manual.Choices

/-!
# Manual.Accuracy — the numeric accuracy `RECIP.fmt` and `RSQRT.fmt` require

The pages leave the result of `RECIP.fmt` and `RSQRT.fmt` to the implementation within a bound
(MD00086 Vol II-A Rev 6.06, RECIP.fmt, p.336: "The computed result differs from the both the exact
result and the IEEE-mandated representation of the exact result by no more than one unit in the
least-significant place (ULP)"; RSQRT.fmt, p.343: "... by no more than two units in the
least-significant place (ULP)"). `Impl.RecipAccurate` (`Manual/Choices.lean`) states the bound
against the IEEE-mandated representation; this file states the bounds against the **exact** result,
on the values of the encodings:

* `FPValue eb fb n` — the value of an `eb`-exponent-bit, `fb`-fraction-bit encoding, MD00082 Vol I-A
  Rev 6.01 §6.3, Table 6.1 (p.78-79), Table 6.2 (p.80-81): `(-1)^s × 2^E × 1.f` for a normalized
  number with `E = e - bias`, `(-1)^s × 2^E_min × 0.f` for a denormalized number or zero
  (`E_min = 1 - bias`), no value for `E_max + 1` (±∞, NaN).
* `ULP eb fb ex` — the unit in the least-significant place of a number in `[2^ex, 2^(ex+1))`: the
  weight `2^(ex - (p - 1))` of the last significand bit of a normalized number, or the denormalized
  unit `2^(E_min - (p - 1))` below `2^E_min` (`p = fb + 1`, Table 6.1). The ULP of the **exact**
  result is used.
* `Impl.RecipExact`, `Impl.RsqrtAccurate` — the two bounds, without flushing (FCSR.FS = 0: with
  FS = 1 a tiny result may be replaced by zero, MD00082 Vol I-A Rev 6.01 §6.7.2.4, p.102, which no
  ULP bound survives). For `RECIP` the exact result `1/x` must be at most the largest finite number:
  beyond it the IEEE-mandated representation itself overflows.
* `Impl.Valid` — a valid implementation: `Impl.WF` and the three bounds.
-/

namespace Manual

/-- **The value of an encoding** with `eb` exponent bits and `fb` fraction bits (MD00082 Vol I-A
Rev 6.01 Table 6.2, p.80-81; bias `2^(eb-1) - 1`, Table 6.1 p.79). -/
def FPValue (eb fb : Nat) (n : Nat) : Option Rat :=
  if n < 2 ^ (1 + eb + fb) then
    let s : Rat := if (n / 2 ^ (eb + fb)) % 2 = 1 then -1 else 1
    let e : Nat := (n / 2 ^ fb) % 2 ^ eb
    let fr : Rat := ((n % 2 ^ fb : Nat) : Rat) / (2 : Rat) ^ fb
    if e = 2 ^ eb - 1 then none
    else if e = 0 then some (s * (2 : Rat) ^ (1 - ((2 ^ (eb - 1) - 1 : Nat) : Int)) * fr)
    else some (s * (2 : Rat) ^ ((e : Int) - ((2 ^ (eb - 1) - 1 : Nat) : Int)) * (1 + fr))
  else none

/-- The largest finite number `(2^(fb+1) - 1) × 2^(E_max - fb)` (`E_max` = the bias, Table 6.1). -/
def FPMax (eb fb : Nat) : Rat :=
  ((2 ^ (fb + 1) - 1 : Nat) : Rat) * (2 : Rat) ^ (((2 ^ (eb - 1) - 1 : Nat) : Int) - fb)

/-- **The unit in the least-significant place** of a number in `[2^ex, 2^(ex+1))`. -/
def ULP (eb fb : Nat) (ex : Int) : Rat :=
  (2 : Rat) ^ (max (1 - ((2 ^ (eb - 1) - 1 : Nat) : Int) - fb) (ex - fb))

/-- `r` is within `k` ULP of the exact value `v ≠ 0` (the ULP of `v`'s binade `2^ex ≤ |v| < 2^(ex+1)`). -/
def WithinULPs (eb fb : Nat) (v r : Rat) (k : Nat) : Prop :=
  ∃ ex : Int, (2 : Rat) ^ ex ≤ v.abs ∧ v.abs < (2 : Rat) ^ (ex + 1) ∧ (r - v).abs ≤ k * ULP eb fb ex

/-- `r` is within `k` ULP of `1/√y` (`y > 0`), stated by squares since `1/√y` need not be rational:
`2^ex ≤ 1/√y < 2^(ex+1)` is `2^ex · 2^ex · y ≤ 1 < 2^(ex+1) · 2^(ex+1) · y`, and
`r - kU ≤ 1/√y ≤ r + kU` is `(r - kU ≤ 0 ∨ (r - kU)² y ≤ 1) ∧ (0 ≤ r + kU ∧ 1 ≤ (r + kU)² y)`. -/
def WithinULPsRsqrt (eb fb : Nat) (y r : Rat) (k : Nat) : Prop :=
  ∃ ex : Int, (2 : Rat) ^ ex * (2 : Rat) ^ ex * y ≤ 1 ∧ 1 < (2 : Rat) ^ (ex + 1) * (2 : Rat) ^ (ex + 1) * y ∧
    (r - k * ULP eb fb ex ≤ 0 ∨ (r - k * ULP eb fb ex) * (r - k * ULP eb fb ex) * y ≤ 1) ∧
    (0 ≤ r + k * ULP eb fb ex ∧ 1 ≤ (r + k * ULP eb fb ex) * (r + k * ULP eb fb ex) * y)

/-- **`RECIP.fmt` against the exact result** (RECIP.fmt, p.336): without flushing, for a finite
nonzero `fs` whose exact reciprocal is at most the largest finite number, a finite result is within
1 ULP of `1/fs`. -/
def Impl.RecipExact (i : Impl) : Prop :=
  (∀ (e : Mips.Fp.Env) (x : W32) (y : Rat), e.flush = false → FPValue 8 23 x.toNat = some y → y ≠ 0 →
    (1 / y).abs ≤ FPMax 8 23 →
    ∀ r, FPValue 8 23 (i.recipS e x).1.toNat = some r → WithinULPs 8 23 (1 / y) r 1) ∧
  (∀ (e : Mips.Fp.Env) (x : BitVec 64) (y : Rat), e.flush = false → FPValue 11 52 x.toNat = some y →
    y ≠ 0 → (1 / y).abs ≤ FPMax 11 52 →
    ∀ r, FPValue 11 52 (i.recipD e x).1.toNat = some r → WithinULPs 11 52 (1 / y) r 1)

/-- **`RSQRT.fmt` against the exact result** (RSQRT.fmt, p.343): without flushing, for a finite
positive `fs`, a finite result is within 2 ULP of `1/√fs`. -/
def Impl.RsqrtAccurate (i : Impl) : Prop :=
  (∀ (e : Mips.Fp.Env) (x : W32) (y : Rat), e.flush = false → FPValue 8 23 x.toNat = some y → 0 < y →
    ∀ r, FPValue 8 23 (i.rsqrtS e x).1.toNat = some r → WithinULPsRsqrt 8 23 y r 2) ∧
  (∀ (e : Mips.Fp.Env) (x : BitVec 64) (y : Rat), e.flush = false → FPValue 11 52 x.toNat = some y →
    0 < y → ∀ r, FPValue 11 52 (i.rsqrtD e x).1.toNat = some r → WithinULPsRsqrt 11 52 y r 2)

/-- **A valid implementation**: of this profile (`Impl.WF`) and with the accuracy the pages require:
`RECIP.fmt` within 1 ULP of the IEEE-mandated representation (`Impl.RecipAccurate`) and of the exact
result (`Impl.RecipExact`), `RSQRT.fmt` within 2 ULP of the exact result (`Impl.RsqrtAccurate`). -/
def Impl.Valid (i : Impl) : Prop := i.WF ∧ i.RecipAccurate ∧ i.RecipExact ∧ i.RsqrtAccurate

end Manual
