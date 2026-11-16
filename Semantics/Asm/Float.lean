import Semantics.Asm.Expr

/-!
# Asm.Float — `.float` / `.double` literals

Exact decimal → IEEE 754 binary32/binary64 conversion (`ratToIeee`), correctly rounded to
nearest-even in exact `Nat` arithmetic; no host floating point is involved.
-/

namespace Asm


/-- Correctly rounded (round-to-nearest, ties-to-even) IEEE-754 encoding of
the exact rational `num/den` (`den > 0`), computed in exact `Nat`/`Int`
arithmetic -- no host floating point is involved. `p` is the precision in
bits (24 single / 53 double), `ebits` the exponent-field width (8 / 11).
Handles subnormals; values that round beyond the largest finite number
become ±infinity (as in IEEE-754 and Java/GNU as). -/
def ratToIeee (p ebits : Nat) (neg : Bool) (num den : Nat) : Nat :=
  let signBit := if neg then 2 ^ (p - 1 + ebits) else 0
  if num == 0 then signBit
  else
    let bias : Int := 2 ^ (ebits - 1) - 1
    -- exponent of the least-significant mantissa bit of the smallest normal
    let qmin : Int := 1 - bias - ((p : Int) - 1)
    let e0 : Int := (Nat.log2 num : Int) - (Nat.log2 den : Int)
    -- is num/den ≥ 2^e ?
    let ge (e : Int) : Bool :=
      if e ≥ 0 then decide (num ≥ den * 2 ^ e.toNat) else decide (num * 2 ^ (-e).toNat ≥ den)
    let e : Int := if ge e0 then e0 else e0 - 1      -- floor(log2(num/den))
    let q : Int := max (e - ((p : Int) - 1)) qmin    -- exponent of one ulp
    let n' := if q ≥ 0 then num else num * 2 ^ (-q).toNat
    let d' := if q ≥ 0 then den * 2 ^ q.toNat else den
    let fl := n' / d'
    let rem := n' % d'
    let m :=
      if 2 * rem > d' then fl + 1
      else if 2 * rem < d' then fl
      else if fl % 2 == 1 then fl + 1 else fl
    -- `m < 2^(p-1)` (subnormal) only when `q = qmin`, where the exponent
    -- field is 0; otherwise the implicit leading 1 of `m` adds 1 to the
    -- exponent field, and a carry to `m = 2^p` adds one more -- all three
    -- cases fall out of this single addition.
    let bits := (q - qmin).toNat * 2 ^ (p - 1) + m
    let infBits := (2 ^ ebits - 1) * 2 ^ (p - 1)
    signBit + (if bits ≥ infBits then infBits else bits)

/-- Parse a `.float`/`.double` operand: `[+-]digits[.digits][e[+-]digits]`
(at least one mantissa digit), or `inf`/`infinity`/`nan` (case-insensitive,
optionally signed; `nan` is the quiet NaN `0x7fc00000`/`0x7ff8000000000000`).
Returns the IEEE-754 bit pattern. -/
def parseFloatLit (p ebits : Nat) (tok : String) (line : Nat) : Except AsmError Nat := do
  let bad : AsmError := .badImmediate s!"invalid floating-point literal: '{tok}'" line
  let cs0 := tok.toList.map Char.toLower
  let (neg, cs) : Bool × List Char :=
    match cs0 with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let signBit := if neg then 2 ^ (p - 1 + ebits) else 0
  let infBits := (2 ^ ebits - 1) * 2 ^ (p - 1)
  let s := String.ofList cs
  if s == "inf" || s == "infinity" then return signBit + infBits
  if s == "nan" then return signBit + infBits + 2 ^ (p - 2)
  let intD := cs.takeWhile Char.isDigit
  let r1 := cs.drop intD.length
  let (fracD, r2) : List Char × List Char :=
    match r1 with
    | '.' :: r => (r.takeWhile Char.isDigit, r.dropWhile Char.isDigit)
    | r => ([], r)
  if intD.isEmpty && fracD.isEmpty then throw bad
  let exp10 : Int ←
    match r2 with
    | [] => pure 0
    | 'e' :: r =>
      let (eneg, ds) : Bool × List Char :=
        match r with
        | '-' :: d => (true, d)
        | '+' :: d => (false, d)
        | d => (false, d)
      match digitsToNat 10 ds with
      | some e =>
        if e > 5000 then
          throw (.badImmediate s!"floating-point exponent too large in '{tok}'" line)
        else pure (if eneg then -(e : Int) else (e : Int))
      | none => throw bad
    | _ => throw bad
  let mant := (digitsToNat 10 (intD ++ fracD)).getD 0
  let e : Int := exp10 - (fracD.length : Int)
  let num := if e ≥ 0 then mant * 10 ^ e.toNat else mant
  let den := if e ≥ 0 then 1 else 10 ^ (-e).toNat
  pure (ratToIeee p ebits neg num den)

end Asm
