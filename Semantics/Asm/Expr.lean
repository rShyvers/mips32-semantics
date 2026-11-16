import Semantics.Asm.Syntax

/-!
# Asm.Expr — literals, expressions, registers and operand parsers

Numeric literals (GNU as radix rules), character and string literals (`scanQuoted`), `label±const`
expressions (`parseExpr`), range checks (nothing is ever truncated), GPR/FPR/coprocessor register
names and the `offset(base)` memory operand. Shared by every instruction-family table.
-/

namespace Asm


def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Non-empty digit string in the given base (2/8/10/16); no separators
(`1_000` is rejected), no sign. -/
def digitsToNat (base : Nat) (cs : List Char) : Option Nat :=
  if cs.isEmpty then none
  else
    cs.foldl
      (fun acc c => acc.bind fun a => (hexDigit? c).bind fun d =>
        if d < base then some (a * base + d) else none)
      (some 0)

/-- Unsigned integer literal with GNU-as radix rules: `0x…` hex, `0b…`
binary, a leading `0` followed by more digits is **octal** (`010` = 8, `08`
is an error), anything else decimal. -/
def parseNatLit (cs : List Char) : Option Nat :=
  match cs with
  | '0' :: 'x' :: r => digitsToNat 16 r
  | '0' :: 'X' :: r => digitsToNat 16 r
  | '0' :: 'b' :: r => digitsToNat 2 r
  | '0' :: 'B' :: r => digitsToNat 2 r
  | '0' :: c :: r => digitsToNat 8 (c :: r)
  | _ => digitsToNat 10 cs

def isOctDigit (c : Char) : Bool := '0' ≤ c && c ≤ '7'

def utf8Bytes (c : Char) : List Nat :=
  (String.singleton c).toUTF8.toList.map (·.toNat)

/-- Scan the body of a quoted literal (the opening quote `q` already
consumed): returns the decoded bytes and the source text after the closing
quote. Escapes (GNU as set plus `\'`): `\n \t \r \b \f \\ \" \'`, octal
`\N`/`\NN`/`\NNN` (so `\0` is NUL; a value above `\377` is an error) and
hex `\xH`/`\xHH` (at most two digits: `"\x41b"` is `A`,`b`, whereas GNU as
would swallow every following hex digit). Any other escape letter is an
error (MARS 4.5 has no octal/hex escapes -- it stores `"\101"` as the three
characters `1`,`0`,`1`). Unescaped characters contribute
their UTF-8 bytes. -/
def scanQuoted (q : Char) : Nat → List Char → List Nat → Except String (List Nat × List Char)
  | 0, _, _ => .error s!"missing closing {q}"
  | fuel + 1, cs, acc =>
    match cs with
    | [] => .error s!"missing closing {q}"
    | '\\' :: [] => .error "dangling '\\' at end of literal"
    | '\\' :: e :: rest =>
      if e == 'x' then
        let hs := (rest.take 2).takeWhile (fun c => (hexDigit? c).isSome)
        match digitsToNat 16 hs with
        | some v => scanQuoted q fuel (rest.drop hs.length) (v :: acc)
        | none => .error "\\x escape needs at least one hex digit"
      else if isOctDigit e then
        let ds := ((e :: rest).take 3).takeWhile isOctDigit
        match digitsToNat 8 ds with
        | some v =>
          if v < 256 then scanQuoted q fuel ((e :: rest).drop ds.length) (v :: acc)
          else .error "octal escape out of range (max \\377)"
        | none => .error "bad octal escape"
      else
        let simple : Option Nat :=
          if e == 'n' then some 10 else if e == 't' then some 9 else if e == 'r' then some 13
          else if e == 'b' then some 8 else if e == 'f' then some 12
          else if e == '\\' then some 92 else if e == '"' then some 34 else if e == '\'' then some 39
          else none
        match simple with
        | some b => scanQuoted q fuel rest (b :: acc)
        | none => .error s!"unknown escape '\\{e}'"
    | c :: rest =>
      if c == q then .ok (acc.reverse, rest)
      else scanQuoted q fuel rest ((utf8Bytes c).reverse ++ acc)

/-- Decode a complete `"..."` operand token into its bytes; anything after
the closing quote is an error. -/
def parseStringTok (tok : String) (line : Nat) : Except AsmError (List Nat) :=
  match tok.toList with
  | '"' :: body =>
    match scanQuoted '"' (body.length + 1) body [] with
    | .ok (bytes, rest) =>
      if rest.isEmpty then pure bytes
      else throw (.badOperand s!"unexpected text after string literal: '{String.ofList rest}'" line)
    | .error m => throw (.badOperand s!"bad string literal {tok}: {m}" line)
  | _ => throw (.badOperand s!"expected a quoted string, got '{tok}'" line)

/-- Unsigned atom: an integer literal or a `'c'` character literal (exactly
one byte, escapes as in strings). -/
def parseAtomNat (cs : List Char) (line : Nat) : Except AsmError Nat :=
  match cs with
  | '\'' :: body =>
    match scanQuoted '\'' (body.length + 1) body [] with
    | .ok ([b], []) => pure b
    | .ok _ => throw (.badImmediate s!"character literal must be exactly one byte: {String.ofList cs}" line)
    | .error m => throw (.badImmediate s!"bad character literal {String.ofList cs}: {m}" line)
  | _ =>
    match parseNatLit cs with
    | some n => pure n
    | none => throw (.badImmediate s!"invalid immediate: '{String.ofList cs}'" line)

/-- Split an operand expression into signed atoms: `lbl+4-'a'` ↦
`[(false, lbl), (false, 4), (true, 'a')]`. Unary sign runs compose. -/
def splitTerms (cs : List Char) : List (Bool × List Char) := Id.run do
  let mut out : Array (Bool × List Char) := #[]
  let mut neg := false
  let mut cur : List Char := []
  let mut st := QState.normal
  for c in cs do
    if st.isNormal && (c == '+' || c == '-') then
      if (trimChars cur).isEmpty then
        if c == '-' then neg := !neg
        cur := []
      else
        out := out.push (neg, trimChars cur.reverse)
        neg := c == '-'
        cur := []
    else
      cur := c :: cur
      st := st.next c
  return (out.push (neg, trimChars cur.reverse)).toList

/-- Parse an operand expression `term (± term)*` where at most one term is
a symbol (which must be added, not subtracted) and the rest are integer /
character literals. Returns the symbol (if any) and the constant part. -/
def parseExpr (tok : String) (line : Nat) : Except AsmError (Option String × Int) := do
  let terms := splitTerms tok.toList
  let mut sym : Option String := none
  let mut k : Int := 0
  for (neg, atom) in terms do
    match atom with
    | [] => throw (.badImmediate s!"malformed expression '{tok}'" line)
    | c :: _ =>
      if c.isDigit || c == '\'' then
        let n ← parseAtomNat atom line
        k := if neg then k - (n : Int) else k + (n : Int)
      else if isIdent atom then
        if neg then throw (.badOperand s!"cannot subtract a label in '{tok}'" line)
        if sym.isSome then throw (.badOperand s!"more than one label in '{tok}'" line)
        sym := some (String.ofList atom)
      else
        throw (.badImmediate s!"invalid immediate: '{tok}'" line)
  pure (sym, k)

/-- Parse a pure numeric constant operand: decimal, `0x` hex, `0b` binary,
leading-0 octal, `'c'` character literals, optional leading `+`/`-`, and
`±`-sums of those. A label is an error here. -/
def parseImmediate (tok : String) (line : Nat) : Except AsmError Int := do
  let (sym, k) ← parseExpr tok line
  match sym with
  | none => pure k
  | some s => throw (.badImmediate s!"expected a numeric constant, got '{s}' in '{tok}'" line)

/-- Reject `v` outside `lo..hi` -- the assembler never truncates an
out-of-range immediate. -/
def checkRange (what : String) (lo hi v : Int) (line : Nat) : Except AsmError Unit :=
  if lo ≤ v ∧ v ≤ hi then pure ()
  else throw (.badImmediate s!"{what} out of range ({lo}..{hi}): {v}" line)

-- ====================================================================
-- Registers
-- ====================================================================

def regTable : List (String × Nat) :=
  [("zero", 0), ("at", 1), ("v0", 2), ("v1", 3),
   ("a0", 4), ("a1", 5), ("a2", 6), ("a3", 7),
   ("t0", 8), ("t1", 9), ("t2", 10), ("t3", 11), ("t4", 12), ("t5", 13), ("t6", 14), ("t7", 15),
   ("s0", 16), ("s1", 17), ("s2", 18), ("s3", 19), ("s4", 20), ("s5", 21), ("s6", 22), ("s7", 23),
   ("t8", 24), ("t9", 25),
   ("k0", 26), ("k1", 27),
   ("gp", 28), ("sp", 29), ("fp", 30), ("s8", 30), ("ra", 31)]

/-- Canonical decimal register number `0`..`31`: digits only, no leading
zero (`$08`), no separators (`$1_0`), no other radix. -/
def parseRegNum (cs : List Char) : Option Nat :=
  if cs.isEmpty || !cs.all Char.isDigit || (cs.length > 1 && cs.head? == some '0') then none
  else
    match digitsToNat 10 cs with
    | some n => if n < 32 then some n else none
    | none => none

def parseRegister (tok : String) (line : Nat) : Except AsmError Nat := do
  if !(tok.startsWith "$") then
    throw (.badRegister s!"register name must start with '$': '{tok}'" line)
  let body := dropS tok 1
  match regTable.find? (fun p => p.1 == body) with
  | some (_, n) => pure n
  | none =>
    match parseRegNum body.toList with
    | some n => pure n
    | none => throw (.badRegister s!"unknown register: '{tok}'" line)

/-- `$f0`..`$f31`, the coprocessor-1 (FPU) single-precision register names. -/
def fpRegTable : List (String × Nat) :=
  (List.range 32).map (fun i => (s!"f{i}", i))

/-- Parse an FP register operand. Unlike `parseRegister`, there is no raw
numeric fallback (`$5` is never an FP register) — FPU operands always use
the `$fN` spelling, matching real MIPS32 assembly syntax. -/
def parseFpRegister (tok : String) (line : Nat) : Except AsmError Nat := do
  if !(tok.startsWith "$") then
    throw (.badRegister s!"FP register name must start with '$': '{tok}'" line)
  let body := dropS tok 1
  match fpRegTable.find? (fun p => p.1 == body) with
  | some (_, n) => pure n
  | none => throw (.badRegister s!"unknown FP register (expected '$f0'..'$f31'): '{tok}'" line)

/-- Parse a coprocessor register-*number* operand (`mfc0`/`mtc0`'s `rd`,
`cfc1`/`ctc1`'s control register): the standard `$N` spelling (`$12`,
canonical decimal, 0-31) or the bare number `12` this assembler has always
accepted. Named GPR aliases (`$t4`) are deliberately not accepted here. -/
def parseCopRegister (what : String) (tok : String) (line : Nat) : Except AsmError Nat := do
  let body := if tok.startsWith "$" then dropS tok 1 else tok
  match parseRegNum body.toList with
  | some n => pure n
  | none => throw (.badRegister s!"expected a {what} register number 0-31 ('$N' or 'N'), got '{tok}'" line)

/-- Parse a `offset(reg)` or `(reg)` memory operand (whitespace allowed around the parts:
`4 ($sp)`). The offset must be a numeric constant in `lo..hi` (the width of the instruction's
offset field: signed 16 bits for the classic loads/stores, signed 9 bits for the Release 6
`ll`/`sc`/`pref`). -/
def parseMemOperandIn (lo hi : Int) (tok : String) (line : Nat) : Except AsmError (Int × Nat) := do
  match splitTop tok.toList '(' with
  | [immCs, restCs] =>
    let rest := trimChars restCs
    if rest.getLast? != some ')' then
      throw (.badOperand s!"missing closing ')' in operand '{tok}'" line)
    let regStr := String.ofList (trimChars rest.dropLast)
    let immStr := String.ofList (trimChars immCs)
    let imm ← if immStr.isEmpty then pure (0 : Int) else parseImmediate immStr line
    checkRange "memory offset" lo hi imm line
    let reg ← parseRegister regStr line
    pure (imm, reg)
  | _ => throw (.badOperand s!"expected 'offset(register)' operand, got '{tok}'" line)

/-- `offset(reg)` with a signed 16-bit offset. -/
def parseMemOperand (tok : String) (line : Nat) : Except AsmError (Int × Nat) :=
  parseMemOperandIn (-32768) 32767 tok line

/-- Parse a software `code`/`stype`/`sel`/`hint` operand in `0..maxCode`. -/
def parseCode (name what : String) (maxCode : Int) (tok : String) (line : Nat) :
    Except AsmError Nat := do
  let c ← parseImmediate tok line
  checkRange s!"{name} {what}" 0 maxCode c line
  pure c.toNat

end Asm
