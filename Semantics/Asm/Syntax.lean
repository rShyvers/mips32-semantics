import Semantics.Word
import Semantics.Types

/-!
# Asm.Syntax — errors, line splitting, labels

The first stage of the assembler (`Semantics/Asm.lean` is the root): the error type, the
segment base addresses, and `parseLine`, which splits one source line into its labels, its
(lower-cased) mnemonic and its comma-separated operand tokens. `#`, `:` and `,` inside string
and character literals are never syntax (`QState`).
-/

/-- Errors produced by `assemble`. Each case carries a human-readable message
and the 1-based source line number where the problem was detected. -/
inductive AsmError where
  | unknownMnemonic (msg : String) (line : Nat)
  | badRegister (msg : String) (line : Nat)
  | undefinedLabel (msg : String) (line : Nat)
  | badImmediate (msg : String) (line : Nat)
  | badDirective (msg : String) (line : Nat)
  | badOperand (msg : String) (line : Nat)
  | duplicateLabel (msg : String) (line : Nat)
  deriving Repr, DecidableEq

/-- Result of assembling source text: either a `Program` or the first error
encountered. -/
abbrev AsmResult := Except AsmError Program

/-- Base address of the `.data` segment (SPEC-NOTES §1; `textBase` lives in
`Types.lean`). -/
def dataBase : W32 := 0x10010000

/-- Default base address of the `.ktext` (kernel text) segment: the MIPS32
general exception vector (`exceptionVectorAddr` in `Types.lean`), so an
exception handler can be assembled where `Step.lean` dispatches to. -/
def ktextBase : W32 := 0x80000180

/-- Default base address of the `.kdata` (kernel data) segment (MARS/SPIM
convention). -/
def kdataBase : W32 := 0x90000000

/-- A natural number as a 32-bit word (modulo 2^32). -/
def natToW32 (n : Nat) : W32 := BitVec.ofNat 32 n

namespace Asm

/-- `String.drop`/`.take`/`.dropEnd` return `String.Slice` in this Lean
version; these wrappers convert back to `String` for uniform downstream use. -/
def dropS (s : String) (n : Nat) : String := (s.drop n).toString

def trimChars (cs : List Char) : List Char :=
  ((cs.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- Quote-tracking state shared by every line-level scanner (comment
stripping, label splitting, operand splitting), so that `#`, `:` and `,`
inside a `"..."` string or a `'c'` character literal are never treated as
syntax. -/
inductive QState
  | normal | str | strEsc | chr | chrEsc

def QState.next (st : QState) (c : Char) : QState :=
  match st with
  | .normal => if c == '"' then .str else if c == '\'' then .chr else .normal
  | .str => if c == '\\' then .strEsc else if c == '"' then .normal else .str
  | .strEsc => .str
  | .chr => if c == '\\' then .chrEsc else if c == '\'' then .normal else .chr
  | .chrEsc => .chr

def QState.isNormal : QState → Bool
  | .normal => true
  | _ => false

/-- Strip a `#` line comment, but not one occurring inside a `"..."` string
or `'c'` character literal (so `.asciiz "a # b"` and `li $t0, '#'` keep
their `#`). -/
def stripComment (cs : List Char) : List Char := Id.run do
  let mut result : List Char := []
  let mut st := QState.normal
  for c in cs do
    if st.isNormal && c == '#' then
      break
    result := c :: result
    st := st.next c
  return result.reverse

/-- Split at every `sep` that is outside string/character literals. Always
returns at least one piece. -/
def splitTop (cs : List Char) (sep : Char) : List (List Char) := Id.run do
  let mut parts : Array (List Char) := #[]
  let mut cur : List Char := []
  let mut st := QState.normal
  for c in cs do
    if st.isNormal && c == sep then
      parts := parts.push cur.reverse
      cur := []
    else
      cur := c :: cur
      st := st.next c
  return (parts.push cur.reverse).toList

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '.' || c == '$'
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.' || c == '$'

/-- A valid label/symbol name: `[A-Za-z_.$][A-Za-z0-9_.$]*`. -/
def isIdent (cs : List Char) : Bool :=
  match cs with
  | [] => false
  | c :: rest => isIdentStart c && rest.all isIdentChar

/-- A single parsed source line: the labels defined on it (possibly several,
`a: b: .word 1`), optional mnemonic (`none` for a label-only or blank line;
always lower-cased -- mnemonics and directives are case-insensitive, as in
GNU as), and its comma-separated operand tokens (trimmed, never empty; string
operands are kept in their quoted source form and decoded by the directive
that consumes them). -/
structure ParsedLine where
  labels : List String
  mnemonic : Option String
  operands : List String
  lineNo : Nat

def parseLine (lineNo : Nat) (rawLine : String) : Except AsmError ParsedLine := do
  let cs := trimChars (stripComment rawLine.toList)
  if cs.isEmpty then
    return { labels := [], mnemonic := none, operands := [], lineNo }
  -- Label splitting: every `:` outside quotes ends a label, and the text in
  -- front of it must be a valid identifier (so `addi $a0,$a0,5 :`, `1bad:`,
  -- `a b:` and a bare `:` are errors instead of silently becoming labels).
  let pieces := (splitTop cs ':').map trimChars
  let labelPieces := pieces.dropLast
  let stmt := pieces.getLast?.getD []
  for lp in labelPieces do
    if !isIdent lp then
      throw (.badOperand s!"invalid label name '{String.ofList lp}' before ':'" lineNo)
  let labels := labelPieces.map String.ofList
  if stmt.isEmpty then
    return { labels, mnemonic := none, operands := [], lineNo }
  let mnemCs := stmt.takeWhile (fun c => !c.isWhitespace)
  let mnem := String.ofList (mnemCs.map Char.toLower)
  let rest := trimChars (stmt.drop mnemCs.length)
  if rest.isEmpty then
    return { labels, mnemonic := some mnem, operands := [], lineNo }
  let operandCs := (splitTop rest ',').map trimChars
  if operandCs.any List.isEmpty then
    throw (.badOperand s!"empty operand in '{String.ofList stmt}'" lineNo)
  return { labels, mnemonic := some mnem, operands := operandCs.map String.ofList, lineNo }

end Asm
