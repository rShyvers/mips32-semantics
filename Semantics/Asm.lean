import Std.Data.HashMap.Basic
import Semantics.Word
import Semantics.Types
import Semantics.Instruction

/-!
# Asm — MIPS assembler

Converts assembler source text for the modeled MIPS32 instruction set into a
`Program` (`Std.HashMap W32 W32`, PC → instruction word). Builds raw instruction
words directly via `mkRT` / `mkIT` / `mkJT` (Types.lean) — this module does
**not** depend on an `Instruction` enum.

## Supported syntax
- Labels (`name:`, one or more per line), optionally followed by an
  instruction/directive on the same line. A label name must match
  `[A-Za-z_.$][A-Za-z0-9_.$]*`; any other text in front of a `:` (outside
  quotes) is an error.
- Directives (case-insensitive): segments `.text`/`.data`/`.ktext`/`.kdata`
  (each with an optional start-address operand); data `.word`, `.half`,
  `.byte`, `.float`, `.double`, `.ascii`, `.asciiz` (= `.asciz`/`.string`),
  `.space`; `.align n`; and `.globl`/`.global`/`.extern` (accepted, no-ops).
- `#` line comments (honoring `"..."` string and `'c'` character literals,
  so `#`/`:`/`,` inside them are not treated as syntax).
- Mnemonics are case-insensitive (`ADD`, `Add`), as in GNU as; register
  names are case-sensitive.
- Numeric operands: decimal, `0x` hex, `0b` binary, **leading-`0` octal**
  (`010` = 8, as GNU as and MARS), character literals `'a'`/`'\n'`, an
  optional leading `+`/`-`, and `±` sums of those. No digit separators.
  `la`, `.word` and branch/jump targets also take `label+const` /
  `label-const`.
- **Nothing is ever truncated**: every immediate, offset, branch/jump
  displacement and data value is range-checked and rejected with an error
  carrying the source line number if it does not fit (see "Range checks"
  below). Out-of-range immediates are *not* macro-expanded.
- Empty operands (`add $t0,, $t1`, a trailing `,`) are errors.
- Assembler idioms expanding to existing instructions (GNU as expansions;
  none inserts a `nop` -- this assembler always behaves like GNU as under
  `.set noreorder`, every branch keeps its real delay slot): `b`, `bal`,
  `beqz`, `bnez`, `neg`, `negu`, `not`, `abs`, `blt`/`bge`/`bgt`/`ble`,
  `bltu`/`bgeu`/`bgtu`/`bleu` (via `$at`), `ssnop`, `ehb`, `pause`, `nal`, `jr.hb`,
  `jalr.hb` -- see `expandIdiom`.
- Optional code operands, in GNU as operand syntax: `break [code[, code2]]`
  (each 0..1023: `code` goes to bits 25..16 and `code2` to bits 15..6 of the
  20-bit field), `syscall [code]` (0..0xFFFFF), `teq rs, rt[, code]` (all six
  register traps, 0..1023), `sync [stype]` (0..31), `wait [code]`
  (0..0x7FFFF) and `mfc0`/`mtc0 rt, rd[, sel]` (0..7). The `Instruction`
  constructors carry these fields, so every value is encoded.
- FPU: `c.cond.s`/`c.cond.d` for all sixteen predicates with an optional
  leading condition code (`c.lt.s $fcc3, $f2, $f4`; `$fccN` or a bare `N`),
  `bc1f`/`bc1t`/`bc1fl`/`bc1tl [cc,] target`, `movf`/`movt rd, rs[, cc]`,
  `movf.fmt`/`movt.fmt fd, fs[, cc]`, `movn.fmt`/`movz.fmt fd, fs, rt`,
  `mfhc1`/`mthc1`, the indexed `lwxc1`/`ldxc1 fd, index(base)`,
  `swxc1`/`sdxc1 fs, index(base)`, `prefx hint, index(base)`,
  `madd.fmt`/`msub.fmt`/`nmadd.fmt`/`nmsub.fmt fd, fr, fs, ft`, `recip.fmt`,
  `rsqrt.fmt`, and `round`/`trunc`/`ceil`/`floor.w.d`.
- `pref hint, offset(base)`, `di [rt]`, `ei [rt]`, `sb`.
- `.set noreorder`, `.set noat`, `.set at` are accepted. This assembler never
  reorders, so `.set noreorder` changes nothing; after `.set noat` the idioms
  that expand through `$at` (`blt`/`bge`/… ) are rejected. `.set reorder` is
  **rejected** (it would ask the assembler to fill delay slots, which this
  one never does), as is every other `.set` option.
- All v1 real instructions (`docs/spec/INSTRUCTION-REF.md`): R-type arith/
  logic/shift/mult-div/mfhi/mflo, I-type immediate/logic/memory, J-type,
  branches, and `syscall` (zero operands, all fields zero except
  funct = 0x0c, i.e. word `0x0000000C`). Plus the MIPS32/MIPS32r2 additions
  `movn`/`movz` (fit the `rd, rs, rt` R-type shape exactly, table-driven like
  `add`), and `clo`/`clz`/`seb`/`seh` (SPECIAL2/SPECIAL3 opcodes, hand-encoded
  below since they don't fit any existing `RForm`).
- Further MIPS32 additions (docs/spec/MIPS-COVERAGE-GAPS.md section 3.4/3.5):
  `sllv`/`srlv`/`srav` (`rd, rt, rs` -- same opcode-0 shape as `shift` but the
  shift amount is a register, table-driven via a new `.shiftv` `RForm`), and
  `mul` (`rd, rs, rt` -- SPECIAL2-opcoded like `clo`/`clz`, hand-encoded
  alongside them since `rTable` only handles opcode-0 forms); and `jr`/`jalr`
  (real MIPS32 register-indirect jump/call, opcode 0 funct 0x08/0x09,
  hand-encoded below since neither fits any existing `RForm` either --
  `jr $rs` is one-operand, `jalr $rd, $rs` is two-operand with `rd` first per
  real MIPS32 assembly syntax (opposite order from the `rs`-then-`rd` field
  layout); `jalr $rs` -- the one-operand sugar for `jalr $ra, $rs` -- is also
  supported); `madd`/`maddu`/`msub`/`msubu` (`rs, rt` -- same shape as `mult`/
  `div`, but SPECIAL2-opcoded like `mul`, so hand-encoded alongside it); and
  `mthi`/`mtlo` (`rs` -- opcode 0, funct 0x11/0x13, the write-direction
  counterparts to `mfhi`/`mflo`, same one-operand shape as `jr` so
  hand-encoded alongside it).
- MIPS32r2 rotate/bitfield additions (docs/spec/MIPS-COVERAGE-GAPS.md section
  3.4), all hand-encoded alongside `clo`/`clz`/`seb`/`seh` since none fits an
  existing `RForm`: `rotr $rd, $rt, $sa` / `rotrv $rd, $rt, $rs` (same
  `rd, rt, shamt`/`rd, rt, rs` shapes as `shift`/`shiftv`, but overload the
  normally-unused `rs`/`shamt` field to `0x01` to select rotate over `srl`/
  `srlv`); `wsbh $rd, $rt` (same BSHFL family as `seb`/`seh`, sub-field
  `0x02`); `ext $rt, $rs, pos, size` / `ins $rt, $rs, pos, size` (SPECIAL3
  opcode 0x1f, funct 0x00/0x04 -- see `Instruction.lean`'s `.ext`/`.ins`
  docstrings for the `pos`/`size` field-packing details).
- The coprocessor-0 trap/exception family (real MIPS32 ISA, added on top of
  the original v1 set -- see `docs/spec/INSTRUCTION-REF.md`): `teq`/`tne`/
  `tlt`/`tge`/`tltu`/`tgeu` (`rs, rt` operands, same shape as `mult`/`div`),
  and `break` (zero operands, like `syscall`; funct = 0x0d, word
  `0x0000000D`). Plus the immediate-operand trap family
  (docs/spec/MIPS-COVERAGE-GAPS.md section 3.8): `teqi`/`tnei`/`tgei`/
  `tgeiu`/`tlti`/`tltiu` (`rs, imm` operands; REGIMM opcode 0x01, same
  opcode as `bltz`/`bgez`/etc. below, distinguished by the `rt` field).
- The "branch likely" family (real MIPS32 ISA; deprecated in MIPS32,
  removed in Release 6 -- see `docs/spec/MIPS-COVERAGE-GAPS.md` section 3.3
  and `bTable`'s docstring below): `beql`/`bnel` (`rs, rt, target`,
  identical shape to `beq`/`bne`), `blezl`/`bgtzl`/`bltzl`/`bgezl`/
  `bltzall`/`bgezall` (`rs, target`, identical shape to `blez`/`bgtz`/
  `bltz`/`bgez`/`bltzal`/`bgezal`). Same table-driven `bTable` encoding as
  every other branch in this file -- the squash-on-not-taken semantics this
  family adds is pure `Step.lean` behavior, invisible to the assembler.
- `ll`/`sc` (real MIPS32 atomic synchronization primitives, added on top of
  the original v1 set -- see `docs/spec/INSTRUCTION-REF.md`): identical
  `rt, offset(rs)` shape and parsing to `lw`/`sw`, table-driven the same way
  (opcodes 0x30/0x38).
- `sync` (zero operands, like `break`; opcode 0, funct 0x0f) and `synci
  offset(rs)` (REGIMM opcode 0x01, `rt` field fixed 0x1f, same addressing
  syntax as `lw`/`sw` but with no destination/source register operand --
  table-driven via a new `IForm.memNoRt`) -- real MIPS32 memory-ordering
  barrier and instruction-cache-flush hint, completing the atomics story
  alongside `ll`/`sc` above (`docs/spec/MIPS-COVERAGE-GAPS.md` section 3.7;
  see `docs/spec/INSTRUCTION-REF.md`).
- `lwl`/`lwr`/`swl`/`swr` (real MIPS32 classic, pre-r6 unaligned load/store
  pair, added on top of the original v1 set -- see `docs/spec/
  MIPS-COVERAGE-GAPS.md` section 3.6 and `docs/spec/INSTRUCTION-REF.md`):
  identical `rt, offset(rs)` shape and parsing to `lw`/`sw`, table-driven the
  same way (opcodes 0x22/0x26/0x2a/0x2e).
- Coprocessor-1 (FPU) single-precision subset (docs/spec/INSTRUCTION-REF.md's
  floating-point section): `mtc1`/`mfc1`, `cfc1`/`ctc1`, `lwc1`/`swc1`,
  `add.s`/`sub.s`/`mul.s`/`div.s`, `mov.s`, `sqrt.s`/`abs.s`/`neg.s`,
  `round.w.s`/`trunc.w.s`/`ceil.w.s`/`floor.w.s`, `cvt.s.w`/`cvt.w.s`,
  `c.eq.s`/`c.lt.s`/`c.le.s`/`c.f.s`/`c.un.s`/`c.ueq.s`/`c.olt.s`/`c.ult.s`/
  `c.ole.s`/`c.ule.s`, `bc1t`/`bc1f`.
- Coprocessor-1 (FPU) double-precision subset (`docs/spec/MIPS-COVERAGE-GAPS.md`
  §3.9A; `docs/spec/INSTRUCTION-REF.md`'s double-precision section): `ldc1`/`sdc1`, `add.d`/`sub.d`/`mul.d`/`div.d`,
  `mov.d`, `sqrt.d`/`abs.d`/`neg.d`, `cvt.d.s`/`cvt.s.d`/`cvt.d.w`/`cvt.w.d`,
  `c.eq.d`/`c.lt.d`/`c.le.d`/`c.f.d`/`c.un.d`/`c.ueq.d`/`c.olt.d`/`c.ult.d`/
  `c.ole.d`/`c.ule.d`. `$fN` operands name the *low* register of the
  register pair the double value occupies (same `$fN` parsing as the
  single-precision instructions above, `parseFpRegister`); the assembler
  does not check/enforce that `N` is even.
- Coprocessor-0 (CP0) register move / execution control (real MIPS32 ISA,
  `docs/spec/MIPS-COVERAGE-GAPS.md` §3.10A; see `Instruction.lean`/
  `Step.lean`): `mfc0 $rt, $rd` / `mtc0 $rt, $rd` (`rd` is a CP0 register
  number, written `$12` as in standard MIPS assembly or as the bare number
  `12`; this model has no named CP0 register aliases), and `eret`/`wait`
  (zero operands, like `break`). `cfc1`/`ctc1` likewise take the FPU
  control register as `$31` (or the older `$f31` spelling).
- Pseudo-ops: `li`, `la` (label or `label±const` — see deviation note
  below), `move`, `nop`, expanded per `PseudoOps.txt` of the MARS 4.5 source (not vendored).
- Register names `$zero,$at,$v0,$v1,$a0..$a3,$t0..$t7,$s0..$s7,$t8,$t9,
  $k0,$k1,$gp,$sp,$fp,$s8,$ra` plus raw numeric `$0`..`$31` (canonical
  decimal only: `$08` and `$1_0` are errors), and FP register names
  `$f0`..`$f31` for the coprocessor-1 instructions.

## Range checks
| operand | accepted range |
|---|---|
| `addi`/`addiu`/`slti`/`sltiu`, trap immediates, memory offsets | −32768..32767 |
| `andi`/`ori`/`xori`/`lui` | 0..65535 |
| `li`, `.word` | −2^31..2^32−1 |
| `.half` | −32768..65535 |
| `.byte` | −128..255 |
| branch to a label | (target − (pc+4)) divisible by 4, −32768..32767 words |
| numeric branch operand (the word offset itself, MARS convention) | −32768..32767 |
| `j`/`jal` | word-aligned, same 256MB region as the delay slot |

## Layout
The `Program` is a sparse address → word map, so any number of disjoint
regions can be assembled. There are four segments, each with its own
location counter: `.text` (default `textBase`, 0x00400000), `.data`
(`dataBase`, 0x10010000, SPEC-NOTES §1), `.ktext` (`ktextBase`, 0x80000180
= the exception vector `Step.lean` dispatches to) and `.kdata` (`kdataBase`,
0x90000000). A segment directive with an address operand (`.data
0x10000000`, `.text 0x00400100`) moves that segment's location counter
there; without an operand the segment resumes where it left off. Execution
still starts at `textBase` (the hosted start state `Env.hostedStart`; `MipsRun --reset`
starts at the reset vector `0xBFC00000`, which `.ktext 0xBFC00000` can fill), exactly
as in MARS. Two items that would occupy the same bytes are an error, as is
running past address 2^32.

Alignment: `.word`/`.float` align the location counter to 4, `.half` to 2,
`.double` to 8; `.byte`/`.ascii`/`.asciiz`/`.space` need none. `.align n`
aligns to 2^n (n = 1..16); `.align 0` switches the automatic alignment of
the data directives off until the next segment directive (MARS/GNU as
behaviour). **A label is bound after alignment**: it names the address of
the next item, so `w: .word 77` after a `.byte` names the word itself, and
so does a label on its own line in front of it. (MARS 4.5 differs for the
own-line case only: it binds such a label to the unaligned address.)

Data in `.text`: data directives are accepted in `.text`/`.ktext` (as in
GNU as; MARS rejects them), and every instruction is word-aligned first, so
data can never misalign the code after it. Instructions in `.data`/`.kdata`
are rejected.

All data is big-endian (`.word 0x01020304` stores byte `01` first; a
`.double` stores its most-significant word first, the order `ldc1`/`sdc1`
use). `.float`/`.double` literals are converted with exact rational
arithmetic, correctly rounded to nearest-even (`ratToIeee`) -- no host
floating point is involved. String literals take the escapes listed at
`scanQuoted`; several comma-separated strings may follow one directive.

## Deviation from MARS `la`
MARS's `la` pseudo-op has many address-forms (`la $t,100($t2)`,
`la $t,label+100000($t2)`, a `COMPACT` single-instruction form when the
resolved address fits 16 bits, etc. — see `PseudoOps.txt` lines 249-258).
Per docs/DESIGN.md §4 ("`la` = `li` of a label address"), this assembler supports
exactly `la $rt, label` and `la $rt, label±const`. It always emits the
general two-instruction `lui $at,hi16 ; ori $rt,$at,lo16` expansion (the
same one MARS uses for non-compact `la`/large `li`), whatever the resolved
address -- pass 1 reserves exactly two words before label addresses are
known. Any other `la` form (register-relative, purely numeric) is a
`badOperand` error.

## Other documented differences from MARS / GNU as
- `li` of 0..65535 uses `ori` (MARS: `addiu` for 0..32767), and a value
  written as a 32-bit pattern `0xffff8000`..`0xffffffff` uses `lui`/`ori`
  (MARS folds it to the one-word `addiu` of the equivalent negative).
- `clo`/`clz` encode `rt = rd` (MIPS32 spec; MARS leaves `rt` 0).
- `b label` is GNU as's `beq $0,$0,label` (MARS: `bgez $0,label`); `abs`
  is GNU as's branch-over form (MARS uses `sra`/`xor`/`subu`).
- The compare-and-branch idioms always use the two-instruction `$at` form;
  GNU as's one-instruction special cases for a literal `$0` operand are not
  replicated (same semantics).
- GNU as defaults to `.set reorder` (it fills delay slots itself); this
  assembler always assembles what is written (`.set noreorder`) and rejects
  `.set reorder`.
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

/-- `$at` (register 1), the scratch register used by the `li`/`la` two-word
expansion, matching MARS's convention (`PseudoOps.txt`). -/
def atReg : Nat := 1

/-- `$zero`, used as the implicit source for `move`/`li`'s one-word forms. -/
def zeroReg : Nat := 0

-- ====================================================================
-- Tokenizing helpers
-- ====================================================================

def natToW32 (n : Nat) : W32 := BitVec.ofNat 32 n

private def trimStr (s : String) : String := s.trimAscii.toString

/-- `String.drop`/`.take`/`.dropEnd` return `String.Slice` in this Lean
version; these wrappers convert back to `String` for uniform downstream use. -/
private def dropS (s : String) (n : Nat) : String := (s.drop n).toString

private def trimChars (cs : List Char) : List Char :=
  ((cs.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- Quote-tracking state shared by every line-level scanner (comment
stripping, label splitting, operand splitting), so that `#`, `:` and `,`
inside a `"..."` string or a `'c'` character literal are never treated as
syntax. -/
private inductive QState
  | normal | str | strEsc | chr | chrEsc

private def QState.next (st : QState) (c : Char) : QState :=
  match st with
  | .normal => if c == '"' then .str else if c == '\'' then .chr else .normal
  | .str => if c == '\\' then .strEsc else if c == '"' then .normal else .str
  | .strEsc => .str
  | .chr => if c == '\\' then .chrEsc else if c == '\'' then .normal else .chr
  | .chrEsc => .chr

private def QState.isNormal : QState → Bool
  | .normal => true
  | _ => false

/-- Strip a `#` line comment, but not one occurring inside a `"..."` string
or `'c'` character literal (so `.asciiz "a # b"` and `li $t0, '#'` keep
their `#`). -/
private def stripComment (cs : List Char) : List Char := Id.run do
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
private def splitTop (cs : List Char) (sep : Char) : List (List Char) := Id.run do
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

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '.' || c == '$'
private def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.' || c == '$'

/-- A valid label/symbol name: `[A-Za-z_.$][A-Za-z0-9_.$]*`. -/
private def isIdent (cs : List Char) : Bool :=
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

private def parseLine (lineNo : Nat) (rawLine : String) : Except AsmError ParsedLine := do
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

-- ====================================================================
-- Numeric / character / string literals
-- ====================================================================

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Non-empty digit string in the given base (2/8/10/16); no separators
(`1_000` is rejected), no sign. -/
private def digitsToNat (base : Nat) (cs : List Char) : Option Nat :=
  if cs.isEmpty then none
  else
    cs.foldl
      (fun acc c => acc.bind fun a => (hexDigit? c).bind fun d =>
        if d < base then some (a * base + d) else none)
      (some 0)

/-- Unsigned integer literal with GNU-as radix rules: `0x…` hex, `0b…`
binary, a leading `0` followed by more digits is **octal** (`010` = 8, `08`
is an error), anything else decimal. -/
private def parseNatLit (cs : List Char) : Option Nat :=
  match cs with
  | '0' :: 'x' :: r => digitsToNat 16 r
  | '0' :: 'X' :: r => digitsToNat 16 r
  | '0' :: 'b' :: r => digitsToNat 2 r
  | '0' :: 'B' :: r => digitsToNat 2 r
  | '0' :: c :: r => digitsToNat 8 (c :: r)
  | _ => digitsToNat 10 cs

private def isOctDigit (c : Char) : Bool := '0' ≤ c && c ≤ '7'

private def utf8Bytes (c : Char) : List Nat :=
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
private def scanQuoted (q : Char) : Nat → List Char → List Nat → Except String (List Nat × List Char)
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
private def parseStringTok (tok : String) (line : Nat) : Except AsmError (List Nat) :=
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
private def parseAtomNat (cs : List Char) (line : Nat) : Except AsmError Nat :=
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
private def splitTerms (cs : List Char) : List (Bool × List Char) := Id.run do
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
private def parseExpr (tok : String) (line : Nat) : Except AsmError (Option String × Int) := do
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
private def parseImmediate (tok : String) (line : Nat) : Except AsmError Int := do
  let (sym, k) ← parseExpr tok line
  match sym with
  | none => pure k
  | some s => throw (.badImmediate s!"expected a numeric constant, got '{s}' in '{tok}'" line)

/-- Reject `v` outside `lo..hi` -- the assembler never truncates an
out-of-range immediate. -/
private def checkRange (what : String) (lo hi v : Int) (line : Nat) : Except AsmError Unit :=
  if lo ≤ v ∧ v ≤ hi then pure ()
  else throw (.badImmediate s!"{what} out of range ({lo}..{hi}): {v}" line)

-- ====================================================================
-- Registers
-- ====================================================================

private def regTable : List (String × Nat) :=
  [("zero", 0), ("at", 1), ("v0", 2), ("v1", 3),
   ("a0", 4), ("a1", 5), ("a2", 6), ("a3", 7),
   ("t0", 8), ("t1", 9), ("t2", 10), ("t3", 11), ("t4", 12), ("t5", 13), ("t6", 14), ("t7", 15),
   ("s0", 16), ("s1", 17), ("s2", 18), ("s3", 19), ("s4", 20), ("s5", 21), ("s6", 22), ("s7", 23),
   ("t8", 24), ("t9", 25),
   ("k0", 26), ("k1", 27),
   ("gp", 28), ("sp", 29), ("fp", 30), ("s8", 30), ("ra", 31)]

/-- Canonical decimal register number `0`..`31`: digits only, no leading
zero (`$08`), no separators (`$1_0`), no other radix. -/
private def parseRegNum (cs : List Char) : Option Nat :=
  if cs.isEmpty || !cs.all Char.isDigit || (cs.length > 1 && cs.head? == some '0') then none
  else
    match digitsToNat 10 cs with
    | some n => if n < 32 then some n else none
    | none => none

private def parseRegister (tok : String) (line : Nat) : Except AsmError Nat := do
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
private def fpRegTable : List (String × Nat) :=
  (List.range 32).map (fun i => (s!"f{i}", i))

/-- Parse an FP register operand. Unlike `parseRegister`, there is no raw
numeric fallback (`$5` is never an FP register) — FPU operands always use
the `$fN` spelling, matching real MIPS32 assembly syntax. -/
private def parseFpRegister (tok : String) (line : Nat) : Except AsmError Nat := do
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
private def parseCopRegister (what : String) (tok : String) (line : Nat) : Except AsmError Nat := do
  let body := if tok.startsWith "$" then dropS tok 1 else tok
  match parseRegNum body.toList with
  | some n => pure n
  | none => throw (.badRegister s!"expected a {what} register number 0-31 ('$N' or 'N'), got '{tok}'" line)

/-- Parse a `offset(reg)` or `(reg)` memory operand (whitespace allowed
around the parts: `4 ($sp)`). The offset must be a numeric constant in the
signed 16-bit range. -/
private def parseMemOperand (tok : String) (line : Nat) : Except AsmError (Int × Nat) := do
  match splitTop tok.toList '(' with
  | [immCs, restCs] =>
    let rest := trimChars restCs
    if rest.getLast? != some ')' then
      throw (.badOperand s!"missing closing ')' in operand '{tok}'" line)
    let regStr := String.ofList (trimChars rest.dropLast)
    let immStr := String.ofList (trimChars immCs)
    let imm ← if immStr.isEmpty then pure (0 : Int) else parseImmediate immStr line
    checkRange "memory offset" (-32768) 32767 imm line
    let reg ← parseRegister regStr line
    pure (imm, reg)
  | _ => throw (.badOperand s!"expected 'offset(register)' operand, got '{tok}'" line)

-- ====================================================================
-- Mnemonic classification
-- ====================================================================

private inductive RForm
  | arith3   -- rd, rs, rt
  | shift    -- rd, rt, shamt
  | shiftv   -- rd, rt, rs (variable shift; shamt field unused/0)
  | multdiv  -- rs, rt
  | hilo     -- rd

private inductive IForm
  | arith    -- rt, rs, imm
  | lui      -- rt, imm
  | mem      -- rt, offset(rs)
  | trapImm (rtField : Nat)  -- rs, imm (rt field fixed to the given REGIMM trap selector)
  | memNoRt (rtField : Nat)  -- offset(rs) only, no destination/source register (synci: rt field fixed 0x1f)

private inductive BForm
  | two          -- rs, rt, target
  | one          -- rs, target (rt field fixed 0, e.g. blez/bgtz)
  | regimm (rt : Nat)  -- rs, target (rt field fixed to the given REGIMM sub-opcode selector)

/-- Static table of R-type mnemonics: (name, funct, form). -/
private def rTable : List (String × Nat × RForm) :=
  [("add", 0x20, .arith3), ("addu", 0x21, .arith3), ("sub", 0x22, .arith3), ("subu", 0x23, .arith3),
   ("and", 0x24, .arith3), ("or", 0x25, .arith3), ("xor", 0x26, .arith3), ("nor", 0x27, .arith3),
   ("slt", 0x2a, .arith3), ("sltu", 0x2b, .arith3),
   ("movn", 0x0b, .arith3), ("movz", 0x0a, .arith3),  -- MIPS32r2; same opcode-0 `rd, rs, rt` shape as `add`
   ("sll", 0x00, .shift), ("srl", 0x02, .shift), ("sra", 0x03, .shift),
   -- Variable shifts (MIPS32; docs/spec/MIPS-COVERAGE-GAPS.md section 3.4):
   -- same opcode-0 `rd, rt, rs` shape as `shift`, but the third operand is a
   -- register (the shift amount), not an immediate shamt.
   ("sllv", 0x04, .shiftv), ("srlv", 0x06, .shiftv), ("srav", 0x07, .shiftv),
   ("mult", 0x18, .multdiv), ("multu", 0x19, .multdiv), ("div", 0x1a, .multdiv), ("divu", 0x1b, .multdiv),
   ("mfhi", 0x10, .hilo), ("mflo", 0x12, .hilo),
   -- Trap-on-condition family (same `rs, rt` shape as `mult`/`div`): real
   -- MIPS32 SPECIAL-opcode funct values (see `Instruction.lean`/
   -- `docs/spec/INSTRUCTION-REF.md`), not MARS-derived.
   ("teq", 0x34, .multdiv), ("tne", 0x36, .multdiv), ("tlt", 0x32, .multdiv),
   ("tge", 0x30, .multdiv), ("tltu", 0x33, .multdiv), ("tgeu", 0x31, .multdiv)]

/-- Static table of I-type mnemonics: (name, opcode, form). -/
private def iTable : List (String × Nat × IForm) :=
  [("addi", 0x08, .arith), ("addiu", 0x09, .arith), ("slti", 0x0a, .arith), ("sltiu", 0x0b, .arith),
   ("andi", 0x0c, .arith), ("ori", 0x0d, .arith), ("xori", 0x0e, .arith),
   ("lui", 0x0f, .lui),
   ("lw", 0x23, .mem), ("sw", 0x2b, .mem), ("lb", 0x20, .mem), ("lbu", 0x24, .mem),
   ("lh", 0x21, .mem), ("lhu", 0x25, .mem), ("sh", 0x29, .mem), ("sb", 0x28, .mem),
   -- `ll`/`sc`: real MIPS32 atomic synchronization primitives (opcodes
   -- 0x30/0x38; MD00086 Rev 2.50 §3.2), same `rt, offset(rs)` shape as
   -- `lw`/`sw` (see `Instruction.lean`/`docs/spec/INSTRUCTION-REF.md`).
   ("ll", 0x30, .mem), ("sc", 0x38, .mem),
   -- Trap-immediate family (REGIMM, real MIPS32 ISA; opcode 0x01, same
   -- opcode as `bltz`/`bgez`/etc. in `bTable`, distinguished by the `rt`
   -- field -- see `Instruction.lean`/`docs/spec/MIPS-COVERAGE-GAPS.md` §3.8).
   -- Operand shape is `rs, imm` (a plain immediate, not a branch target).
   ("teqi", 0x01, .trapImm 0x0c), ("tnei", 0x01, .trapImm 0x0e),
   ("tgei", 0x01, .trapImm 0x08), ("tgeiu", 0x01, .trapImm 0x09),
   ("tlti", 0x01, .trapImm 0x0a), ("tltiu", 0x01, .trapImm 0x0b),
   -- `lwl`/`lwr`/`swl`/`swr`: real MIPS32 classic (pre-r6) unaligned
   -- load/store pair (opcodes 0x22/0x26/0x2a/0x2e; MD00086 Rev 2.50
   -- §3.2, Table 3-4), same `rt, offset(rs)` shape as `lw`/`sw` (see
   -- `Instruction.lean`/`docs/spec/INSTRUCTION-REF.md`).
   ("lwl", 0x22, .mem), ("lwr", 0x26, .mem), ("swl", 0x2a, .mem), ("swr", 0x2e, .mem),
   -- `synci`: real MIPS32 instruction-cache-flush hint (REGIMM opcode
   -- 0x01, `rt` field fixed 0x1f; MIPS32r2, `docs/spec/MIPS-COVERAGE-GAPS.md`
   -- section 3.7), `offset(rs)` only -- no destination/source register,
   -- unlike every other `.mem`-shaped mnemonic above.
   ("synci", 0x01, .memNoRt 0x1f)]

/-- Static table of J-type mnemonics: (name, opcode). -/
private def jTable : List (String × Nat) := [("j", 0x02), ("jal", 0x03)]

/-- Static table of branch mnemonics: (name, opcode, form). The REGIMM
zero-comparison branches (`bltz`/`bgez`/`bltzal`/`bgezal`) all share opcode
0x01; the `rt` field (carried in `.regimm`, not a separate opcode) is what
selects which one, per MD00086 Rev 2.50 §3.2, Table 3-2 (see
`Instruction.lean`'s decode/encode and `docs/spec/INSTRUCTION-REF.md`). -/
private def bTable : List (String × Nat × BForm) :=
  [("beq", 0x04, .two), ("bne", 0x05, .two), ("blez", 0x06, .one), ("bgtz", 0x07, .one),
   ("bltz", 0x01, .regimm 0x00), ("bgez", 0x01, .regimm 0x01),
   ("bltzal", 0x01, .regimm 0x10), ("bgezal", 0x01, .regimm 0x11),
   -- "Branch likely" family (real MIPS32; deprecated in MIPS32, removed in
   -- Release 6 -- MD00086 Rev 2.50 §3.2, Table 3-10, p. 28; see
   -- docs/spec/MIPS-COVERAGE-GAPS.md §3.3 and `Instruction.lean`'s
   -- `.beql`..`.bgezall` docstrings). Identical field shapes/operand syntax
   -- to the non-likely branches directly above, so this table-driven
   -- `encodeBForm` needs no changes at all -- the squash-on-not-taken
   -- semantics is pure `Step.lean` behavior, invisible to the assembler.
   ("beql", 0x14, .two), ("bnel", 0x15, .two), ("blezl", 0x16, .one), ("bgtzl", 0x17, .one),
   ("bltzl", 0x01, .regimm 0x02), ("bgezl", 0x01, .regimm 0x03),
   ("bltzall", 0x01, .regimm 0x12), ("bgezall", 0x01, .regimm 0x13)]

/-- Coprocessor-1 (FPU) mnemonic operand shapes. The static parameters
(`fmt`/`opcode`/`funct`/`tf`) needed to build each instruction's word are
carried directly in the constructor — see `cop1Table` and
`docs/spec/INSTRUCTION-REF.md`'s floating-point section for the exact
encodings (same values as `Instruction.lean`'s `encode`). -/
private inductive Cop1Form
  | moveGpFp (fmt : Nat)        -- mtc1/mfc1/mthc1/mfhc1/ctc1/cfc1: $rt, $fs
  | mem (opcode : Nat)          -- lwc1/swc1/ldc1/sdc1: $ft, offset($rs)
  | arith3 (fmt funct : Nat)    -- add/sub/mul/div: $fd, $fs, $ft
  | unary (fmt funct : Nat)     -- mov/sqrt/abs/neg/recip/rsqrt/cvt/round…: $fd, $fs
  | compare (fmt cond : Nat)    -- c.cond.fmt: [cc,] $fs, $ft
  | branch (nd tf : Nat)        -- bc1f/bc1t/bc1fl/bc1tl: [cc,] target
  | movcf (fmt tf : Nat)        -- movf.fmt/movt.fmt: $fd, $fs[, cc]
  | movci (tf : Nat)            -- movf/movt (GPR): $rd, $rs[, cc]
  | movGpr (fmt funct : Nat)    -- movn.fmt/movz.fmt: $fd, $fs, $rt
  | madd (funct : Nat)          -- madd/msub/nmadd/nmsub.fmt: $fd, $fr, $fs, $ft
  | indexedLoad (funct : Nat)   -- lwxc1/ldxc1: $fd, $index($base)
  | indexedStore (funct : Nat)  -- swxc1/sdxc1: $fs, $index($base)
  | prefx                       -- prefx hint, $index($base)

/-- The sixteen `C.cond.fmt` predicate names, in `cond` order (MD00086
Vol II-A Rev 6.06, C.cond.fmt, Tables 3.1 / 3.2, p.111-112). -/
def fpCondNames : List String :=
  ["f", "un", "eq", "ueq", "olt", "ult", "ole", "ule",
   "sf", "ngle", "seq", "ngl", "lt", "nge", "le", "ngt"]

/-- Static table of coprocessor-1 (FPU) mnemonics: (name, form). `fmt` is
`S` = 0x10, `D` = 0x11, `W` = 0x14; a conversion's `fmt` names its *source*
format. -/
private def cop1Table : List (String × Cop1Form) :=
  [("mtc1", .moveGpFp 4), ("mfc1", .moveGpFp 0), ("mthc1", .moveGpFp 7), ("mfhc1", .moveGpFp 3),
   ("cfc1", .moveGpFp 2), ("ctc1", .moveGpFp 6),
   ("lwc1", .mem 0x31), ("swc1", .mem 0x39), ("ldc1", .mem 0x35), ("sdc1", .mem 0x3d),
   ("cvt.s.w", .unary 0x14 0x20), ("cvt.d.w", .unary 0x14 0x21),
   ("cvt.d.s", .unary 0x10 0x21), ("cvt.s.d", .unary 0x11 0x20),
   ("bc1f", .branch 0 0), ("bc1t", .branch 0 1), ("bc1fl", .branch 1 0), ("bc1tl", .branch 1 1),
   ("movf", .movci 0), ("movt", .movci 1),
   ("lwxc1", .indexedLoad 0x00), ("ldxc1", .indexedLoad 0x01),
   ("swxc1", .indexedStore 0x08), ("sdxc1", .indexedStore 0x09), ("prefx", .prefx),
   ("madd.s", .madd 0x20), ("madd.d", .madd 0x21), ("msub.s", .madd 0x28), ("msub.d", .madd 0x29),
   ("nmadd.s", .madd 0x30), ("nmadd.d", .madd 0x31), ("nmsub.s", .madd 0x38),
   ("nmsub.d", .madd 0x39)] ++
  ([("s", 0x10), ("d", 0x11)].flatMap fun (sfx, fmt) =>
    [("add." ++ sfx, Cop1Form.arith3 fmt 0x00), ("sub." ++ sfx, .arith3 fmt 0x01),
     ("mul." ++ sfx, .arith3 fmt 0x02), ("div." ++ sfx, .arith3 fmt 0x03),
     ("sqrt." ++ sfx, .unary fmt 0x04), ("abs." ++ sfx, .unary fmt 0x05),
     ("mov." ++ sfx, .unary fmt 0x06), ("neg." ++ sfx, .unary fmt 0x07),
     ("round.w." ++ sfx, .unary fmt 0x0c), ("trunc.w." ++ sfx, .unary fmt 0x0d),
     ("ceil.w." ++ sfx, .unary fmt 0x0e), ("floor.w." ++ sfx, .unary fmt 0x0f),
     ("recip." ++ sfx, .unary fmt 0x15), ("rsqrt." ++ sfx, .unary fmt 0x16),
     ("cvt.w." ++ sfx, .unary fmt 0x24),
     ("movf." ++ sfx, .movcf fmt 0), ("movt." ++ sfx, .movcf fmt 1),
     ("movz." ++ sfx, .movGpr fmt 0x12), ("movn." ++ sfx, .movGpr fmt 0x13)] ++
    fpCondNames.zipIdx.map fun (c, i) => ("c." ++ c ++ "." ++ sfx, Cop1Form.compare fmt i))

/-- The mnemonics of `cop1Table`, in table order (exposed for the tests in
`Semantics/Tests/AsmTests.lean`; the table itself stays private). -/
def cop1Mnemonics : List String := cop1Table.map (·.1)

-- `break`/`sync` are real instructions, not pseudo-ops, but are
-- zero-operand (like `syscall`) rather than fitting any `RForm` with
-- register operands, so they are special-cased alongside `syscall` the
-- same way throughout this file (`isKnownMnemonic`, `wordsForMnemonic`,
-- `encodeInstruction`). `sync` (opcode 0, funct 0x0f; real MIPS32 memory-
-- ordering barrier, `docs/spec/MIPS-COVERAGE-GAPS.md` section 3.7) takes an
-- optional `stype` operand (bits 10..6, 0..31; `sync` alone is `stype = 0`),
-- carried by `Instruction.sync` -- see `Instruction.lean`'s `.sync` docstring.
private def pseudoSet : List String :=
  ["li", "la", "move", "nop", "syscall", "break", "sync", "pref", "di", "ei",
   -- assembler idioms (see `expandIdiom` / `encodeInstruction`)
   "b", "bal", "beqz", "bnez", "neg", "negu", "not", "abs",
   "blt", "bge", "bgt", "ble", "bltu", "bgeu", "bgtu", "bleu",
   "ssnop", "ehb", "pause", "nal", "jr.hb", "jalr.hb"]
/-- Data-emitting directives (laid out by `directiveLayout`). Segment
directives, `.align` and the no-op `.globl`/`.global`/`.extern` are handled
directly in `layoutLine`. -/
private def directiveSet : List String :=
  [".word", ".half", ".byte", ".ascii", ".asciiz", ".asciz", ".string", ".space", ".float", ".double"]

/-- SPECIAL2/SPECIAL3 mnemonics with an opcode-bearing R-type-like shape that
doesn't fit any existing `RForm` (nonzero opcode and/or an operand count
that doesn't match `arith3`/`shift`/`shiftv`/`multdiv`/`hilo`); hand-encoded
directly in `encodeInstruction` below instead of via `rTable`. `mul` has the
same `rd, rs, rt` operand shape as `arith3`, but is SPECIAL2-opcoded (0x1c)
like `clo`/`clz` rather than plain SPECIAL (opcode 0), so it is hand-encoded
here too rather than via `rTable`. -/
private def bshflMnemonics : List String := ["clo", "clz", "seb", "seh", "mul"]

/-- SPECIAL2 multiply-accumulate (MIPS32): `madd`/`maddu`/`msub`/`msubu` have
the same `rs, rt` operand shape as `mult`/`multu`/`div`/`divu` (`RForm.
multdiv`), but unlike those, are SPECIAL2-opcoded (0x1c) like `mul`/`clo`/
`clz` above, so they can't go through the opcode-0 `rTable` either; hand-
encoded directly in `encodeInstruction` below (docs/spec/MIPS-COVERAGE-GAPS.md
§3.5). -/
private def multAccumMnemonics : List String := ["madd", "maddu", "msub", "msubu"]

/-- Real MIPS32 register-indirect jump/call (opcode 0, funct 0x08/0x09):
`jr $rs` (one operand) and `jalr $rd, $rs` (two operands, also accepting the
`jalr $rs` one-operand sugar for `jalr $ra, $rs`) don't fit any existing
`RForm`'s fixed operand count, so they're hand-encoded directly in
`encodeInstruction` below, the same way `bshflMnemonics` are. -/
private def jrJalrMnemonics : List String := ["jr", "jalr"]

/-- Write-direction HI/LO register moves (real MIPS32 `mthi`/`mtlo`, opcode
0, funct 0x11/0x13): single-operand `rs` only, the same shape as `jr`, so
like `jrJalrMnemonics` they don't fit any existing `RForm`'s fixed operand
count and are hand-encoded directly in `encodeInstruction` below. The
write-direction counterparts to `mfhi`/`mflo` (`RForm.hilo`), needed for OS
context switching and setjmp/longjmp to save/restore `hi`/`lo` (see
docs/spec/MIPS-COVERAGE-GAPS.md §3.5). -/
private def hiLoMoveMnemonics : List String := ["mthi", "mtlo"]
/-- MIPS32r2 rotate/bitfield mnemonics (docs/spec/MIPS-COVERAGE-GAPS.md
section 3.4): `rotr`/`rotrv` overload `srl`/`srlv`'s opcode/funct via the
`rs`/`shamt` field (so they don't fit `rTable`'s `.shift`/`.shiftv` forms,
which always encode `rs`/`shamt` as 0); `wsbh` is another BSHFL sub-op like
`seb`/`seh`; `ext`/`ins` are SPECIAL3-opcoded with a four-operand
`rt, rs, pos, size` shape no existing `RForm` has. All hand-encoded in
`encodeInstruction` below, the same way `bshflMnemonics` are. -/
private def bitfieldMnemonics : List String := ["rotr", "rotrv", "wsbh", "ext", "ins"]
/-- Coprocessor-0 (CP0) register move / execution-control mnemonics
(docs/spec/MIPS-COVERAGE-GAPS.md §3.10A). `mfc0`/`mtc0` share `mfc1`/
`mtc1`'s move-shape but address a plain numeric CP0 register instead of an
`$fN` FP register, and `eret`/`wait` are zero-operand like `break`, so none
of the four fit `Cop1Form`/`RForm`/the existing zero-operand special cases
exactly -- hand-encoded directly in `encodeInstruction` below, the same way
`bshflMnemonics`/`jrJalrMnemonics` are. -/
private def cop0Mnemonics : List String := ["mfc0", "mtc0", "eret", "wait", "rdpgpr", "wrpgpr"]
/-- `rdhwr $rt, $rd` (MIPS32 Release 2, SPECIAL3 funct 0x3b; MD00086 Vol II-A Rev 6.06, RDHWR,
p.332): read hardware register `rd` (0-31, written `$29` or `29`) into GPR `rt`. The Release 6
`sel` operand does not exist before Release 6 (bits 10..6 are zero), so exactly two operands. -/
private def hwRegMnemonics : List String := ["rdhwr"]

private def isKnownMnemonic (m : String) : Bool :=
  rTable.any (·.1 == m) ∨ iTable.any (·.1 == m) ∨ jTable.any (·.1 == m) ∨
    bTable.any (·.1 == m) ∨ cop1Table.any (·.1 == m) ∨ pseudoSet.contains m ∨
    bshflMnemonics.contains m ∨ jrJalrMnemonics.contains m ∨
    multAccumMnemonics.contains m ∨ hiLoMoveMnemonics.contains m ∨
    bitfieldMnemonics.contains m ∨ cop0Mnemonics.contains m ∨ hwRegMnemonics.contains m

/-- Number of 32-bit words a `li $rt, v` expansion emits, per
`PseudoOps.txt` lines 245-247: sign-extendable-16-bit values use a single
`addiu`; zero-extendable-16-bit (unsigned) values use a single `ori`;
everything else needs the `lui`/`ori` two-word split. -/
private def liWordCount (v : Int) : Nat :=
  if (-32768 : Int) ≤ v ∧ v ≤ -1 then 1
  else if (0 : Int) ≤ v ∧ v ≤ 65535 then 1
  else 2


-- ====================================================================
-- Program-building helpers (byte/half-word packing, big-endian)
-- ====================================================================

/-- Round `a` up to the next multiple of `n` (`n > 0`). -/
private def alignUpNat (a n : Nat) : Nat := ((a + n - 1) / n) * n

/-- Write a single byte into `prog` at `addr`, merging it into the
big-endian-packed 4-byte-aligned word that contains it (other bytes of that
word are left untouched, defaulting to 0 if the word doesn't exist yet). -/
private def putByte (prog : Program) (addr : W32) (b : Nat) : Program :=
  let wordAddr := natToW32 ((addr.toNat / 4) * 4)
  let byteIdx := addr.toNat % 4          -- 0 = most-significant byte (big-endian)
  let shift := (3 - byteIdx) * 8
  let existing := prog.getD wordAddr 0
  let mask : W32 := natToW32 (0xff <<< shift)
  let cleared := existing &&& (natToW32 0xffffffff ^^^ mask)
  let inserted := cleared ||| (natToW32 (b % 256) <<< shift)
  prog.insert wordAddr inserted

private def putWord (prog : Program) (addr : W32) (w : W32) : Program :=
  prog.insert addr w

/-- Write `bytes` at consecutive addresses starting at `addr`. -/
private def putBytes (prog : Program) (addr : W32) (bytes : List Nat) : Program :=
  (bytes.foldl (fun (p, a) b => (putByte p a b, a + 1#32)) (prog, addr)).1

/-- The `n` big-endian bytes of `v` (most-significant first), `v` taken
modulo `256^n`. Every multi-byte datum (`.half`/`.word`/`.float`/`.double`)
goes through this, so data is laid out big-endian whether or not its address
is aligned (`.align 0`). -/
private def beBytes (n : Nat) (v : Nat) : List Nat :=
  (List.range n).map (fun i => (v / 256 ^ (n - 1 - i)) % 256)

-- ====================================================================
-- `.float` / `.double`: exact decimal → IEEE-754 conversion
-- ====================================================================

/-- Correctly rounded (round-to-nearest, ties-to-even) IEEE-754 encoding of
the exact rational `num/den` (`den > 0`), computed in exact `Nat`/`Int`
arithmetic -- no host floating point is involved. `p` is the precision in
bits (24 single / 53 double), `ebits` the exponent-field width (8 / 11).
Handles subnormals; values that round beyond the largest finite number
become ±infinity (as in IEEE-754 and Java/GNU as). -/
private def ratToIeee (p ebits : Nat) (neg : Bool) (num den : Nat) : Nat :=
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
private def parseFloatLit (p ebits : Nat) (tok : String) (line : Nat) : Except AsmError Nat := do
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

-- ====================================================================
-- Idiom expansion (pure text → text, shared by both passes)
-- ====================================================================

private def trapRegMnemonics : List String := ["teq", "tne", "tlt", "tge", "tltu", "tgeu"]

/-- Parse an optional software `code`/`stype`/`sel` operand in `0..maxCode`. -/
private def parseCode (name what : String) (maxCode : Int) (tok : String) (line : Nat) :
    Except AsmError Nat := do
  let c ← parseImmediate tok line
  checkRange s!"{name} {what}" 0 maxCode c line
  pure c.toNat

/-- The idioms whose expansion goes through `$at` (rejected under
`.set noat`). -/
private def atIdioms : List String :=
  ["blt", "bge", "bgt", "ble", "bltu", "bgeu", "bgtu", "bleu"]

/-- Rewrite one source statement into the list of table-level instructions
it stands for. Anything that is not an idiom is returned unchanged. The
result depends only on the text (never on label addresses), so pass 1 can
use it to size the statement.

Compare-and-branch idioms always use the general two-instruction form
`slt/sltu $at, …` + `bne/beq $at, $0, target` (GNU as's and MARS's general
expansion; GNU as's shorter special cases for a literal `$0` operand are
not replicated -- the result is semantically identical). `abs` is GNU as's
`bgez rs, 1f ; move rd, rs ; sub rd, $0, rs ; 1:` (the `move` sits in the
`bgez` delay slot; `nop` instead when `rd = rs`). -/
private def expandIdiom (name : String) (ops : List String) (line : Nat) :
    Except AsmError (List (String × List String)) := do
  let cmpBranch (setOp brOp : String) (swap : Bool) : Except AsmError (List (String × List String)) :=
    match ops with
    | [rs, rt, l] =>
      pure [(setOp, if swap then ["$at", rt, rs] else ["$at", rs, rt]), (brOp, ["$at", "$0", l])]
    | _ => throw (.badOperand s!"{name} expects 'rs, rt, target'" line)
  match name with
  | "b" =>
    match ops with
    | [l] => pure [("beq", ["$0", "$0", l])]
    | _ => throw (.badOperand "b expects a single target operand" line)
  | "bal" =>
    match ops with
    | [l] => pure [("bgezal", ["$0", l])]
    | _ => throw (.badOperand "bal expects a single target operand" line)
  | "beqz" =>
    match ops with
    | [rs, l] => pure [("beq", [rs, "$0", l])]
    | _ => throw (.badOperand "beqz expects 'rs, target'" line)
  | "bnez" =>
    match ops with
    | [rs, l] => pure [("bne", [rs, "$0", l])]
    | _ => throw (.badOperand "bnez expects 'rs, target'" line)
  | "neg" =>
    match ops with
    | [rd, rs] => pure [("sub", [rd, "$0", rs])]
    | [rd] => pure [("sub", [rd, "$0", rd])]
    | _ => throw (.badOperand "neg expects 'rd, rs'" line)
  | "negu" =>
    match ops with
    | [rd, rs] => pure [("subu", [rd, "$0", rs])]
    | [rd] => pure [("subu", [rd, "$0", rd])]
    | _ => throw (.badOperand "negu expects 'rd, rs'" line)
  | "not" =>
    match ops with
    | [rd, rs] => pure [("nor", [rd, rs, "$0"])]
    | [rd] => pure [("nor", [rd, rd, "$0"])]
    | _ => throw (.badOperand "not expects 'rd, rs'" line)
  | "abs" =>
    let build (rdT rsT : String) : Except AsmError (List (String × List String)) := do
      let rd ← parseRegister rdT line
      let rs ← parseRegister rsT line
      pure [("bgez", [rsT, "2"]),
            (if rd == rs then ("nop", []) else ("move", [rdT, rsT])),
            ("sub", [rdT, "$0", rsT])]
    match ops with
    | [rd, rs] => build rd rs
    | [rd] => build rd rd
    | _ => throw (.badOperand "abs expects 'rd, rs'" line)
  | "blt" => cmpBranch "slt" "bne" false
  | "bge" => cmpBranch "slt" "beq" false
  | "bgt" => cmpBranch "slt" "bne" true
  | "ble" => cmpBranch "slt" "beq" true
  | "bltu" => cmpBranch "sltu" "bne" false
  | "bgeu" => cmpBranch "sltu" "beq" false
  | "bgtu" => cmpBranch "sltu" "bne" true
  | "bleu" => cmpBranch "sltu" "beq" true
  | "ssnop" =>
    match ops with
    | [] => pure [("sll", ["$0", "$0", "1"])]
    | _ => throw (.badOperand "ssnop takes no operands" line)
  | "ehb" =>
    match ops with
    | [] => pure [("sll", ["$0", "$0", "3"])]
    | _ => throw (.badOperand "ehb takes no operands" line)
  -- `pause` = `sll $0,$0,5` (MD00086 Vol II-A Rev 6.06, PAUSE, p.317).
  | "pause" =>
    match ops with
    | [] => pure [("sll", ["$0", "$0", "5"])]
    | _ => throw (.badOperand "pause takes no operands" line)
  -- `nal` = `bltzal $0, 0`: REGIMM, rs = 0, rt = 10000, offset ignored
  -- (written as 0) (MD00086 Vol II-A Rev 6.06, NAL, p.306).
  | "nal" =>
    match ops with
    | [] => pure [("bltzal", ["$0", "0"])]
    | _ => throw (.badOperand "nal takes no operands" line)
  | _ => pure [(name, ops)]

-- ====================================================================
-- Pass 1: layout (addresses + labels), pass-1 word/byte counts only
-- ====================================================================

/-- The four assembly segments. Each has its own location counter; a
segment directive without an operand resumes where that segment left off. -/
private inductive Seg
  | text | data | ktext | kdata

private def Seg.isText : Seg → Bool
  | .text => true
  | .ktext => true
  | _ => false

/-- A line with real content (label-only lines are folded into the label
table and otherwise dropped). `size` is the number of bytes the item
occupies (used for overlap detection). -/
private structure RawItem where
  lineNo : Nat
  addr : W32
  size : Nat
  mnemonic : String
  operands : List String

/-- Layout state. Location counters are `Nat`s so that running past
`2^32` is detected instead of wrapping. `pending` holds labels seen but
not yet bound: a label binds to the address of the *next item after
alignment* (B2), not to the raw location counter at the label. -/
private structure LState where
  seg : Seg
  textAddr : Nat
  dataAddr : Nat
  ktextAddr : Nat
  kdataAddr : Nat
  autoAlign : Bool
  /-- `.set noat` is in effect: idioms that need `$at` are rejected. -/
  noat : Bool := false
  pending : List String
  labels : Std.HashMap String W32
  items : Array RawItem

private def LState.curAddr (s : LState) : Nat :=
  match s.seg with
  | .text => s.textAddr
  | .data => s.dataAddr
  | .ktext => s.ktextAddr
  | .kdata => s.kdataAddr

private def LState.setAddr (s : LState) (a : Nat) : LState :=
  match s.seg with
  | .text => { s with textAddr := a }
  | .data => { s with dataAddr := a }
  | .ktext => { s with ktextAddr := a }
  | .kdata => { s with kdataAddr := a }

/-- Bind every pending label to `addr`. -/
private def LState.bindPending (s : LState) (addr : Nat) (line : Nat) : Except AsmError LState :=
  if s.pending.isEmpty then pure s
  else if addr ≥ 4294967296 then
    throw (.badDirective "label address is beyond the 32-bit address space" line)
  else
    pure { s with
      labels := s.pending.foldl (fun m l => m.insert l (natToW32 addr)) s.labels
      pending := [] }

private def stringDirectives : List String := [".ascii", ".asciiz", ".asciz", ".string"]

/-- Alignment and byte count of a data directive (the alignment is applied
to the location counter before the item -- and before binding its labels --
unless `.align 0` switched automatic alignment off). -/
private def directiveLayout (mnemonic : String) (operands : List String) (lineNo : Nat) :
    Except AsmError (Nat × Nat) := do -- (alignment, byteCount)
  if operands.isEmpty then
    throw (.badOperand s!"{mnemonic} needs at least one operand" lineNo)
  match mnemonic with
  | ".word" => pure (4, 4 * operands.length)
  | ".half" => pure (2, 2 * operands.length)
  | ".byte" => pure (1, operands.length)
  | ".float" => pure (4, 4 * operands.length)
  | ".double" => pure (8, 8 * operands.length)
  | ".space" =>
    match operands with
    | [tok] => do
        let n ← parseImmediate tok lineNo
        if n < 0 then throw (.badImmediate s!".space requires a non-negative count" lineNo)
        pure (1, n.toNat)
    | _ => throw (.badOperand s!".space expects exactly one operand" lineNo)
  | _ =>
    if stringDirectives.contains mnemonic then do
      let nul := if mnemonic == ".ascii" then 0 else 1
      let mut total := 0
      for tok in operands do
        let bytes ← parseStringTok tok lineNo
        total := total + bytes.length + nul
      pure (1, total)
    else throw (.badDirective s!"unknown directive '{mnemonic}'" lineNo)

/-- Number of 32-bit words one table-level instruction emits, without
needing label resolution: `li`'s numeric literal determines its size
directly; `la` is always the two-word `lui`/`ori` form. -/
private def wordsForSimple (mnemonic : String) (operands : List String) (lineNo : Nat) :
    Except AsmError Nat :=
  match mnemonic with
  | "li" =>
    match operands with
    | [_, valTok] => do
        let v ← parseImmediate valTok lineNo
        checkRange "li value" (-2147483648) 4294967295 v lineNo
        pure (liWordCount v)
    | _ => throw (.badOperand s!"li expects 'li $reg, imm'" lineNo)
  | "la" =>
    match operands with
    | [_, lbl] => do
        let (sym, _) ← parseExpr lbl lineNo
        if sym.isNone then
          throw (.badOperand s!"la requires a label operand (use li for numeric constants): '{lbl}'" lineNo)
        pure 2
    | _ => throw (.badOperand s!"la expects 'la $reg, label'" lineNo)
  | _ => pure 1

/-- Place an item of `bytes` bytes at the current location rounded up to
`align`, binding the pending labels to that aligned address. -/
private def LState.place (s : LState) (pl : ParsedLine) (m : String) (align bytes : Nat) :
    Except AsmError LState := do
  let aligned := alignUpNat s.curAddr align
  if aligned + bytes > 4294967296 then
    throw (.badDirective s!"'{m}' runs past the end of the 32-bit address space" pl.lineNo)
  let s ← s.bindPending aligned pl.lineNo
  let item : RawItem :=
    { lineNo := pl.lineNo, addr := natToW32 aligned, size := bytes, mnemonic := m, operands := pl.operands }
  pure { (s.setAddr (aligned + bytes)) with items := s.items.push item }

private def layoutLine (s : LState) (pl : ParsedLine) : Except AsmError LState := do
  let mut st := s
  for lbl in pl.labels do
    if st.labels.contains lbl || st.pending.contains lbl then
      throw (.duplicateLabel s!"label '{lbl}' already defined" pl.lineNo)
    st := { st with pending := lbl :: st.pending }
  let s := st
  match pl.mnemonic with
  | none => pure s
  | some m =>
    let segOf : Option Seg :=
      match m with
      | ".text" => some .text
      | ".data" => some .data
      | ".ktext" => some .ktext
      | ".kdata" => some .kdata
      | _ => none
    match segOf with
    | some seg =>
      -- A label still pending at a segment switch names the end of the
      -- segment being left.
      let s ← s.bindPending s.curAddr pl.lineNo
      let s := { s with seg := seg, autoAlign := true }
      match pl.operands with
      | [] => pure s
      | [tok] => do
          let a ← parseImmediate tok pl.lineNo
          checkRange s!"{m} address" 0 4294967295 a pl.lineNo
          pure (s.setAddr a.toNat)
      | _ => throw (.badOperand s!"{m} takes at most one address operand" pl.lineNo)
    | none =>
    if m == ".set" then
      -- `.set noreorder` is what this assembler always does; `.set noat` /
      -- `.set at` only switch the `$at` idioms off / on. `.set reorder` would
      -- change the meaning of the program (the assembler would have to fill
      -- delay slots) and is rejected, as is any other option.
      match pl.operands with
      | ["noreorder"] => pure s
      | ["noat"] => pure { s with noat := true }
      | ["at"] => pure { s with noat := false }
      | ["reorder"] =>
        throw (.badDirective
          ".set reorder is not supported: this assembler never fills delay slots (it always behaves as .set noreorder)"
          pl.lineNo)
      | _ => throw (.badDirective s!".set: unsupported option(s) {pl.operands}" pl.lineNo)
    else if m == ".globl" || m == ".global" || m == ".extern" then
      -- Accepted for source compatibility; this single-file assembler has
      -- no symbol visibility, so they are no-ops (labels stay pending).
      if pl.operands.isEmpty then throw (.badOperand s!"{m} expects a symbol name" pl.lineNo)
      else pure s
    else if m == ".align" then
      match pl.operands with
      | [tok] => do
          let n ← parseImmediate tok pl.lineNo
          checkRange ".align exponent" 0 16 n pl.lineNo
          if n == 0 then
            -- MARS/GNU as: `.align 0` turns off the automatic alignment of
            -- `.half`/`.word`/`.float`/`.double` until the next segment
            -- directive. Instructions are always word-aligned regardless.
            pure { s with autoAlign := false }
          else
            let aligned := alignUpNat s.curAddr (2 ^ n.toNat)
            if aligned > 4294967296 then
              throw (.badDirective ".align runs past the end of the 32-bit address space" pl.lineNo)
            let s ← s.bindPending aligned pl.lineNo
            pure (s.setAddr aligned)
      | _ => throw (.badOperand ".align expects exactly one operand" pl.lineNo)
    else if directiveSet.contains m then do
      let (align, bytes) ← directiveLayout m pl.operands pl.lineNo
      s.place pl m (if s.autoAlign then align else 1) bytes
    else if isKnownMnemonic m then do
      if !s.seg.isText then
        throw (.badDirective s!"instruction '{m}' in a data segment (.data/.kdata)" pl.lineNo)
      if s.noat && atIdioms.contains m then
        throw (.badOperand s!"'{m}' expands through $at, which .set noat forbids" pl.lineNo)
      let simple ← expandIdiom m pl.operands pl.lineNo
      let mut n := 0
      for (sm, sops) in simple do
        n := n + (← wordsForSimple sm sops pl.lineNo)
      -- Instructions are always word-aligned (data directives are allowed
      -- in `.text`, so the location counter may be unaligned here).
      s.place pl m 4 (4 * n)
    else if m.startsWith "." then
      throw (.badDirective s!"unknown directive '{m}'" pl.lineNo)
    else
      throw (.unknownMnemonic s!"unknown mnemonic '{m}'" pl.lineNo)

-- ====================================================================
-- Pass 2: encode (labels now fully resolved)
-- ====================================================================

private def resolveLabel (labels : Std.HashMap String W32) (tok : String) (lineNo : Nat) :
    Except AsmError W32 :=
  match labels.get? tok with
  | some addr => pure addr
  | none => throw (.undefinedLabel s!"undefined label '{tok}'" lineNo)

/-- Evaluate a `label`, `label±const` or pure constant operand to an exact
(unwrapped) integer. -/
private def evalExpr (labels : Std.HashMap String W32) (tok : String) (lineNo : Nat) :
    Except AsmError Int := do
  let (sym, k) ← parseExpr tok lineNo
  match sym with
  | none => pure k
  | some l => do
      let a ← resolveLabel labels l lineNo
      pure ((a.toNat : Int) + k)

private def rtWord (rs rt rd shamt funct : Nat) : W32 :=
  mkRT (natToW32 rs) (natToW32 rt) (natToW32 rd) (natToW32 shamt) (natToW32 funct)

private def itWord (opcode rs rt : Nat) (imm : W32) : W32 :=
  mkIT (natToW32 opcode) (natToW32 rs) (natToW32 rt) imm

private def jWord (opcode : Nat) (targetWordAddr : Nat) : W32 :=
  (natToW32 opcode <<< 26) ||| mkJT (natToW32 targetWordAddr)

/-- Build a nonzero-opcode R-type-like word (`clo`/`clz`/`seb`/`seh`:
SPECIAL2/SPECIAL3), same as `rtWord` but with the real opcode OR'd into the
top 6 bits (mirrors `jWord`'s `opcode <<< 26` composition, since `mkRT`
always leaves the opcode field as 0). -/
private def opRtWord (opcode rs rt rd shamt funct : Nat) : W32 :=
  (natToW32 opcode <<< 26) ||| rtWord rs rt rd shamt funct

/-- Build a coprocessor-1 (FPU) R-type-shaped word: `mkRT`'s opcode field is
always 0 (correct for plain R-type), so this ORs in opcode 0x11 explicitly,
the same way `jWord` ORs its opcode over `mkJT`'s target-only field. -/
private def cop1RtWord (fmt rt rd shamt funct : Nat) : W32 :=
  (natToW32 0x11 <<< 26) ||| rtWord fmt rt rd shamt funct

/-- Build a coprocessor-0 (CP0) R-type-shaped word: same opcode-OR
convention as `cop1RtWord`, but opcode 0x10 (COP0). -/
private def cop0RtWord (fmt rt rd shamt funct : Nat) : W32 :=
  (natToW32 0x10 <<< 26) ||| rtWord fmt rt rd shamt funct

/-- The general two-word `lui $at, hi16 ; ori rt, $at, lo16` load of a
32-bit value (used for large `li` and for every `la`). -/
private def encodeLuiOri (rt : Nat) (w : W32) : List W32 :=
  [itWord 0x0f 0 atReg (w >>> 16),                 -- lui $at, hi16
   itWord 0x0d atReg rt (w &&& 0xffff#32)]         -- ori rt, $at, lo16

/-- Encode an `li $rt, v` expansion per `PseudoOps.txt` (see `liWordCount`).
`v` must already be range-checked to `-2^31 .. 2^32-1`. -/
private def encodeLi (rt : Nat) (v : Int) : List W32 :=
  if (-32768 : Int) ≤ v ∧ v ≤ -1 then
    [itWord 0x09 zeroReg rt (ofInt32 v &&& 0xffff#32)]   -- addiu rt, $zero, v
  else if (0 : Int) ≤ v ∧ v ≤ 65535 then
    [itWord 0x0d zeroReg rt (ofInt32 v)]           -- ori rt, $zero, v
  else
    encodeLuiOri rt (ofInt32 v)

private def encodeRForm (name : String) (funct : Nat) (form : RForm) (operands : List String)
    (lineNo : Nat) : Except AsmError W32 :=
  match form with
  | .arith3 =>
    match operands with
    | [rdT, rsT, rtT] => do
        let rd ← parseRegister rdT lineNo
        let rs ← parseRegister rsT lineNo
        let rt ← parseRegister rtT lineNo
        pure (rtWord rs rt rd 0 funct)
    | _ => throw (.badOperand s!"{name} expects 'rd, rs, rt'" lineNo)
  | .shift =>
    match operands with
    | [rdT, rtT, shT] => do
        let rd ← parseRegister rdT lineNo
        let rt ← parseRegister rtT lineNo
        let sh ← parseImmediate shT lineNo
        if sh < 0 ∨ sh > 31 then throw (.badImmediate s!"{name} shamt out of range (0-31)" lineNo)
        pure (rtWord 0 rt rd sh.toNat funct)
    | _ => throw (.badOperand s!"{name} expects 'rd, rt, shamt'" lineNo)
  | .shiftv =>
    match operands with
    | [rdT, rtT, rsT] => do
        let rd ← parseRegister rdT lineNo
        let rt ← parseRegister rtT lineNo
        let rs ← parseRegister rsT lineNo
        pure (rtWord rs rt rd 0 funct)
    | _ => throw (.badOperand s!"{name} expects 'rd, rt, rs'" lineNo)
  | .multdiv =>
    match operands with
    | [rsT, rtT] => do
        let rs ← parseRegister rsT lineNo
        let rt ← parseRegister rtT lineNo
        pure (rtWord rs rt 0 0 funct)
    | _ => throw (.badOperand s!"{name} expects 'rs, rt'" lineNo)
  | .hilo =>
    match operands with
    | [rdT] => do
        let rd ← parseRegister rdT lineNo
        pure (rtWord 0 0 rd 0 funct)
    | _ => throw (.badOperand s!"{name} expects 'rd'" lineNo)

/-- 16-bit immediate field of an in-range value (two's complement for
negatives). -/
private def imm16 (v : Int) : W32 := ofInt32 v &&& 0xffff#32

private def encodeIForm (name : String) (opcode : Nat) (form : IForm) (operands : List String)
    (lineNo : Nat) : Except AsmError W32 :=
  match form with
  | .arith =>
    match operands with
    | [rtT, rsT, immT] => do
        let rt ← parseRegister rtT lineNo
        let rs ← parseRegister rsT lineNo
        let imm ← parseImmediate immT lineNo
        -- andi/ori/xori (0x0c/0x0d/0x0e) zero-extend; addi/addiu/slti/sltiu
        -- sign-extend. Out-of-range values are rejected, never truncated
        -- or macro-expanded.
        if opcode == 0x0c || opcode == 0x0d || opcode == 0x0e then
          checkRange s!"{name} immediate" 0 65535 imm lineNo
        else
          checkRange s!"{name} immediate" (-32768) 32767 imm lineNo
        pure (itWord opcode rs rt (imm16 imm))
    | _ => throw (.badOperand s!"{name} expects 'rt, rs, imm'" lineNo)
  | .lui =>
    match operands with
    | [rtT, immT] => do
        let rt ← parseRegister rtT lineNo
        let imm ← parseImmediate immT lineNo
        checkRange s!"{name} immediate" 0 65535 imm lineNo
        pure (itWord opcode 0 rt (imm16 imm))
    | _ => throw (.badOperand s!"{name} expects 'rt, imm'" lineNo)
  | .mem =>
    match operands with
    | [rtT, memT] => do
        let rt ← parseRegister rtT lineNo
        let (imm, rs) ← parseMemOperand memT lineNo
        pure (itWord opcode rs rt (imm16 imm))
    | _ => throw (.badOperand s!"{name} expects 'rt, offset(rs)'" lineNo)
  | .trapImm rtField =>
    match operands with
    | [rsT, immT] => do
        let rs ← parseRegister rsT lineNo
        let imm ← parseImmediate immT lineNo
        checkRange s!"{name} immediate" (-32768) 32767 imm lineNo
        pure (itWord opcode rs rtField (imm16 imm))
    | _ => throw (.badOperand s!"{name} expects 'rs, imm'" lineNo)
  | .memNoRt rtField =>
    match operands with
    | [memT] => do
        let (imm, rs) ← parseMemOperand memT lineNo
        pure (itWord opcode rs rtField (imm16 imm))
    | _ => throw (.badOperand s!"{name} expects 'offset(rs)'" lineNo)

/-- `j`/`jal`: the operand is an absolute address (numeric, `label`, or
`label±const`). It must be word-aligned and lie in the same 256MB region as
the delay slot (`pc + 4`), since only the low 28 bits are encoded. -/
private def encodeJForm (labels : Std.HashMap String W32) (opcode : Nat) (operands : List String)
    (instrAddr : W32) (lineNo : Nat) : Except AsmError W32 :=
  match operands with
  | [tgt] => do
      let target ← evalExpr labels tgt lineNo
      if target < 0 ∨ target ≥ 4294967296 then
        throw (.badImmediate s!"jump target outside the 32-bit address space: {target}" lineNo)
      let t := target.toNat
      if t % 4 ≠ 0 then throw (.badOperand s!"jump target must be word-aligned: '{tgt}'" lineNo)
      let slot := (instrAddr.toNat + 4) % 4294967296
      if t / 268435456 ≠ slot / 268435456 then
        throw (.badOperand
          s!"jump target '{tgt}' is outside the 256MB region of the delay slot (not encodable in j/jal)" lineNo)
      pure (jWord opcode ((t % 268435456) / 4))
  | _ => throw (.badOperand s!"jump expects a single target operand" lineNo)

/-- Branch offset field (in words, relative to the delay slot). A purely
numeric operand is the offset itself (MARS convention, unchanged); a
`label`/`label±const` operand is an address, which must be a whole number
of words away from `pc + 4` and within the signed 16-bit word range. -/
private def branchOffset (labels : Std.HashMap String W32) (tgt : String) (instrAddr : W32)
    (lineNo : Nat) : Except AsmError Int := do
  let (sym, k) ← parseExpr tgt lineNo
  match sym with
  | none => do
      checkRange "branch offset" (-32768) 32767 k lineNo
      pure k
  | some l => do
      let base ← resolveLabel labels l lineNo
      let diff : Int := (base.toNat : Int) + k - ((instrAddr.toNat : Int) + 4)
      if diff % 4 ≠ 0 then
        throw (.badOperand s!"branch target '{tgt}' is not word-aligned relative to the branch" lineNo)
      let w := diff / 4
      if w < -32768 ∨ w > 32767 then
        throw (.badOperand s!"branch target '{tgt}' out of range ({w} words; limit -32768..32767)" lineNo)
      pure w

private def encodeBForm (labels : Std.HashMap String W32) (name : String) (opcode : Nat)
    (form : BForm) (operands : List String) (instrAddr : W32) (lineNo : Nat) :
    Except AsmError W32 :=
  match form with
  | .two =>
    match operands with
    | [rsT, rtT, tgt] => do
        let rs ← parseRegister rsT lineNo
        let rt ← parseRegister rtT lineNo
        let off ← branchOffset labels tgt instrAddr lineNo
        pure (itWord opcode rs rt (imm16 off))
    | _ => throw (.badOperand s!"{name} expects 'rs, rt, target'" lineNo)
  | .one =>
    match operands with
    | [rsT, tgt] => do
        let rs ← parseRegister rsT lineNo
        let off ← branchOffset labels tgt instrAddr lineNo
        pure (itWord opcode rs 0 (imm16 off))
    | _ => throw (.badOperand s!"{name} expects 'rs, target'" lineNo)
  | .regimm rtField =>
    match operands with
    | [rsT, tgt] => do
        let rs ← parseRegister rsT lineNo
        let off ← branchOffset labels tgt instrAddr lineNo
        pure (itWord opcode rs rtField (imm16 off))
    | _ => throw (.badOperand s!"{name} expects 'rs, target'" lineNo)

/-- Parse an FP condition-code operand: `$fccN` or a bare `N`, `0 ≤ N ≤ 7`. -/
private def parseFcc (tok : String) (line : Nat) : Except AsmError Nat := do
  let body := if tok.startsWith "$fcc" then dropS tok 4 else tok
  match digitsToNat 10 body.toList with
  | some n =>
    if n < 8 then pure n
    else throw (.badOperand s!"FP condition code must be 0..7: '{tok}'" line)
  | none => throw (.badOperand s!"expected an FP condition code ('$fccN' or 'N'), got '{tok}'" line)

/-- Parse an indexed memory operand `$index($base)`. -/
private def parseIndexedOperand (tok : String) (line : Nat) : Except AsmError (Nat × Nat) := do
  match splitTop tok.toList '(' with
  | [idxCs, restCs] =>
    let rest := trimChars restCs
    if rest.getLast? != some ')' then
      throw (.badOperand s!"missing closing ')' in operand '{tok}'" line)
    let base ← parseRegister (String.ofList (trimChars rest.dropLast)) line
    let index ← parseRegister (String.ofList (trimChars idxCs)) line
    pure (index, base)
  | _ => throw (.badOperand s!"expected '$index($base)' operand, got '{tok}'" line)

/-- Encode a coprocessor-1 (FPU) mnemonic's operand list into its word, per
`Cop1Form`'s shape and the static parameters carried in `cop1Table`. -/
private def encodeCop1Form (labels : Std.HashMap String W32) (name : String) (form : Cop1Form)
    (operands : List String) (instrAddr : W32) (lineNo : Nat) : Except AsmError W32 :=
  match form with
  | .moveGpFp fmt =>
    match operands with
    | [rtT, fsT] => do
        let rt ← parseRegister rtT lineNo
        -- `cfc1`/`ctc1` (fmt 2/6) address an FPU *control* register, written
        -- `$31` in standard syntax; the `$f31` spelling stays accepted.
        let fs ←
          if fmt == 2 || fmt == 6 then
            match parseFpRegister fsT lineNo with
            | .ok n => pure n
            | .error _ => parseCopRegister "FPU control" fsT lineNo
          else parseFpRegister fsT lineNo
        pure (cop1RtWord fmt rt fs 0 0)
    | _ => throw (.badOperand s!"{name} expects '$rt, $fs'" lineNo)
  | .mem opcode =>
    match operands with
    | [ftT, memT] => do
        let ft ← parseFpRegister ftT lineNo
        let (imm, rs) ← parseMemOperand memT lineNo
        pure (itWord opcode rs ft (imm16 imm))
    | _ => throw (.badOperand s!"{name} expects '$ft, offset($rs)'" lineNo)
  | .arith3 fmt funct =>
    match operands with
    | [fdT, fsT, ftT] => do
        let fd ← parseFpRegister fdT lineNo
        let fs ← parseFpRegister fsT lineNo
        let ft ← parseFpRegister ftT lineNo
        pure (cop1RtWord fmt ft fs fd funct)
    | _ => throw (.badOperand s!"{name} expects '$fd, $fs, $ft'" lineNo)
  | .unary fmt funct =>
    match operands with
    | [fdT, fsT] => do
        let fd ← parseFpRegister fdT lineNo
        let fs ← parseFpRegister fsT lineNo
        pure (cop1RtWord fmt 0 fs fd funct)
    | _ => throw (.badOperand s!"{name} expects '$fd, $fs'" lineNo)
  -- `C.cond.fmt`: bits 10..8 = cc, 7..6 = 0, 5..4 = FC = 11, 3..0 = cond
  | .compare fmt cond =>
    let go (cc : Nat) (fsT ftT : String) : Except AsmError W32 := do
      let fs ← parseFpRegister fsT lineNo
      let ft ← parseFpRegister ftT lineNo
      pure (cop1RtWord fmt ft fs (cc * 4) (0x30 + cond))
    match operands with
    | [fsT, ftT] => go 0 fsT ftT
    | [ccT, fsT, ftT] => do go (← parseFcc ccT lineNo) fsT ftT
    | _ => throw (.badOperand s!"{name} expects '[cc,] $fs, $ft'" lineNo)
  -- FP branches: `rt` field = cc (3 bits) ‖ nd ‖ tf
  | .branch nd tf =>
    let go (cc : Nat) (tgt : String) : Except AsmError W32 := do
      let off ← branchOffset labels tgt instrAddr lineNo
      pure (itWord 0x11 0x08 (cc * 4 + nd * 2 + tf) (imm16 off))
    match operands with
    | [tgt] => go 0 tgt
    | [ccT, tgt] => do go (← parseFcc ccT lineNo) tgt
    | _ => throw (.badOperand s!"{name} expects '[cc,] target'" lineNo)
  | .movcf fmt tf =>
    let go (fdT fsT : String) (cc : Nat) : Except AsmError W32 := do
      let fd ← parseFpRegister fdT lineNo
      let fs ← parseFpRegister fsT lineNo
      pure (cop1RtWord fmt (cc * 4 + tf) fs fd 0x11)
    match operands with
    | [fdT, fsT] => go fdT fsT 0
    | [fdT, fsT, ccT] => do go fdT fsT (← parseFcc ccT lineNo)
    | _ => throw (.badOperand s!"{name} expects '$fd, $fs[, cc]'" lineNo)
  | .movci tf =>
    let go (rdT rsT : String) (cc : Nat) : Except AsmError W32 := do
      let rd ← parseRegister rdT lineNo
      let rs ← parseRegister rsT lineNo
      pure (rtWord rs (cc * 4 + tf) rd 0 0x01)
    match operands with
    | [rdT, rsT] => go rdT rsT 0
    | [rdT, rsT, ccT] => do go rdT rsT (← parseFcc ccT lineNo)
    | _ => throw (.badOperand s!"{name} expects '$rd, $rs[, cc]'" lineNo)
  | .movGpr fmt funct =>
    match operands with
    | [fdT, fsT, rtT] => do
        let fd ← parseFpRegister fdT lineNo
        let fs ← parseFpRegister fsT lineNo
        let rt ← parseRegister rtT lineNo
        pure (cop1RtWord fmt rt fs fd funct)
    | _ => throw (.badOperand s!"{name} expects '$fd, $fs, $rt'" lineNo)
  | .madd funct =>
    match operands with
    | [fdT, frT, fsT, ftT] => do
        let fd ← parseFpRegister fdT lineNo
        let fr ← parseFpRegister frT lineNo
        let fs ← parseFpRegister fsT lineNo
        let ft ← parseFpRegister ftT lineNo
        pure (opRtWord 0x13 fr ft fs fd funct)
    | _ => throw (.badOperand s!"{name} expects '$fd, $fr, $fs, $ft'" lineNo)
  | .indexedLoad funct =>
    match operands with
    | [fdT, memT] => do
        let fd ← parseFpRegister fdT lineNo
        let (index, base) ← parseIndexedOperand memT lineNo
        pure (opRtWord 0x13 base index 0 fd funct)
    | _ => throw (.badOperand s!"{name} expects '$fd, $index($base)'" lineNo)
  | .indexedStore funct =>
    match operands with
    | [fsT, memT] => do
        let fs ← parseFpRegister fsT lineNo
        let (index, base) ← parseIndexedOperand memT lineNo
        pure (opRtWord 0x13 base index fs 0 funct)
    | _ => throw (.badOperand s!"{name} expects '$fs, $index($base)'" lineNo)
  | .prefx =>
    match operands with
    | [hintT, memT] => do
        let hint ← parseCode name "hint" 31 hintT lineNo
        let (index, base) ← parseIndexedOperand memT lineNo
        pure (opRtWord 0x13 base index hint 0 0x0f)
    | _ => throw (.badOperand s!"{name} expects 'hint, $index($base)'" lineNo)

/-- `mfc0`/`mtc0` operands: `$rt, rd` or `$rt, rd, sel`, where `rd` is
`$N` or a bare `N` and `sel` (default 0) is `0..7`. Returns `(rt, rd, sel)`. -/
private def parseCp0Operands (name : String) (operands : List String) (lineNo : Nat) :
    Except AsmError (Nat × Nat × Nat) := do
  let two (rtT rdT : String) : Except AsmError (Nat × Nat) := do
    let rt ← parseRegister rtT lineNo
    let rd ← parseCopRegister "CP0" rdT lineNo
    pure (rt, rd)
  match operands with
  | [rtT, rdT] => do
      let (rt, rd) ← two rtT rdT
      pure (rt, rd, 0)
  | [rtT, rdT, selT] => do
      let (rt, rd) ← two rtT rdT
      let sel ← parseCode name "sel" 7 selT lineNo
      pure (rt, rd, sel)
  | _ => throw (.badOperand s!"{name} expects '$rt, $rd[, sel]'" lineNo)

/-- Encode one table-level real/pseudo instruction (after `expandIdiom`)
into its emitted word(s). -/
private def encodeInstruction (labels : Std.HashMap String W32) (item : RawItem) :
    Except AsmError (List W32) := do
  let name := item.mnemonic
  match rTable.find? (·.1 == name) with
  | some (_, funct, form) =>
    -- register traps take an optional third operand: the 10-bit `code`
    -- field (bits 15..6)
    match trapRegMnemonics.contains name, item.operands with
    | true, [rsT, rtT, cT] =>
      let c ← parseCode name "code" 1023 cT item.lineNo
      let w ← encodeRForm name funct form [rsT, rtT] item.lineNo
      return [w ||| (natToW32 c <<< 6)]
    | _, _ => return [← encodeRForm name funct form item.operands item.lineNo]
  | none =>
  match iTable.find? (·.1 == name) with
  | some (_, opcode, form) => return [← encodeIForm name opcode form item.operands item.lineNo]
  | none =>
  match jTable.find? (·.1 == name) with
  | some (_, opcode) => return [← encodeJForm labels opcode item.operands item.addr item.lineNo]
  | none =>
  match bTable.find? (·.1 == name) with
  | some (_, opcode, form) => return [← encodeBForm labels name opcode form item.operands item.addr item.lineNo]
  | none =>
  match cop1Table.find? (·.1 == name) with
  | some (_, form) => return [← encodeCop1Form labels name form item.operands item.addr item.lineNo]
  | none =>
  match name with
  | "li" =>
    match item.operands with
    | [rtT, valT] => do
        let rt ← parseRegister rtT item.lineNo
        let v ← parseImmediate valT item.lineNo
        checkRange "li value" (-2147483648) 4294967295 v item.lineNo
        pure (encodeLi rt v)
    | _ => throw (.badOperand s!"li expects 'li $reg, imm'" item.lineNo)
  | "la" =>
    match item.operands with
    | [rtT, lbl] => do
        let rt ← parseRegister rtT item.lineNo
        let addr ← evalExpr labels lbl item.lineNo
        checkRange "la address" 0 4294967295 addr item.lineNo
        -- Always the two-word form, whatever the address (pass 1 reserved
        -- exactly two words).
        pure (encodeLuiOri rt (ofInt32 addr))
    | _ => throw (.badOperand s!"la expects 'la $reg, label'" item.lineNo)
  | "move" =>
    match item.operands with
    | [rdT, rsT] => do
        let rd ← parseRegister rdT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord 0 rs rd 0 0x21]              -- addu rd, $zero, rs
    | _ => throw (.badOperand s!"move expects 'move $dst, $src'" item.lineNo)
  | "nop" =>
    match item.operands with
    | [] => pure [0#32]
    | _ => throw (.badOperand s!"nop takes no operands" item.lineNo)
  | "syscall" =>
    match item.operands with
    | [] => pure [0x0000000C#32]              -- all fields zero except funct = 0x0c
    | [cT] => do                              -- 20-bit `code`, bits 25..6
        let c ← parseCode name "code" 1048575 cT item.lineNo
        pure [(natToW32 c <<< 6) ||| 0x0000000C#32]
    | _ => throw (.badOperand s!"syscall expects at most one (code) operand" item.lineNo)
  -- SPECIAL2 bit-count (MIPS32): `clo $rd, $rs` / `clz $rd, $rs`. The raw
  -- encoding's rt-position field duplicates rd (real hardware quirk, see
  -- `Instruction.lean`'s `.clo`/`.clz` docstrings).
  | "clo" =>
    match item.operands with
    | [rdT, rsT] => do
        let rd ← parseRegister rdT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        pure [opRtWord 0x1c rs rd rd 0 0x21]
    | _ => throw (.badOperand s!"clo expects 'rd, rs'" item.lineNo)
  | "clz" =>
    match item.operands with
    | [rdT, rsT] => do
        let rd ← parseRegister rdT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        pure [opRtWord 0x1c rs rd rd 0 0x20]
    | _ => throw (.badOperand s!"clz expects 'rd, rs'" item.lineNo)
  -- SPECIAL2 GPR multiply (MIPS32): `mul $rd, $rs, $rt`. Plain `rs, rt, rd`
  -- shape, unlike `clo`/`clz` -- no duplicated-field quirk -- but still
  -- SPECIAL2-opcoded (0x1c), so it needs `opRtWord` rather than plain
  -- `rtWord`/`rTable` (docs/spec/MIPS-COVERAGE-GAPS.md §3.5).
  | "mul" =>
    match item.operands with
    | [rdT, rsT, rtT] => do
        let rd ← parseRegister rdT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1c rs rt rd 0 0x02]
    | _ => throw (.badOperand s!"mul expects 'rd, rs, rt'" item.lineNo)
  -- SPECIAL2 multiply-accumulate (MIPS32): `madd $rs, $rt` / `maddu $rs, $rt`
  -- / `msub $rs, $rt` / `msubu $rs, $rt`. Same `rs, rt` shape as `mult`/
  -- `div` (RForm.multdiv), but SPECIAL2-opcoded like `mul` above, so it
  -- needs `opRtWord` rather than `rTable` (docs/spec/MIPS-COVERAGE-GAPS.md
  -- §3.5).
  | "madd" =>
    match item.operands with
    | [rsT, rtT] => do
        let rs ← parseRegister rsT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1c rs rt 0 0 0x00]
    | _ => throw (.badOperand s!"madd expects 'rs, rt'" item.lineNo)
  | "maddu" =>
    match item.operands with
    | [rsT, rtT] => do
        let rs ← parseRegister rsT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1c rs rt 0 0 0x01]
    | _ => throw (.badOperand s!"maddu expects 'rs, rt'" item.lineNo)
  | "msub" =>
    match item.operands with
    | [rsT, rtT] => do
        let rs ← parseRegister rsT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1c rs rt 0 0 0x04]
    | _ => throw (.badOperand s!"msub expects 'rs, rt'" item.lineNo)
  | "msubu" =>
    match item.operands with
    | [rsT, rtT] => do
        let rs ← parseRegister rsT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1c rs rt 0 0 0x05]
    | _ => throw (.badOperand s!"msubu expects 'rs, rt'" item.lineNo)
  -- SPECIAL3 BSHFL sign-extend (MIPS32r2): `seb $rd, $rt` / `seh $rd, $rt`.
  -- `rs` is unused/fixed 0; the shamt-position field (0x10/0x18) selects
  -- which BSHFL sub-op this is.
  | "seb" =>
    match item.operands with
    | [rdT, rtT] => do
        let rd ← parseRegister rdT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1f 0 rt rd 0x10 0x20]
    | _ => throw (.badOperand s!"seb expects 'rd, rt'" item.lineNo)
  | "seh" =>
    match item.operands with
    | [rdT, rtT] => do
        let rd ← parseRegister rdT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1f 0 rt rd 0x18 0x20]
    | _ => throw (.badOperand s!"seh expects 'rd, rt'" item.lineNo)
  -- `wsbh $rd, $rt`: SPECIAL3 BSHFL (MIPS32r2), same family/shape as
  -- `seb`/`seh`, sub-field 0x02.
  | "wsbh" =>
    match item.operands with
    | [rdT, rtT] => do
        let rd ← parseRegister rdT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [opRtWord 0x1f 0 rt rd 0x02 0x20]
    | _ => throw (.badOperand s!"wsbh expects 'rd, rt'" item.lineNo)
  -- `rotr $rd, $rt, $sa` (MIPS32r2): same `rd, rt, shamt` shape as `srl`
  -- (the `.shift` `RForm`), but overloads the normally-0 `rs` field to
  -- 0x01 to select rotate (see `Instruction.lean`'s `.rotr` docstring).
  | "rotr" =>
    match item.operands with
    | [rdT, rtT, saT] => do
        let rd ← parseRegister rdT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        let sa ← parseImmediate saT item.lineNo
        if sa < 0 ∨ sa > 31 then throw (.badImmediate s!"rotr shamt out of range (0-31)" item.lineNo)
        pure [rtWord 1 rt rd sa.toNat 0x02]
    | _ => throw (.badOperand s!"rotr expects 'rd, rt, sa'" item.lineNo)
  -- `rotrv $rd, $rt, $rs` (MIPS32r2): same `rd, rt, rs` shape as `srlv`
  -- (the `.shiftv` `RForm`), but overloads the normally-0 `shamt` field to
  -- 0x01 to select rotate.
  | "rotrv" =>
    match item.operands with
    | [rdT, rtT, rsT] => do
        let rd ← parseRegister rdT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs rt rd 1 0x06]
    | _ => throw (.badOperand s!"rotrv expects 'rd, rt, rs'" item.lineNo)
  -- `ext $rt, $rs, pos, size` / `ins $rt, $rs, pos, size` (MIPS32r2
  -- bitfield extract/insert, SPECIAL3 opcode 0x1f): `pos`/`size` are
  -- compile-time constants (not registers). Real hardware packs `pos`
  -- into the `shamt` field for both, but the `rd`-position field differs
  -- (`size - 1` for `ext`, `pos + size - 1` for `ins`) -- see
  -- `Instruction.lean`'s `.ext`/`.ins` docstrings. Both fields must fit
  -- their 5-bit encoding slots, so `pos` is 0-31, `size` is 1-32, and
  -- `pos + size <= 32` (the real architectural constraint; violating it
  -- is UNPREDICTABLE on real hardware, so this assembler rejects it
  -- outright rather than silently truncating).
  | "ext" =>
    match item.operands with
    | [rtT, rsT, posT, sizeT] => do
        let rt ← parseRegister rtT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        let pos ← parseImmediate posT item.lineNo
        let size ← parseImmediate sizeT item.lineNo
        if pos < 0 ∨ pos > 31 then throw (.badImmediate s!"ext pos out of range (0-31)" item.lineNo)
        if size < 1 ∨ size > 32 then throw (.badImmediate s!"ext size out of range (1-32)" item.lineNo)
        if pos + size > 32 then throw (.badImmediate s!"ext pos + size must be <= 32" item.lineNo)
        pure [opRtWord 0x1f rs rt (size - 1).toNat pos.toNat 0x00]
    | _ => throw (.badOperand s!"ext expects 'rt, rs, pos, size'" item.lineNo)
  | "ins" =>
    match item.operands with
    | [rtT, rsT, posT, sizeT] => do
        let rt ← parseRegister rtT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        let pos ← parseImmediate posT item.lineNo
        let size ← parseImmediate sizeT item.lineNo
        if pos < 0 ∨ pos > 31 then throw (.badImmediate s!"ins pos out of range (0-31)" item.lineNo)
        if size < 1 ∨ size > 32 then throw (.badImmediate s!"ins size out of range (1-32)" item.lineNo)
        if pos + size > 32 then throw (.badImmediate s!"ins pos + size must be <= 32" item.lineNo)
        pure [opRtWord 0x1f rs rt (pos + size - 1).toNat pos.toNat 0x04]
    | _ => throw (.badOperand s!"ins expects 'rt, rs, pos, size'" item.lineNo)
  -- Register-indirect jump/call (real MIPS32 `jr`/`jalr`, opcode 0, funct
  -- 0x08/0x09; see `Instruction.lean`'s `.jr`/`.jalr` docstrings). `rt`/
  -- `shamt` are unused/fixed 0 in the real encoding.
  | "jr" =>
    match item.operands with
    | [rsT] => do
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs 0 0 0 0x08]
    | _ => throw (.badOperand s!"jr expects 'rs'" item.lineNo)
  | "jalr" =>
    match item.operands with
    | [rdT, rsT] => do
        let rd ← parseRegister rdT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs 0 rd 0 0x09]
    -- One-operand sugar: `jalr $rs` == `jalr $ra, $rs` (rd defaults to 31),
    -- per real MIPS32 assembly syntax.
    | [rsT] => do
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs 0 31 0 0x09]
    | _ => throw (.badOperand s!"jalr expects 'rd, rs' or 'rs'" item.lineNo)
  -- Write-direction HI/LO moves (real MIPS32 `mthi`/`mtlo`, opcode 0, funct
  -- 0x11/0x13 -- the next funct values immediately after `mfhi`'s 0x10/
  -- `mflo`'s 0x12; see `Instruction.lean`'s `.mthi`/`.mtlo` docstrings).
  | "mthi" =>
    match item.operands with
    | [rsT] => do
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs 0 0 0 0x11]
    | _ => throw (.badOperand s!"mthi expects 'rs'" item.lineNo)
  | "mtlo" =>
    match item.operands with
    | [rsT] => do
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs 0 0 0 0x13]
    | _ => throw (.badOperand s!"mtlo expects 'rs'" item.lineNo)
  -- `jr.hb $rs` / `jalr.hb [$rd,] $rs` (MIPS32r2 hazard-barrier jumps):
  -- `jr`/`jalr` with the hint bit (bit 10, i.e. `shamt` = 0x10) set; they
  -- decode to `.jrHb`/`.jalrHb` (MD00086 Vol II-A Rev 6.06, JR.HB p.208,
  -- JALR.HB p.198), which execute as `jr`/`jalr` in a model with no pipeline
  -- hazards (see the `#guard`s in `Tests/AsmTests.lean`).
  | "jr.hb" =>
    match item.operands with
    | [rsT] => do
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs 0 0 0x10 0x08]
    | _ => throw (.badOperand s!"jr.hb expects 'rs'" item.lineNo)
  | "jalr.hb" =>
    match item.operands with
    | [rdT, rsT] => do
        let rd ← parseRegister rdT item.lineNo
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs 0 rd 0x10 0x09]
    | [rsT] => do
        let rs ← parseRegister rsT item.lineNo
        pure [rtWord rs 0 31 0x10 0x09]
    | _ => throw (.badOperand s!"jalr.hb expects 'rd, rs' or 'rs'" item.lineNo)
  | "break" =>
    match item.operands with
    | [] => pure [0x0000000D#32]              -- all fields zero except funct = 0x0d
    -- GNU as syntax: `break c` puts `c` in bits 25..16, `break c, d` also
    -- `d` in bits 15..6 (together the manual's 20-bit `code`, bits 25..6)
    | [cT] => do
        let c ← parseCode name "code" 1023 cT item.lineNo
        pure [(natToW32 c <<< 16) ||| 0x0000000D#32]
    | [cT, dT] => do
        let c ← parseCode name "code" 1023 cT item.lineNo
        let d ← parseCode name "code" 1023 dT item.lineNo
        pure [(natToW32 c <<< 16) ||| (natToW32 d <<< 6) ||| 0x0000000D#32]
    | _ => throw (.badOperand s!"break expects at most two (code) operands" item.lineNo)
  | "sync" =>
    match item.operands with
    | [] => pure [0x0000000F#32]              -- all fields zero except funct = 0x0f (stype = 0)
    | [cT] => do
        let c ← parseCode name "stype" 31 cT item.lineNo
        pure [(natToW32 c <<< 6) ||| 0x0000000F#32]
    | _ => throw (.badOperand s!"sync expects at most one (stype) operand" item.lineNo)
  -- `pref hint, offset(base)` (opcode 0x33; hint in the `rt` field)
  | "pref" =>
    match item.operands with
    | [hintT, memT] => do
        let hint ← parseCode name "hint" 31 hintT item.lineNo
        let (imm, rs) ← parseMemOperand memT item.lineNo
        pure [itWord 0x33 rs hint (imm16 imm)]
    | _ => throw (.badOperand s!"pref expects 'hint, offset($rs)'" item.lineNo)
  -- `di [rt]` / `ei [rt]` (COP0 MFMC0, rd = 12, sc = bit 5)
  | "di" =>
    match item.operands with
    | [] => pure [cop0RtWord 0x0b 0 12 0 0x00]
    | [rtT] => do pure [cop0RtWord 0x0b (← parseRegister rtT item.lineNo) 12 0 0x00]
    | _ => throw (.badOperand s!"di expects at most one register operand" item.lineNo)
  | "ei" =>
    match item.operands with
    | [] => pure [cop0RtWord 0x0b 0 12 0 0x20]
    | [rtT] => do pure [cop0RtWord 0x0b (← parseRegister rtT item.lineNo) 12 0 0x20]
    | _ => throw (.badOperand s!"ei expects at most one register operand" item.lineNo)
  -- Coprocessor-0 (CP0) register move / execution control (real MIPS32
  -- ISA, docs/spec/MIPS-COVERAGE-GAPS.md §3.10A; see `Instruction.lean`/
  -- `Step.lean`). `rd` is a CP0 register number (`$12` or `12`, 0-31);
  -- with an optional `sel`; see `isModeledCp0Reg` for the modeled pairs.
  -- `rdhwr $rt, $rd` (MIPS32r2): SPECIAL3 (0x1f), `rs` = 0, bits 10..6 = 0, funct 0x3b.
  | "rdhwr" =>
    match item.operands with
    | [rtT, rdT] => do
        let rt ← parseRegister rtT item.lineNo
        let rd ← parseCopRegister "hardware" rdT item.lineNo
        pure [opRtWord 0x1f 0 rt rd 0 0x3b]
    | _ => throw (.badOperand s!"rdhwr expects '$rt, $rd'" item.lineNo)
  | "mfc0" => do
      let (rt, rd, sel) ← parseCp0Operands name item.operands item.lineNo
      pure [cop0RtWord 0x00 rt rd 0 sel]
  | "mtc0" => do
      let (rt, rd, sel) ← parseCp0Operands name item.operands item.lineNo
      pure [cop0RtWord 0x04 rt rd 0 sel]
  | "eret" =>
    match item.operands with
    | [] => pure [cop0RtWord 0x10 0 0 0 0x18]
    | _ => throw (.badOperand s!"eret takes no operands" item.lineNo)
  | "wait" =>
    match item.operands with
    | [] => pure [cop0RtWord 0x10 0 0 0 0x20]
    | [cT] => do                              -- 19-bit `code`, bits 24..6
        let c ← parseCode name "code" 524287 cT item.lineNo
        pure [cop0RtWord 0x10 0 0 0 0x20 ||| (natToW32 c <<< 6)]
    | _ => throw (.badOperand s!"wait expects at most one (code) operand" item.lineNo)
  -- `rdpgpr $rd, $rt` / `wrpgpr $rd, $rt` (MIPS32 Release 2; MD00086 Vol II-A Rev 6.06, RDPGPR
  -- p.335, WRPGPR p.444): COP0, `rs` = 0x0a / 0x0e, bits 10..0 zero.
  | "rdpgpr" | "wrpgpr" =>
    match item.operands with
    | [rdT, rtT] => do
        let rd ← parseRegister rdT item.lineNo
        let rt ← parseRegister rtT item.lineNo
        pure [cop0RtWord (if name == "rdpgpr" then 0x0a else 0x0e) rt rd 0 0]
    | _ => throw (.badOperand s!"{name} expects '$rd, $rt'" item.lineNo)
  | _ => throw (.unknownMnemonic s!"unknown mnemonic '{name}'" item.lineNo)

private def applyItem (labels : Std.HashMap String W32) (prog : Program) (item : RawItem) :
    Except AsmError Program :=
  match item.mnemonic with
  | ".word" => do
      let mut bytes : List Nat := []
      for tok in item.operands do
        let v ← evalExpr labels tok item.lineNo
        checkRange ".word value" (-2147483648) 4294967295 v item.lineNo
        bytes := bytes ++ beBytes 4 (ofInt32 v).toNat
      pure (putBytes prog item.addr bytes)
  | ".half" => do
      let mut bytes : List Nat := []
      for tok in item.operands do
        let v ← parseImmediate tok item.lineNo
        checkRange ".half value" (-32768) 65535 v item.lineNo
        bytes := bytes ++ beBytes 2 (ofInt32 v).toNat
      pure (putBytes prog item.addr bytes)
  | ".byte" => do
      let mut bytes : List Nat := []
      for tok in item.operands do
        let v ← parseImmediate tok item.lineNo
        checkRange ".byte value" (-128) 255 v item.lineNo
        bytes := bytes ++ beBytes 1 (ofInt32 v).toNat
      pure (putBytes prog item.addr bytes)
  | ".float" => do
      let mut bytes : List Nat := []
      for tok in item.operands do
        bytes := bytes ++ beBytes 4 (← parseFloatLit 24 8 tok item.lineNo)
      pure (putBytes prog item.addr bytes)
  | ".double" => do
      -- Big-endian doubleword: most-significant word at the lower address,
      -- the layout `ldc1`/`sdc1` use (`Step.lean`).
      let mut bytes : List Nat := []
      for tok in item.operands do
        bytes := bytes ++ beBytes 8 (← parseFloatLit 53 11 tok item.lineNo)
      pure (putBytes prog item.addr bytes)
  | ".space" => pure prog  -- reserved bytes default to 0 (sparse map, unread = 0)
  | m =>
    if stringDirectives.contains m then do
      let mut bytes : List Nat := []
      for tok in item.operands do
        let b ← parseStringTok tok item.lineNo
        bytes := bytes ++ b ++ (if m == ".ascii" then [] else [0])
      pure (putBytes prog item.addr bytes)
    else do
      let simple ← expandIdiom m item.operands item.lineNo
      let mut p := prog
      let mut a := item.addr
      for (sm, sops) in simple do
        let words ← encodeInstruction labels
          { lineNo := item.lineNo, addr := a, size := 0, mnemonic := sm, operands := sops }
        for w in words do
          p := putWord p a w
          a := a + 4#32
      if a.toNat ≠ (item.addr.toNat + item.size) % 4294967296 then
        throw (.badOperand s!"internal error: '{m}' emitted a different size in pass 2 than pass 1 reserved" item.lineNo)
      pure p

/-- Reject two items occupying the same bytes (possible once segment
directives take explicit addresses) -- the later one would otherwise
silently overwrite the earlier. -/
private def checkOverlap (items : Array RawItem) : Except AsmError Unit := do
  let spans := (items.filter (fun it => it.size > 0)).qsort (fun a b => a.addr.toNat < b.addr.toNat)
  let mut prev : Option RawItem := none
  for it in spans do
    match prev with
    | some p =>
      if p.addr.toNat + p.size > it.addr.toNat then
        let (first, second) := if p.lineNo ≤ it.lineNo then (p, it) else (it, p)
        throw (.badDirective
          s!"'{second.mnemonic}' overlaps the bytes emitted by '{first.mnemonic}' on line {first.lineNo}" second.lineNo)
    | none => pure ()
    prev := some it
  pure ()

-- ====================================================================
-- Top level
-- ====================================================================

/-- Assemble MIPS32 source text into a `Program` (address → word map
covering every segment's contents). See module docstring for supported
syntax and layout conventions. -/
def assemble (src : String) : AsmResult := do
  let rawLines := src.splitOn "\n"
  let numbered := rawLines.zipIdx.map (fun (l, i) => (i + 1, l))
  let initial : LState :=
    { seg := .text, textAddr := textBase.toNat, dataAddr := dataBase.toNat,
      ktextAddr := ktextBase.toNat, kdataAddr := kdataBase.toNat,
      autoAlign := true, pending := [], labels := ∅, items := #[] }
  let laidOut ← numbered.foldlM
    (fun s (lineNo, line) => do
      let pl ← parseLine lineNo line
      layoutLine s pl)
    initial
  -- Labels at the very end of the source name the final location counter.
  let final ← laidOut.bindPending laidOut.curAddr rawLines.length
  checkOverlap final.items
  final.items.foldlM (fun prog item => applyItem final.labels prog item) (∅ : Program)
