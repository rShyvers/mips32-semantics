import Std.Data.HashMap.Basic
import Semantics.Word
import Semantics.Types
import Semantics.Instruction
import Semantics.Asm.Syntax
import Semantics.Asm.Expr
import Semantics.Asm.Float
import Semantics.Asm.Operands
import Semantics.Asm.Int
import Semantics.Asm.Memory
import Semantics.Asm.Branch
import Semantics.Asm.System
import Semantics.Asm.Fpu
import Semantics.Asm.Pseudo
import Semantics.Asm.Table
import Semantics.Asm.Layout

/-!
# Asm — MIPS32 Release 6 assembler (tested, not proved)

Converts assembler source text into a `Program` (`Std.HashMap W32 W32`, address → word). The
public API is `assemble`; the pieces live in `Semantics/Asm/`:

| module | contents |
|---|---|
| `Asm/Syntax` | `AsmError`, segment bases, `parseLine` (labels, mnemonic, operands) |
| `Asm/Expr` | literals, `label±const` expressions, range checks, registers, `offset(base)` |
| `Asm/Float` | exact decimal → IEEE 754 for `.float`/`.double` |
| `Asm/Operands` | `Ctx`, `Enc`, the operand-shape combinators, branch/jump displacements |
| `Asm/Int`, `Asm/Memory`, `Asm/Branch`, `Asm/System`, `Asm/Fpu` | one encoder table per family |
| `Asm/Pseudo` | idioms (text → text) and the `li`/`la` macros |
| `Asm/Table` | the union of the tables; removed pre-Release 6 mnemonics |
| `Asm/Layout` | segments, data directives (byte order of `profile`), the two passes |

**Encodings.** Every table entry produces an `Instruction` and the word is the model's `encode`,
so the assembler emits exactly the Release 6 encodings of the 203 constructors of
`Instruction.lean` (MD00086 Vol II-A Rev 6.06). Instructions Release 6 removed (MOVN/MOVZ,
MULT/DIV/MFHI/..., the SPECIAL2 MUL/MADD family, ADDI, LWL/LWR/SWL/SWR, branch-likely, BLTZAL/
BGEZAL with `rs ≠ 0`, the trap-immediates, the COP1X and FP condition-code instructions) are
assembler errors (`removedMnemonics`).

## Supported syntax
- Labels (`name:`, one or more per line), optionally followed by an instruction/directive on the
  same line. A label name must match `[A-Za-z_.$][A-Za-z0-9_.$]*`; any other text in front of a
  `:` (outside quotes) is an error.
- Directives (case-insensitive): segments `.text`/`.data`/`.ktext`/`.kdata` (each with an
  optional start-address operand); data `.word`, `.half`, `.byte`, `.float`, `.double`, `.ascii`,
  `.asciiz` (= `.asciz`/`.string`), `.space`; `.align n`; `.globl`/`.global`/`.extern` (no-ops);
  `.set noreorder`/`noat`/`at`.
- `#` line comments (honoring `"..."` string and `'c'` character literals).
- Mnemonics are case-insensitive, register names case-sensitive.
- Numeric operands: decimal, `0x` hex, `0b` binary, leading-`0` octal, character literals
  `'a'`/`'\n'`, an optional leading `+`/`-`, and `±` sums of those. `la`, `.word` and branch/jump
  targets also take `label+const` / `label-const`.
- **Nothing is ever truncated**: every immediate, offset, displacement and data value is
  range-checked and rejected with an error carrying the source line number if it does not fit.
  Out-of-range immediates are *not* macro-expanded.
- Empty operands (`add $t0,, $t1`, a trailing `,`) are errors.
- Release 6 operand forms: `aui rt, rs, imm`; `lui rt, imm` (= `aui rt, $0, imm`); `ll`/`sc rt,
  offset(base)` and `pref hint, offset(base)` with a signed 9-bit offset (-256..255);
  `rdhwr rt, rd[, sel]`; `nal`; `bal target`; `pause`; `jalr[.hb] [rd,] rs` (`rd` defaults to
  `$ra`); `jr[.hb] rs` = `jalr[.hb] $0, rs`.
- Optional code operands (GNU as syntax): `break [code[, code2]]`, `syscall [code]`, `teq rs,
  rt[, code]` (all six register traps), `sync [stype]`, `wait [code]`, `mfc0`/`mtc0 rt, rd[,
  sel]`, `di`/`ei`/`dvp`/`evp [rt]`.
- Idioms and macros: see `Asm/Pseudo.lean` (`nop`, `ehb`, `move`, `b`, `beqz`, `bnez`,
  `neg`, `negu`, `not`, `abs`, `blt`/`bge`/`bgt`/`ble`(`u`) via `$at`, `jr`, `jr.hb`, the
  reversed-operand compact branches `bgtc`/`blec`/`bgtuc`/`bleuc`, `li`, `la`). `ssnop` is rejected
  (SSNOP p.387: "Assemblers targeting specifically Release 6 should reject the SSNOP instruction").
- `.set noreorder`, `.set noat`, `.set at` are accepted. This assembler never reorders, so `.set
  noreorder` changes nothing; after `.set noat` the idioms that expand through `$at` are
  rejected. `.set reorder` is **rejected** (it would ask the assembler to fill delay slots), as
  is every other `.set` option.
- Register names `$zero,$at,$v0,$v1,$a0..$a3,$t0..$t7,$s0..$s7,$t8,$t9,$k0,$k1,$gp,$sp,$fp,$s8,
  $ra` plus raw numeric `$0`..`$31` (canonical decimal only), FP registers `$f0`..`$f31`;
  coprocessor register numbers as `$N` or `N`.

## Range checks
| operand | accepted range |
|---|---|
| `addiu`/`slti`/`sltiu`, 16-bit memory offsets | −32768..32767 |
| `ll`/`sc`/`pref` offsets | −256..255 |
| `andi`/`ori`/`xori`/`lui` | 0..65535 |
| `aui` | −32768..65535 |
| `li`, `.word` | −2^31..2^32−1 |
| `.half` | −32768..65535 |
| `.byte` | −128..255 |
| branch to a label | (target − (pc+4)) divisible by 4, −32768..32767 words |
| numeric branch operand (the word offset itself, MARS convention) | −32768..32767 |
| `j`/`jal` | word-aligned, same 256MB region as the delay slot |

## Layout
The `Program` is a sparse address → word map, so any number of disjoint regions can be
assembled. There are four segments, each with its own location counter: `.text` (default
`textBase`, 0x00400000), `.data` (`dataBase`, 0x10010000), `.ktext` (`ktextBase`, 0x80000180 =
the exception vector) and `.kdata` (`kdataBase`, 0x90000000). A segment directive with an
address operand moves that segment's location counter there; without an operand the segment
resumes where it left off. Execution starts at `textBase` (`Env.hostedStart`; `MipsRun --reset`
starts at the reset vector `0xBFC00000`, which `.ktext 0xBFC00000` can fill). Two items that
would occupy the same bytes are an error, as is running past address 2^32.

Alignment: `.word`/`.float` align the location counter to 4, `.half` to 2, `.double` to 8;
`.byte`/`.ascii`/`.asciiz`/`.space` need none. `.align n` aligns to 2^n (n = 1..16); `.align 0`
switches the automatic alignment of the data directives off until the next segment directive.
**A label is bound after alignment**: it names the address of the next item. Data directives are
accepted in `.text`/`.ktext` (every instruction is word-aligned first); instructions in
`.data`/`.kdata` are rejected.

**Byte order**: data is laid out in the byte order of `profile` (`Asm/Layout.lean`): little-endian
for the Release 6 profile (`.word 0x01020304` stores byte `04` first; a `.double` stores its
least-significant byte first). `.float`/`.double` literals are converted with exact rational
arithmetic, correctly rounded to nearest-even (`ratToIeee`).

## Deviation from MARS `la`
This assembler supports exactly `la $rt, label` and `la $rt, label±const`, always as the
two-instruction `aui $at, $0, hi16 ; ori $rt, $at, lo16` (pass 1 reserves two words before label
addresses are known). Any other `la` form is a `badOperand` error.

## Other documented differences from MARS / GNU as
- `li` of 0..65535 uses `ori` (MARS: `addiu` for 0..32767), and a value written as a 32-bit
  pattern `0xffff8000`..`0xffffffff` uses `aui`/`ori`.
- `b label` is GNU as's `beq $0,$0,label` (MARS: `bgez $0,label`); `abs` is GNU as's
  branch-over form.
- The compare-and-branch idioms always use the two-instruction `$at` form.
- GNU as defaults to `.set reorder`; this assembler always assembles what is written.
-/

open Asm

/-- Assemble MIPS32 Release 6 source text into a `Program` (address → word map covering every
segment's contents). See the module docstring for the syntax and layout conventions. -/
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
