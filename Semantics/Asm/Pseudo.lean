import Semantics.Asm.Operands

/-!
# Asm.Pseudo — assembler idioms and the `li`/`la` macros

**Idioms** rewrite one statement into table-level statements, as text (so pass 1 can size them
without labels). None inserts a `nop`: this assembler always behaves like GNU as under `.set
noreorder`, every branch keeps its real delay slot.

| idiom | expansion |
|---|---|
| `nop` / `ehb` | `sll $0, $0, 0` / `3` (NOP p.312, EHB p.175) |
| `move rd, rs` | `addu rd, $0, rs` |
| `b target` | `beq $0, $0, target` (GNU as) |
| `beqz rs, t` / `bnez rs, t` | `beq rs, $0, t` / `bne rs, $0, t` |
| `neg rd[, rs]` / `negu` | `sub rd, $0, rs` / `subu rd, $0, rs` |
| `not rd[, rs]` | `nor rd, rs, $0` |
| `abs rd[, rs]` | `bgez rs, 2 ; move rd, rs (nop if rd = rs) ; sub rd, $0, rs` (GNU as) |
| `blt`/`bge`/`bgt`/`ble`(`u`) `rs, rt, t` | `slt(u) $at, ... ; bne/beq $at, $0, t` |
| `jr rs` / `jr.hb rs` | `jalr $0, rs` / `jalr.hb $0, rs` (Release 6: JR p.207, JR.HB p.208) |
| `bgtc`/`blec`/`bgtuc`/`bleuc rt, rs, t` | `bltc`/`bgec`/`bltuc`/`bgeuc rs, rt, t` (B<cond>C p.83) |

`ssnop` is rejected: "Assemblers targeting specifically Release 6 should reject the SSNOP instruction
with an error" (MD00086 Vol II-A Rev 6.06, SSNOP, p.387; `Asm.rejectedMnemonics`).

(`lui` is the AUI idiom, in `Asm/Int.lean`; `bal`, `nal`, `pause` are real instructions.)

**Macros** need the operand values: `li rt, v` is `addiu rt, $0, v` for -32768..-1, `ori rt, $0,
v` for 0..65535, else `aui $at, $0, hi16 ; ori rt, $at, lo16`; `la rt, label[±const]` is always
the two-word form (pass 1 reserves two words before labels are known).
-/

namespace Asm

/-- A text idiom: operands and line to the statements it stands for. -/
abbrev Idiom := List String → Nat → Except AsmError (List (String × List String))

/-- An idiom with exactly the operand shapes `f` accepts. -/
def idiom (name syn : String) (f : List String → Option (List (String × List String))) : Idiom :=
  fun ops line =>
    match f ops with
    | some r => pure r
    | none => throw (.badOperand s!"{name} expects '{syn}'" line)

/-- `slt(u) $at, a, b ; br $at, $0, target`, operands swapped for `bgt`/`ble`. -/
def cmpBranch (name setOp brOp : String) (swap : Bool) : Idiom :=
  idiom name "rs, rt, target" fun
    | [rs, rt, l] => some [(setOp, if swap then ["$at", rt, rs] else ["$at", rs, rt]),
                           (brOp, ["$at", "$0", l])]
    | _ => none

/-- GNU as's branch-over `abs`. -/
def absIdiom : Idiom := fun ops line => do
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

/-- A one- or two-register unary idiom `name rd[, rs]` ↦ `op` with `args rd rs`. -/
def unaryIdiom (name op : String) (args : String → String → List String) : Idiom :=
  idiom name "rd, rs" fun
    | [rd, rs] => some [(op, args rd rs)]
    | [rd] => some [(op, args rd rd)]
    | _ => none

/-- The no-operand `sll $0, $0, sa` hints. -/
def sllHint (name sa : String) : Idiom :=
  idiom name "" fun
    | [] => some [("sll", ["$0", "$0", sa])]
    | _ => none

/-- `name a, b, target` ↦ `base b, a, target`: an assembly idiom with the two registers reversed. -/
def reversedOperands (name base : String) : Idiom :=
  idiom name "rt, rs, target" fun
    | [rt, rs, l] => some [(base, [rs, rt, l])]
    | _ => none

/-- **The reversed-operand compact branches** (MD00086 Vol II-A Rev 6.06, B<cond>C, p.83: "Assembly
idioms with reversed operands for signed/unsigned compare-and-branch: BGTC rt, rs, offset; BLEC rt, rs,
offset; BGTUC rt, rs, offset; BLEUC rt, rs, offset"; "BLEC: ... (alias for BGEC)", "BGTC: ... (alias for
BLTC)", "BLEUC: ... (alias for BGEUC)", "BGTUC: ... (alias for BLTUC)"). The written first operand is
the instruction's `rt`, the second its `rs`: `bgtc a, b, t` branches if `a > b`, which is `bltc b, a, t`
(`GPR[rs] < GPR[rt]`). llvm-mc 21 (`-mcpu=mips32r6`) rejects these four mnemonics, so they are checked
by `Tests/AsmTests.lean` against the instruction they stand for, not by `tests/oracle/encodings.list`. -/
def reversedCompactIdioms : List (String × Idiom) :=
  [ ("bgtc",  reversedOperands "bgtc" "bltc"),
    ("blec",  reversedOperands "blec" "bgec"),
    ("bgtuc", reversedOperands "bgtuc" "bltuc"),
    ("bleuc", reversedOperands "bleuc" "bgeuc") ]

/-- The idiom table. -/
def idiomTable : List (String × Idiom) :=
  [ ("nop", sllHint "nop" "0"),
    ("ehb", sllHint "ehb" "3"),
    ("move", idiom "move" "rd, rs" fun | [rd, rs] => some [("addu", [rd, "$0", rs])] | _ => none),
    ("b", idiom "b" "target" fun | [l] => some [("beq", ["$0", "$0", l])] | _ => none),
    ("beqz", idiom "beqz" "rs, target" fun | [rs, l] => some [("beq", [rs, "$0", l])] | _ => none),
    ("bnez", idiom "bnez" "rs, target" fun | [rs, l] => some [("bne", [rs, "$0", l])] | _ => none),
    ("neg", unaryIdiom "neg" "sub" fun rd rs => [rd, "$0", rs]),
    ("negu", unaryIdiom "negu" "subu" fun rd rs => [rd, "$0", rs]),
    ("not", unaryIdiom "not" "nor" fun rd rs => [rd, rs, "$0"]),
    ("abs", absIdiom),
    ("blt", cmpBranch "blt" "slt" "bne" false),
    ("bge", cmpBranch "bge" "slt" "beq" false),
    ("bgt", cmpBranch "bgt" "slt" "bne" true),
    ("ble", cmpBranch "ble" "slt" "beq" true),
    ("bltu", cmpBranch "bltu" "sltu" "bne" false),
    ("bgeu", cmpBranch "bgeu" "sltu" "beq" false),
    ("bgtu", cmpBranch "bgtu" "sltu" "bne" true),
    ("bleu", cmpBranch "bleu" "sltu" "beq" true),
    ("jr", idiom "jr" "rs" fun | [rs] => some [("jalr", ["$0", rs])] | _ => none),
    ("jr.hb", idiom "jr.hb" "rs" fun | [rs] => some [("jalr.hb", ["$0", rs])] | _ => none) ] ++
  reversedCompactIdioms

/-- The idioms whose expansion goes through `$at` (rejected under `.set noat`). -/
def atIdioms : List String := ["blt", "bge", "bgt", "ble", "bltu", "bgeu", "bgtu", "bleu"]

/-- One rewriting step: the expansion of an idiom, or the statement itself. -/
def expandOnce (name : String) (ops : List String) (line : Nat) :
    Except AsmError (List (String × List String)) :=
  match idiomTable.find? (·.1 == name) with
  | some (_, f) => f ops line
  | none => pure [(name, ops)]

/-- Rewrite one statement into the table-level statements it stands for (itself if it is not an
idiom). Depends only on the text, never on label addresses. Idioms expand into at most one further
level of idioms (`abs` uses `move`/`nop`), so two steps reach table level. -/
def expandIdiom (name : String) (ops : List String) (line : Nat) :
    Except AsmError (List (String × List String)) := do
  let first ← expandOnce name ops line
  let mut out := []
  for (m, o) in first do
    out := out ++ (← expandOnce m o line)
  pure out

-- ====================================================================
-- Macros: `li`, `la`
-- ====================================================================

/-- A macro: its word count from the text alone (pass 1) and its instructions (pass 2). -/
structure Macro where
  size : List String → Nat → Except AsmError Nat
  gen : Ctx → List String → Except AsmError (List Instruction)

/-- `$at` (register 1), the scratch register of the two-word `li`/`la` (MARS convention). -/
def atW : W32 := 1#32

/-- The general two-word load of a 32-bit value: `aui $at, $0, hi16 ; ori rt, $at, lo16`. -/
def loadWordPair (rt : W32) (v : W32) : List Instruction :=
  [.aui 0#32 atW (v >>> 16), .ori atW rt (v &&& 0xffff#32)]

/-- Words of `li rt, v`: one for a sign-extendable negative or a zero-extendable value, else two. -/
def liWords (v : Int) : Nat :=
  if (-32768 : Int) ≤ v ∧ v ≤ 65535 then 1 else 2

/-- The value operand of `li` (-2^31..2^32-1). -/
def liValue (tok : String) (line : Nat) : Except AsmError Int := do
  let v ← parseImmediate tok line
  checkRange "li value" (-2147483648) 4294967295 v line
  pure v

/-- `li rt, v`. -/
def liMacro : Macro where
  size ops line :=
    match ops with
    | [_, t] => do pure (liWords (← liValue t line))
    | _ => throw (.badOperand "li expects 'li $reg, imm'" line)
  gen c ops :=
    match ops with
    | [r, t] => do
        let rt ← gpr c r
        let v ← liValue t c.line
        pure <|
          if v < 0 ∧ (-32768 : Int) ≤ v then [.addiu 0#32 rt (immField 16 v)]
          else if (0 : Int) ≤ v ∧ v ≤ 65535 then [.ori 0#32 rt (immField 16 v)]
          else loadWordPair rt (ofInt32 v)
    | _ => badShape c "li $reg, imm"

/-- `la rt, label[±const]`. -/
def laMacro : Macro where
  size ops line :=
    match ops with
    | [_, l] => do
        let (sym, _) ← parseExpr l line
        if sym.isNone then
          throw (.badOperand s!"la requires a label operand (use li for numeric constants): '{l}'" line)
        pure 2
    | _ => throw (.badOperand "la expects 'la $reg, label'" line)
  gen c ops :=
    match ops with
    | [r, l] => do
        let rt ← gpr c r
        let addr ← evalExpr c.labels l c.line
        checkRange "la address" 0 4294967295 addr c.line
        pure (loadWordPair rt (ofInt32 addr))
    | _ => badShape c "la $reg, label"

/-- The macro table. -/
def macroTable : List (String × Macro) := [("li", liMacro), ("la", laMacro)]

end Asm
