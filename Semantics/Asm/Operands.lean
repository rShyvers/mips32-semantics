import Std.Data.HashMap.Basic
import Semantics.Instruction
import Semantics.Asm.Expr

/-!
# Asm.Operands — operand shapes, the combinators every encoder table is built from

An instruction-family table (`Asm/Int.lean`, `Asm/Memory.lean`, `Asm/Branch.lean`,
`Asm/System.lean`, `Asm/Fpu.lean`) maps a mnemonic to an `Enc`: a function from the operand
tokens (and the label table and address, `Ctx`) to the `Instruction` it denotes. The word is then
the model's own `encode` (`Instruction.lean`), so the assembler can only emit the Release 6
encodings the decoder accepts. Every encoder here is one *operand shape* (`rd, rs, rt`,
`rt, offset(base)`, ...) parameterised by the constructor; a table entry is one line.
-/

namespace Asm

/-- What an encoder may look at besides its operands: the resolved labels (pass 2), the address
of the instruction (branch and jump displacements), the mnemonic and the source line (errors). -/
structure Ctx where
  labels : Std.HashMap String W32
  addr : W32
  name : String
  line : Nat

/-- An encoder: operand tokens to one machine instruction. -/
abbrev Enc := Ctx → List String → Except AsmError Instruction

/-- An encoder table, keyed by mnemonic. -/
abbrev EncTable := List (String × Enc)

/-- The wrong number/shape of operands for `c.name`; `syn` is the expected syntax. -/
def badShape (c : Ctx) (syn : String) : Except AsmError α :=
  throw (.badOperand s!"{c.name} expects '{syn}'" c.line)

/-- A register number as an instruction field. -/
def fld (n : Nat) : W32 := natToW32 n

/-- The low `bits` bits of an in-range (possibly negative) value: the raw immediate field. -/
def immField (bits : Nat) (v : Int) : W32 := ofInt32 v &&& natToW32 (2 ^ bits - 1)

/-- GPR operand. -/
def gpr (c : Ctx) (t : String) : Except AsmError W32 := do pure (fld (← parseRegister t c.line))

/-- FPR operand (`$f0`..`$f31`). -/
def fpr (c : Ctx) (t : String) : Except AsmError W32 := do pure (fld (← parseFpRegister t c.line))

/-- A numeric operand in `lo..hi`, as the raw `bits`-bit field. -/
def immIn (c : Ctx) (what : String) (bits : Nat) (lo hi : Int) (t : String) :
    Except AsmError W32 := do
  let v ← parseImmediate t c.line
  checkRange s!"{c.name} {what}" lo hi v c.line
  pure (immField bits v)

/-- A signed 16-bit immediate. -/
def simm16 (c : Ctx) (t : String) : Except AsmError W32 := immIn c "immediate" 16 (-32768) 32767 t

/-- An unsigned 16-bit immediate. -/
def uimm16 (c : Ctx) (t : String) : Except AsmError W32 := immIn c "immediate" 16 0 65535 t

/-- An optional trailing code-like operand (`code`, `stype`, `sel`, ...) in `0..maxCode`,
default 0. -/
def optCode (c : Ctx) (what : String) (maxCode : Int) : List String → Except AsmError W32
  | [] => pure 0#32
  | [t] => do pure (fld (← parseCode c.name what maxCode t c.line))
  | _ => throw (.badOperand s!"{c.name}: too many operands" c.line)

-- ====================================================================
-- Labels and displacements
-- ====================================================================

def resolveLabel (labels : Std.HashMap String W32) (tok : String) (lineNo : Nat) :
    Except AsmError W32 :=
  match labels.get? tok with
  | some addr => pure addr
  | none => throw (.undefinedLabel s!"undefined label '{tok}'" lineNo)

/-- Evaluate a `label`, `label±const` or pure constant operand to an exact (unwrapped) integer. -/
def evalExpr (labels : Std.HashMap String W32) (tok : String) (lineNo : Nat) :
    Except AsmError Int := do
  let (sym, k) ← parseExpr tok lineNo
  match sym with
  | none => pure k
  | some l => do
      let a ← resolveLabel labels l lineNo
      pure ((a.toNat : Int) + k)

/-- Branch offset field (in words, relative to the delay slot) as the raw 16-bit field. A purely
numeric operand is the offset itself (MARS convention); a `label`/`label±const` operand is an
address, which must be a whole number of words away from `pc + 4` and within the signed 16-bit
word range. -/
def branchOff (c : Ctx) (tgt : String) : Except AsmError W32 := do
  let (sym, k) ← parseExpr tgt c.line
  match sym with
  | none => do
      checkRange "branch offset" (-32768) 32767 k c.line
      pure (immField 16 k)
  | some l => do
      let base ← resolveLabel c.labels l c.line
      let diff : Int := (base.toNat : Int) + k - ((c.addr.toNat : Int) + 4)
      if diff % 4 ≠ 0 then
        throw (.badOperand s!"branch target '{tgt}' is not word-aligned relative to the branch" c.line)
      let w := diff / 4
      if w < -32768 ∨ w > 32767 then
        throw (.badOperand s!"branch target '{tgt}' out of range ({w} words; limit -32768..32767)" c.line)
      pure (immField 16 w)

/-- `j`/`jal` target field: the operand is an absolute address (numeric, `label`, or
`label±const`), word-aligned and in the same 256MB region as the delay slot (`pc + 4`), since
only the low 28 bits are encoded. -/
def jumpTarget (c : Ctx) (tgt : String) : Except AsmError W32 := do
  let target ← evalExpr c.labels tgt c.line
  if target < 0 ∨ target ≥ 4294967296 then
    throw (.badImmediate s!"jump target outside the 32-bit address space: {target}" c.line)
  let t := target.toNat
  if t % 4 ≠ 0 then throw (.badOperand s!"jump target must be word-aligned: '{tgt}'" c.line)
  let slot := (c.addr.toNat + 4) % 4294967296
  if t / 268435456 ≠ slot / 268435456 then
    throw (.badOperand
      s!"jump target '{tgt}' is outside the 256MB region of the delay slot (not encodable in j/jal)" c.line)
  pure (natToW32 ((t % 268435456) / 4))

-- ====================================================================
-- Operand shapes (each takes the constructor, by named field)
-- ====================================================================

/-- No operands. -/
def none0 (i : Instruction) : Enc := fun c ops =>
  match ops with
  | [] => pure i
  | _ => throw (.badOperand s!"{c.name} takes no operands" c.line)

/-- `rd, rs, rt`. -/
def rdRsRt (mk : (rd rs rt : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [d, s, t] => do pure (mk (← gpr c d) (← gpr c s) (← gpr c t))
  | _ => badShape c "rd, rs, rt"

/-- `rd, rt, sa` (constant shift/rotate amount 0..31). -/
def rdRtSa (mk : (rd rt sa : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [d, t, a] => do pure (mk (← gpr c d) (← gpr c t) (← immIn c "shift amount" 5 0 31 a))
  | _ => badShape c "rd, rt, sa"

/-- `rd, rt, rs` (variable shift/rotate). -/
def rdRtRs (mk : (rd rt rs : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [d, t, s] => do pure (mk (← gpr c d) (← gpr c t) (← gpr c s))
  | _ => badShape c "rd, rt, rs"

/-- Two GPRs, `first, second` (`clo rd, rs`; `seb rd, rt`; `rdpgpr rd, rt`). -/
def gpr2 (syn : String) (mk : W32 → W32 → Instruction) : Enc := fun c ops =>
  match ops with
  | [a, b] => do pure (mk (← gpr c a) (← gpr c b))
  | _ => badShape c syn

/-- `rt, rs, pos, size` (EXT/INS: `pos` 0..31, `size` 1..32, `pos + size ≤ 32`; the field
packing is `encode`'s). -/
def bitField (mk : (rt rs pos size : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [t, s, p, z] => do
      let rt ← gpr c t
      let rs ← gpr c s
      let pos ← parseImmediate p c.line
      let size ← parseImmediate z c.line
      if pos < 0 ∨ pos > 31 then throw (.badImmediate s!"{c.name} pos out of range (0-31)" c.line)
      if size < 1 ∨ size > 32 then throw (.badImmediate s!"{c.name} size out of range (1-32)" c.line)
      if pos + size > 32 then throw (.badImmediate s!"{c.name} pos + size must be <= 32" c.line)
      pure (mk rt rs (immField 5 pos) (natToW32 size.toNat))
  | _ => badShape c "rt, rs, pos, size"

/-- `rt, rs, imm` with the immediate parsed by `imm`. -/
def rtRsImm (imm : Ctx → String → Except AsmError W32) (mk : (rs rt imm : W32) → Instruction) :
    Enc := fun c ops =>
  match ops with
  | [t, s, i] => do pure (mk (← gpr c s) (← gpr c t) (← imm c i))
  | _ => badShape c "rt, rs, imm"

/-- `rt, offset(base)` with an offset of `bits` bits (signed); `reg` parses `rt` (GPR or FPR). -/
def memOp (bits : Nat) (reg : Ctx → String → Except AsmError W32)
    (mk : (base rt off : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [t, m] => do
      let rt ← reg c t
      let lim : Int := 2 ^ (bits - 1)
      let (off, base) ← parseMemOperandIn (-lim) (lim - 1) m c.line
      pure (mk (fld base) rt (immField bits off))
  | _ => badShape c "rt, offset(base)"

/-- `hint, offset(base)` (PREF; `hint` 0..31, 9-bit offset). -/
def hintMem (bits : Nat) (mk : (base hint off : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [h, m] => do
      let hint ← parseCode c.name "hint" 31 h c.line
      let lim : Int := 2 ^ (bits - 1)
      let (off, base) ← parseMemOperandIn (-lim) (lim - 1) m c.line
      pure (mk (fld base) (fld hint) (immField bits off))
  | _ => badShape c "hint, offset(base)"

/-- `offset(base)` alone (SYNCI). -/
def memOnly (mk : (base off : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [m] => do
      let (off, base) ← parseMemOperand m c.line
      pure (mk (fld base) (immField 16 off))
  | _ => badShape c "offset(base)"

/-- `rs, rt, target`. -/
def brRsRt (mk : (rs rt off : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [s, t, l] => do pure (mk (← gpr c s) (← gpr c t) (← branchOff c l))
  | _ => badShape c "rs, rt, target"

/-- `rs, target`. -/
def brRs (mk : (rs off : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [s, l] => do pure (mk (← gpr c s) (← branchOff c l))
  | _ => badShape c "rs, target"

/-- `target` alone (BAL). -/
def brOnly (mk : (off : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [l] => do pure (mk (← branchOff c l))
  | _ => badShape c "target"

/-- `target` of a J-type jump. -/
def jumpOp (mk : (target : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [l] => do pure (mk (← jumpTarget c l))
  | _ => badShape c "target"

/-- `rd, rs` or `rs` (`rd` defaults to 31: JALR/JALR.HB). -/
def jalrOp (mk : (rs rd : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [d, s] => do pure (mk (← gpr c s) (← gpr c d))
  | [s] => do pure (mk (← gpr c s) 31#32)
  | _ => badShape c "rd, rs' or 'rs"

/-- `rs, rt[, code]` (register traps; 10-bit code). -/
def trapOp (mk : (rs rt code : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | s :: t :: rest => do pure (mk (← gpr c s) (← gpr c t) (← optCode c "code" 1023 rest))
  | _ => badShape c "rs, rt[, code]"

/-- `[code]`: one optional code-like operand in `0..maxCode`. -/
def optOp (what : String) (maxCode : Int) (mk : W32 → Instruction) : Enc := fun c ops => do
  pure (mk (← optCode c what maxCode ops))

/-- `[rt]` (DI/EI; default `$0`). -/
def optGpr (mk : W32 → Instruction) : Enc := fun c ops =>
  match ops with
  | [] => pure (mk 0#32)
  | [t] => do pure (mk (← gpr c t))
  | _ => badShape c "[rt]"

/-- `rt, rd[, sel]` with `rd` a coprocessor register number (`$N` or `N`) and `sel` 0..7
(MFC0/MTC0, RDHWR). -/
def copSel (what : String) (mk : (rt rd sel : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | t :: d :: rest => do
      let rt ← gpr c t
      let rd ← parseCopRegister what d c.line
      pure (mk rt (fld rd) (← optCode c "sel" 7 rest))
  | _ => badShape c "rt, rd[, sel]"

end Asm
