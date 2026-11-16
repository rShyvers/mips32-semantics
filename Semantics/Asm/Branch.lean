import Semantics.Asm.Operands

/-!
# Asm.Branch — branches and jumps

Release 6 keeps BEQ/BNE/BLEZ/BGTZ/BLTZ/BGEZ, BAL and NAL (the `rs = 0` cases of the removed
BGEZAL/BLTZAL; BAL p.50, NAL p.306), J/JAL and JALR/JALR.HB, all with a delay slot. `jr rs`/`jr.hb rs`
are idioms for `jalr $0, rs`/`jalr.hb $0, rs` (JR p.207, JR.HB p.208; `Asm/Pseudo.lean`). A numeric
branch operand is the word offset itself; a label operand is a target address.

**The Release 6 compact branches and jumps** (MD00086 Vol II-A Rev 6.06, BC p.53, BALC
p.52, B<cond>C p.82-85, B{LE,GE,GT,LT,EQ,NE}ZALC p.77-79, BOVC/BNVC p.107, JIC p.205, JIALC p.203)
share primary opcodes and are told apart by the `rs`/`rt` fields (Table A.26, p.464), so a form whose
registers would select another instruction is an error: `beqc`/`bnec` need two different nonzero
registers (written in either order: equality is symmetric, the word has `rs < rt`), `bltc`/`bgec`/
`bltuc`/`bgeuc` two different nonzero registers, the compare-with-zero and branch-and-link forms a
nonzero register; `bovc`/`bnvc` take the registers in either order (the word has `rs >= rt`; the sum
is symmetric). The offset is relative to the instruction after the branch, 16 bits (21 for
`beqzc`/`bnezc`, 26 for `bc`/`balc`); `jic`/`jialc` take a signed 16-bit byte offset added to the
register.
-/

namespace Asm

/-- A compact branch offset of `bits` bits (in words, relative to `pc + 4`), as the raw field: a
numeric operand is the offset itself, a `label`/`label±const` an address (`branchOff`'s rules). -/
def branchOffBits (c : Ctx) (bits : Nat) (tgt : String) : Except AsmError W32 := do
  let lim : Int := 2 ^ (bits - 1)
  let (sym, k) ← parseExpr tgt c.line
  match sym with
  | none => do
      checkRange "branch offset" (-lim) (lim - 1) k c.line
      pure (immField bits k)
  | some l => do
      let base ← resolveLabel c.labels l c.line
      let diff : Int := (base.toNat : Int) + k - ((c.addr.toNat : Int) + 4)
      if diff % 4 ≠ 0 then
        throw (.badOperand s!"branch target '{tgt}' is not word-aligned relative to the branch" c.line)
      let w := diff / 4
      if w < -lim ∨ w > lim - 1 then
        throw (.badOperand s!"branch target '{tgt}' out of range ({w} words; limit {-lim}..{lim - 1})" c.line)
      pure (immField bits w)

/-- A GPR operand that must not be `$0` (its zero value selects another instruction). -/
def gprNZ (c : Ctx) (t : String) : Except AsmError W32 := do
  let r ← gpr c t
  if r == 0#32 then throw (.badOperand s!"{c.name}: $zero is not allowed here (Table A.26)" c.line)
  pure r

/-- `target` with a 26-bit offset (BC, BALC). -/
def cbTarget (mk : W32 → Instruction) : Enc := fun c ops =>
  match ops with
  | [l] => do pure (mk (← branchOffBits c 26 l))
  | _ => badShape c "target"

/-- `rs, rt, target`, symmetric (BEQC, BNEC): two different nonzero registers, put in `rs < rt`
order. -/
def cbSym (mk : (rs rt off : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [s, t, l] => do
      let a ← gprNZ c s
      let b ← gprNZ c t
      if a == b then throw (.badOperand s!"{c.name}: registers must be different" c.line)
      let off ← branchOffBits c 16 l
      pure (if a.toNat < b.toNat then mk a b off else mk b a off)
  | _ => badShape c "rs, rt, target"

/-- `rs, rt, target` (BLTC, BGEC, BLTUC, BGEUC): two different nonzero registers. -/
def cbCmp (mk : (rs rt off : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [s, t, l] => do
      let a ← gprNZ c s
      let b ← gprNZ c t
      if a == b then throw (.badOperand s!"{c.name}: registers must be different" c.line)
      pure (mk a b (← branchOffBits c 16 l))
  | _ => badShape c "rs, rt, target"

/-- `rs, rt, target` (BOVC, BNVC): any registers, put in `rs >= rt` order. -/
def cbOvf (mk : (rs rt off : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [s, t, l] => do
      let a ← gpr c s
      let b ← gpr c t
      let off ← branchOffBits c 16 l
      pure (if b.toNat ≤ a.toNat then mk a b off else mk b a off)
  | _ => badShape c "rs, rt, target"

/-- `reg, target` with a nonzero register and a `bits`-bit offset (the compare-with-zero forms). -/
def cbZero (bits : Nat) (mk : (r off : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [r, l] => do pure (mk (← gprNZ c r) (← branchOffBits c bits l))
  | _ => badShape c "reg, target"

/-- `rt, offset` (JIC, JIALC): a signed 16-bit byte offset. -/
def cbJump (mk : (rt off : W32) → Instruction) : Enc := fun c ops =>
  match ops with
  | [t, o] => do pure (mk (← gpr c t) (← simm16 c o))
  | _ => badShape c "rt, offset"

/-- The Release 6 compact branches and jumps (module doc). -/
def compactBranchTable : EncTable :=
  [ ("bc",      cbTarget .bc),
    ("balc",    cbTarget .balc),
    ("beqc",    cbSym .beqc),
    ("bnec",    cbSym .bnec),
    ("bltc",    cbCmp .bltc),
    ("bgec",    cbCmp .bgec),
    ("bltuc",   cbCmp .bltuc),
    ("bgeuc",   cbCmp .bgeuc),
    ("blezc",   cbZero 16 .blezc),
    ("bgezc",   cbZero 16 .bgezc),
    ("bgtzc",   cbZero 16 .bgtzc),
    ("bltzc",   cbZero 16 .bltzc),
    ("beqzc",   cbZero 21 .beqzc),
    ("bnezc",   cbZero 21 .bnezc),
    ("blezalc", cbZero 16 .blezalc),
    ("bgezalc", cbZero 16 .bgezalc),
    ("bgtzalc", cbZero 16 .bgtzalc),
    ("bltzalc", cbZero 16 .bltzalc),
    ("beqzalc", cbZero 16 .beqzalc),
    ("bnezalc", cbZero 16 .bnezalc),
    ("bovc",    cbOvf .bovc),
    ("bnvc",    cbOvf .bnvc),
    ("jic",     cbJump .jic),
    ("jialc",   cbJump .jialc) ]

/-- Branches and jumps. -/
def branchTable : EncTable :=
  [ ("beq",  brRsRt .beq),
    ("bne",  brRsRt .bne),
    ("blez", brRs .blez),
    ("bgtz", brRs .bgtz),
    ("bltz", brRs .bltz),
    ("bgez", brRs .bgez),
    ("bal",  brOnly .bal),
    ("nal",  none0 (.nal 0#32)),
    ("j",    jumpOp .j),
    ("jal",  jumpOp .jal),
    ("jalr",    jalrOp .jalr),
    ("jalr.hb", jalrOp .jalrHb) ] ++
  compactBranchTable

end Asm
