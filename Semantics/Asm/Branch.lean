import Semantics.Asm.Operands

/-!
# Asm.Branch — branches and jumps (all with a delay slot)

Release 6 keeps BEQ/BNE/BLEZ/BGTZ/BLTZ/BGEZ, BAL and NAL (the `rs = 0` cases of the removed
BGEZAL/BLTZAL; BAL p.50, NAL p.306), J/JAL and JALR/JALR.HB. `jr rs`/`jr.hb rs` are idioms for
`jalr $0, rs`/`jalr.hb $0, rs` (JR p.207, JR.HB p.208; `Asm/Pseudo.lean`). A numeric branch
operand is the word offset itself; a label operand is a target address.
-/

namespace Asm

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
    ("jalr.hb", jalrOp .jalrHb) ]

end Asm
