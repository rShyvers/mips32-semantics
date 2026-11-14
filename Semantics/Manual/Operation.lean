import Semantics.Manual.Ops.IntArith
import Semantics.Manual.Ops.Shift
import Semantics.Manual.Ops.MulDiv
import Semantics.Manual.Ops.BitOps
import Semantics.Manual.Ops.Immediate
import Semantics.Manual.Ops.Memory
import Semantics.Manual.Ops.Unaligned
import Semantics.Manual.Ops.Branch
import Semantics.Manual.Ops.BranchLikely
import Semantics.Manual.Ops.FpuArith
import Semantics.Manual.Ops.Cp0

/-!
# Manual.Operation — the Operation section of each instruction

One arm per `Instruction` constructor, naming the transcribed Operation of its manual page
(`Semantics/Manual/Ops/*.lean`). Sub-wave 7A covers the pilot instructions; `none` marks a
constructor whose page is not transcribed yet (7B makes this total).
-/

namespace Manual

/-- **The Operation of instruction `i`** (`none`: not transcribed yet). -/
def Operation : Instruction → Option (Pseudo Unit)
  | .add rs rt rd => some (Ops.ADD rs rt rd)
  | .lw base rt off => some (Ops.LW base rt off)
  | .sw base rt off => some (Ops.SW base rt off)
  | .lwl base rt off => some (Ops.LWL base rt off)
  | .beq rs rt off => some (Ops.BEQ rs rt off)
  | .beql rs rt off => some (Ops.BEQL rs rt off)
  | .addS fd fs ft => some (Ops.ADD_S fd fs ft)
  | .mtc0 rt rd sel => some (Ops.MTC0 rt rd sel)
  -- 7B S1 integer ALU: begin
  | .addu rs rt rd => some (Ops.ADDU rs rt rd)
  | .sub rs rt rd => some (Ops.SUB rs rt rd)
  | .subu rs rt rd => some (Ops.SUBU rs rt rd)
  | .and rs rt rd => some (Ops.AND rs rt rd)
  | .or rs rt rd => some (Ops.OR rs rt rd)
  | .xor rs rt rd => some (Ops.XOR rs rt rd)
  | .nor rs rt rd => some (Ops.NOR rs rt rd)
  | .slt rs rt rd => some (Ops.SLT rs rt rd)
  | .sltu rs rt rd => some (Ops.SLTU rs rt rd)
  | .movn rs rt rd => some (Ops.MOVN rs rt rd)
  | .movz rs rt rd => some (Ops.MOVZ rs rt rd)
  | .sll rd rt shamt => some (Ops.SLL rd rt shamt)
  | .srl rd rt shamt => some (Ops.SRL rd rt shamt)
  | .sra rd rt shamt => some (Ops.SRA rd rt shamt)
  | .sllv rd rt rs => some (Ops.SLLV rd rt rs)
  | .srlv rd rt rs => some (Ops.SRLV rd rt rs)
  | .srav rd rt rs => some (Ops.SRAV rd rt rs)
  | .rotr rd rt sa => some (Ops.ROTR rd rt sa)
  | .rotrv rd rt rs => some (Ops.ROTRV rd rt rs)
  | .mult rs rt => some (Ops.MULT rs rt)
  | .multu rs rt => some (Ops.MULTU rs rt)
  | .div rs rt => some (Ops.DIV rs rt)
  | .divu rs rt => some (Ops.DIVU rs rt)
  | .mflo rd => some (Ops.MFLO rd)
  | .mfhi rd => some (Ops.MFHI rd)
  | .mthi rs => some (Ops.MTHI rs)
  | .mtlo rs => some (Ops.MTLO rs)
  | .mul rs rt rd => some (Ops.MUL rs rt rd)
  | .madd rs rt => some (Ops.MADD rs rt)
  | .maddu rs rt => some (Ops.MADDU rs rt)
  | .msub rs rt => some (Ops.MSUB rs rt)
  | .msubu rs rt => some (Ops.MSUBU rs rt)
  | .clo rs rd => some (Ops.CLO rs rd)
  | .clz rs rd => some (Ops.CLZ rs rd)
  | .seb rd rt => some (Ops.SEB rd rt)
  | .seh rd rt => some (Ops.SEH rd rt)
  | .wsbh rd rt => some (Ops.WSBH rd rt)
  | .ext rt rs pos size => some (Ops.EXT rt rs pos size)
  | .ins rt rs pos size => some (Ops.INS rt rs pos size)
  | .addi rs rt imm => some (Ops.ADDI rs rt imm)
  | .addiu rs rt imm => some (Ops.ADDIU rs rt imm)
  | .slti rs rt imm => some (Ops.SLTI rs rt imm)
  | .sltiu rs rt imm => some (Ops.SLTIU rs rt imm)
  | .andi rs rt imm => some (Ops.ANDI rs rt imm)
  | .ori rs rt imm => some (Ops.ORI rs rt imm)
  | .xori rs rt imm => some (Ops.XORI rs rt imm)
  | .lui rt imm => some (Ops.LUI rt imm)
  -- 7B S1 integer ALU: end
  | _ => none

end Manual
