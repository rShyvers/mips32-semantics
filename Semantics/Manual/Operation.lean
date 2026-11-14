import Semantics.Manual.Ops.IntArith
import Semantics.Manual.Ops.Shift
import Semantics.Manual.Ops.MulDiv
import Semantics.Manual.Ops.BitOps
import Semantics.Manual.Ops.Immediate
import Semantics.Manual.Ops.Memory
import Semantics.Manual.Ops.Unaligned
import Semantics.Manual.Ops.Atomic
import Semantics.Manual.Ops.Trap
import Semantics.Manual.Ops.Syscall
import Semantics.Manual.Ops.Branch
import Semantics.Manual.Ops.BranchLikely
import Semantics.Manual.Ops.FpuArith
import Semantics.Manual.Ops.Cp0
-- 7B S3 control + system
import Semantics.Manual.Ops.Jump
import Semantics.Manual.Ops.System
-- end 7B S3
-- 7B S4 FPU
import Semantics.Manual.Ops.FpuBranch
import Semantics.Manual.Ops.FpuCompare
import Semantics.Manual.Ops.FpuControl
import Semantics.Manual.Ops.FpuConvert
import Semantics.Manual.Ops.FpuMemory
import Semantics.Manual.Ops.FpuMove

/-!
# Manual.Operation — the Operation section of each instruction

One arm per `Instruction` constructor, naming the transcribed Operation of its manual page
(`Semantics/Manual/Ops/*.lean`). Every constructor has a transcribed page since 7B, so every arm
is `some`; the `Option` type is kept from 7A, when `none` marked an untranscribed page (making it
total would restate every refinement theorem; `docs/MANUAL-SPEC.md` I.5, decision 1).
-/

namespace Manual

/-- **The Operation of instruction `i`** (`some` for every constructor; see the module doc). -/
def Operation : Instruction → Option (Pseudo Unit)
  | .add rs rt rd => some (Ops.ADD rs rt rd)
  | .lw base rt off => some (Ops.LW base rt off)
  | .sw base rt off => some (Ops.SW base rt off)
  | .lwl base rt off => some (Ops.LWL base rt off)
  | .beq rs rt off => some (Ops.BEQ rs rt off)
  | .beql rs rt off => some (Ops.BEQL rs rt off)
  | .addS fd fs ft => some (Ops.ADD_S fd fs ft)
  | .mtc0 rt rd sel => some (Ops.MTC0 rt rd sel)
  -- 7B S3 control + system
  | .bne rs rt off => some (Ops.BNE rs rt off)
  | .blez rs off => some (Ops.BLEZ rs off)
  | .bgtz rs off => some (Ops.BGTZ rs off)
  | .bltz rs off => some (Ops.BLTZ rs off)
  | .bgez rs off => some (Ops.BGEZ rs off)
  | .bltzal rs off => some (Ops.BLTZAL rs off)
  | .bgezal rs off => some (Ops.BGEZAL rs off)
  | .bnel rs rt off => some (Ops.BNEL rs rt off)
  | .blezl rs off => some (Ops.BLEZL rs off)
  | .bgtzl rs off => some (Ops.BGTZL rs off)
  | .bltzl rs off => some (Ops.BLTZL rs off)
  | .bgezl rs off => some (Ops.BGEZL rs off)
  | .bltzall rs off => some (Ops.BLTZALL rs off)
  | .bgezall rs off => some (Ops.BGEZALL rs off)
  | .j target => some (Ops.J target)
  | .jal target => some (Ops.JAL target)
  | .jr rs => some (Ops.JR rs)
  | .jalr rs rd => some (Ops.JALR rs rd)
  | .jrHb rs => some (Ops.JR_HB rs)
  | .jalrHb rs rd => some (Ops.JALR_HB rs rd)
  | .mfc0 rt rd sel => some (Ops.MFC0 rt rd sel)
  | .di rt => some (Ops.DI rt)
  | .ei rt => some (Ops.EI rt)
  | .eret => some Ops.ERET
  | .wait code => some (Ops.WAIT code)
  | .rdpgpr rd rt => some (Ops.RDPGPR rd rt)
  | .wrpgpr rd rt => some (Ops.WRPGPR rd rt)
  | .rdhwr rt rd => some (Ops.RDHWR rt rd)
  -- end 7B S3
  -- 7B S2 memory/atomic/trap/syscall
  | .lb base rt off => some (Ops.LB base rt off)
  | .lbu base rt off => some (Ops.LBU base rt off)
  | .lh base rt off => some (Ops.LH base rt off)
  | .lhu base rt off => some (Ops.LHU base rt off)
  | .sb base rt off => some (Ops.SB base rt off)
  | .sh base rt off => some (Ops.SH base rt off)
  | .pref base hint off => some (Ops.PREF base hint off)
  | .sync stype => some (Ops.SYNC stype)
  | .synci base off => some (Ops.SYNCI base off)
  | .ll base rt off => some (Ops.LL base rt off)
  | .sc base rt off => some (Ops.SC base rt off)
  | .lwr base rt off => some (Ops.LWR base rt off)
  | .swl base rt off => some (Ops.SWL base rt off)
  | .swr base rt off => some (Ops.SWR base rt off)
  | .teq rs rt code => some (Ops.TEQ rs rt code)
  | .tne rs rt code => some (Ops.TNE rs rt code)
  | .tlt rs rt code => some (Ops.TLT rs rt code)
  | .tge rs rt code => some (Ops.TGE rs rt code)
  | .tltu rs rt code => some (Ops.TLTU rs rt code)
  | .tgeu rs rt code => some (Ops.TGEU rs rt code)
  | .teqi rs imm => some (Ops.TEQI rs imm)
  | .tnei rs imm => some (Ops.TNEI rs imm)
  | .tgei rs imm => some (Ops.TGEI rs imm)
  | .tgeiu rs imm => some (Ops.TGEIU rs imm)
  | .tlti rs imm => some (Ops.TLTI rs imm)
  | .tltiu rs imm => some (Ops.TLTIU rs imm)
  | .syscall code => some (Ops.SYSCALL code)
  | .break code => some (Ops.BREAK code)
  -- 7B S4 FPU
  | .mfc1 rt fs => some (Ops.MFC1 rt fs)
  | .mtc1 rt fs => some (Ops.MTC1 rt fs)
  | .mfhc1 rt fs => some (Ops.MFHC1 rt fs)
  | .mthc1 rt fs => some (Ops.MTHC1 rt fs)
  | .cfc1 rt fs => some (Ops.CFC1 rt fs)
  | .ctc1 rt fs => some (Ops.CTC1 rt fs)
  | .lwc1 rs ft imm => some (Ops.LWC1 rs ft imm)
  | .swc1 rs ft imm => some (Ops.SWC1 rs ft imm)
  | .ldc1 rs ft imm => some (Ops.LDC1 rs ft imm)
  | .sdc1 rs ft imm => some (Ops.SDC1 rs ft imm)
  | .lwxc1 fd index base => some (Ops.LWXC1 fd index base)
  | .ldxc1 fd index base => some (Ops.LDXC1 fd index base)
  | .swxc1 fs index base => some (Ops.SWXC1 fs index base)
  | .sdxc1 fs index base => some (Ops.SDXC1 fs index base)
  | .prefx hint index base => some (Ops.PREFX hint index base)
  | .subS fd fs ft => some (Ops.SUB_S fd fs ft)
  | .mulS fd fs ft => some (Ops.MUL_S fd fs ft)
  | .divS fd fs ft => some (Ops.DIV_S fd fs ft)
  | .sqrtS fd fs => some (Ops.SQRT_S fd fs)
  | .absS fd fs => some (Ops.ABS_S fd fs)
  | .movS fd fs => some (Ops.MOV_S fd fs)
  | .negS fd fs => some (Ops.NEG_S fd fs)
  | .recipS fd fs => some (Ops.RECIP_S fd fs)
  | .rsqrtS fd fs => some (Ops.RSQRT_S fd fs)
  | .roundWS fd fs => some (Ops.ROUND_W_S fd fs)
  | .truncWS fd fs => some (Ops.TRUNC_W_S fd fs)
  | .ceilWS fd fs => some (Ops.CEIL_W_S fd fs)
  | .floorWS fd fs => some (Ops.FLOOR_W_S fd fs)
  | .cvtWS fd fs => some (Ops.CVT_W_S fd fs)
  | .addD fd fs ft => some (Ops.ADD_D fd fs ft)
  | .subD fd fs ft => some (Ops.SUB_D fd fs ft)
  | .mulD fd fs ft => some (Ops.MUL_D fd fs ft)
  | .divD fd fs ft => some (Ops.DIV_D fd fs ft)
  | .sqrtD fd fs => some (Ops.SQRT_D fd fs)
  | .absD fd fs => some (Ops.ABS_D fd fs)
  | .movD fd fs => some (Ops.MOV_D fd fs)
  | .negD fd fs => some (Ops.NEG_D fd fs)
  | .recipD fd fs => some (Ops.RECIP_D fd fs)
  | .rsqrtD fd fs => some (Ops.RSQRT_D fd fs)
  | .roundWD fd fs => some (Ops.ROUND_W_D fd fs)
  | .truncWD fd fs => some (Ops.TRUNC_W_D fd fs)
  | .ceilWD fd fs => some (Ops.CEIL_W_D fd fs)
  | .floorWD fd fs => some (Ops.FLOOR_W_D fd fs)
  | .cvtWD fd fs => some (Ops.CVT_W_D fd fs)
  | .cvtDS fd fs => some (Ops.CVT_D_S fd fs)
  | .cvtSW fd fs => some (Ops.CVT_S_W fd fs)
  | .cvtDW fd fs => some (Ops.CVT_D_W fd fs)
  | .cvtSD fd fs => some (Ops.CVT_S_D fd fs)
  | .cCondS cond cc fs ft => some (Ops.C_cond_S cond cc fs ft)
  | .cCondD cond cc fs ft => some (Ops.C_cond_D cond cc fs ft)
  | .movfS fd fs cc => some (Ops.MOVF_S fd fs cc)
  | .movtS fd fs cc => some (Ops.MOVT_S fd fs cc)
  | .movnS fd fs rt => some (Ops.MOVN_S fd fs rt)
  | .movzS fd fs rt => some (Ops.MOVZ_S fd fs rt)
  | .movfD fd fs cc => some (Ops.MOVF_D fd fs cc)
  | .movtD fd fs cc => some (Ops.MOVT_D fd fs cc)
  | .movnD fd fs rt => some (Ops.MOVN_D fd fs rt)
  | .movzD fd fs rt => some (Ops.MOVZ_D fd fs rt)
  | .movf rs cc rd => some (Ops.MOVF rs cc rd)
  | .movt rs cc rd => some (Ops.MOVT rs cc rd)
  | .maddS fd fr fs ft => some (Ops.MADD_S fd fr fs ft)
  | .maddD fd fr fs ft => some (Ops.MADD_D fd fr fs ft)
  | .msubS fd fr fs ft => some (Ops.MSUB_S fd fr fs ft)
  | .msubD fd fr fs ft => some (Ops.MSUB_D fd fr fs ft)
  | .nmaddS fd fr fs ft => some (Ops.NMADD_S fd fr fs ft)
  | .nmaddD fd fr fs ft => some (Ops.NMADD_D fd fr fs ft)
  | .nmsubS fd fr fs ft => some (Ops.NMSUB_S fd fr fs ft)
  | .nmsubD fd fr fs ft => some (Ops.NMSUB_D fd fr fs ft)
  | .bc1f cc imm => some (Ops.BC1F cc imm)
  | .bc1t cc imm => some (Ops.BC1T cc imm)
  | .bc1fl cc imm => some (Ops.BC1FL cc imm)
  | .bc1tl cc imm => some (Ops.BC1TL cc imm)
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

end Manual
