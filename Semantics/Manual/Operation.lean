import Semantics.Manual.Ops.IntArith
import Semantics.Manual.Ops.Shift
import Semantics.Manual.Ops.BitOps
import Semantics.Manual.Ops.Immediate
import Semantics.Manual.Ops.Memory
import Semantics.Manual.Ops.Atomic
import Semantics.Manual.Ops.Trap
import Semantics.Manual.Ops.Syscall
import Semantics.Manual.Ops.Branch
import Semantics.Manual.Ops.FpuArith
import Semantics.Manual.Ops.Cp0
-- 7B S3 control + system
import Semantics.Manual.Ops.Jump
import Semantics.Manual.Ops.System
-- end 7B S3
-- 7B S4 FPU
import Semantics.Manual.Ops.FpuControl
import Semantics.Manual.Ops.FpuConvert
import Semantics.Manual.Ops.FpuMemory
import Semantics.Manual.Ops.FpuMove
-- BEGIN R6-4
import Semantics.Manual.Ops.PcRel
-- END R6-4

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
  | .beq rs rt off => some (Ops.BEQ rs rt off)
  | .addS fd fs ft => some (Ops.ADD_S fd fs ft)
  | .mtc0 rt rd sel => some (Ops.MTC0 rt rd sel)
  -- 7B S3 control + system
  | .bne rs rt off => some (Ops.BNE rs rt off)
  | .blez rs off => some (Ops.BLEZ rs off)
  | .bgtz rs off => some (Ops.BGTZ rs off)
  | .bltz rs off => some (Ops.BLTZ rs off)
  | .bgez rs off => some (Ops.BGEZ rs off)
  | .j target => some (Ops.J target)
  | .jal target => some (Ops.JAL target)
  | .jalr rs rd => some (Ops.JALR rs rd)
  | .jalrHb rs rd => some (Ops.JALR_HB rs rd)
  | .mfc0 rt rd sel => some (Ops.MFC0 rt rd sel)
  | .di rt => some (Ops.DI rt)
  | .ei rt => some (Ops.EI rt)
  | .eret => some Ops.ERET
  | .wait code => some (Ops.WAIT code)
  | .rdpgpr rd rt => some (Ops.RDPGPR rd rt)
  | .wrpgpr rd rt => some (Ops.WRPGPR rd rt)
  | .rdhwr rt rd sel => some (Ops.RDHWR rt rd sel)
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
  | .teq rs rt code => some (Ops.TEQ rs rt code)
  | .tne rs rt code => some (Ops.TNE rs rt code)
  | .tlt rs rt code => some (Ops.TLT rs rt code)
  | .tge rs rt code => some (Ops.TGE rs rt code)
  | .tltu rs rt code => some (Ops.TLTU rs rt code)
  | .tgeu rs rt code => some (Ops.TGEU rs rt code)
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
  | .sll rd rt shamt => some (Ops.SLL rd rt shamt)
  | .srl rd rt shamt => some (Ops.SRL rd rt shamt)
  | .sra rd rt shamt => some (Ops.SRA rd rt shamt)
  | .sllv rd rt rs => some (Ops.SLLV rd rt rs)
  | .srlv rd rt rs => some (Ops.SRLV rd rt rs)
  | .srav rd rt rs => some (Ops.SRAV rd rt rs)
  | .rotr rd rt sa => some (Ops.ROTR rd rt sa)
  | .rotrv rd rt rs => some (Ops.ROTRV rd rt rs)
  | .clo rs rd => some (Ops.CLO rs rd)
  | .clz rs rd => some (Ops.CLZ rs rd)
  | .seb rd rt => some (Ops.SEB rd rt)
  | .seh rd rt => some (Ops.SEH rd rt)
  | .wsbh rd rt => some (Ops.WSBH rd rt)
  | .ext rt rs pos size => some (Ops.EXT rt rs pos size)
  | .ins rt rs pos size => some (Ops.INS rt rs pos size)
  | .addiu rs rt imm => some (Ops.ADDIU rs rt imm)
  | .slti rs rt imm => some (Ops.SLTI rs rt imm)
  | .sltiu rs rt imm => some (Ops.SLTIU rs rt imm)
  | .andi rs rt imm => some (Ops.ANDI rs rt imm)
  | .ori rs rt imm => some (Ops.ORI rs rt imm)
  | .xori rs rt imm => some (Ops.XORI rs rt imm)
  -- 7B S1 integer ALU: end
  -- Release 6 (wave R6-1)
  | .aui rs rt imm => some (Ops.AUI rs rt imm)
  | .nal off => some (Ops.NAL off)
  | .bal off => some (Ops.BAL off)
  | .pause => some Ops.PAUSE
  -- BEGIN R6-2
  | .eretnc => some Ops.ERETNC
  | .sigrie code => some (Ops.SIGRIE code)
  | .cache base op off => some (Ops.CACHE base op off)
  -- END R6-2
  -- BEGIN R6-4
  | .mul rs rt rd => some (Ops.MUL rs rt rd)
  | .muh rs rt rd => some (Ops.MUH rs rt rd)
  | .mulu rs rt rd => some (Ops.MULU rs rt rd)
  | .muhu rs rt rd => some (Ops.MUHU rs rt rd)
  | .div rs rt rd => some (Ops.DIV rs rt rd)
  | .mod rs rt rd => some (Ops.MOD rs rt rd)
  | .divu rs rt rd => some (Ops.DIVU rs rt rd)
  | .modu rs rt rd => some (Ops.MODU rs rt rd)
  | .seleqz rs rt rd => some (Ops.SELEQZ rs rt rd)
  | .selnez rs rt rd => some (Ops.SELNEZ rs rt rd)
  | .lsa rs rt rd sa => some (Ops.LSA rs rt rd sa)
  | .align rs rt rd bp => some (Ops.ALIGN rs rt rd bp)
  | .bitswap rd rt => some (Ops.BITSWAP rd rt)
  | .addiupc rs imm => some (Ops.ADDIUPC rs imm)
  | .lwpc rs off => some (Ops.LWPC rs off)
  | .auipc rs imm => some (Ops.AUIPC rs imm)
  | .aluipc rs imm => some (Ops.ALUIPC rs imm)
  -- END R6-4
  -- BEGIN R6-5
  | .cvtLS fd fs => some (Ops.CVT_L_S fd fs)
  | .cvtLD fd fs => some (Ops.CVT_L_D fd fs)
  | .roundLS fd fs => some (Ops.ROUND_L_S fd fs)
  | .roundLD fd fs => some (Ops.ROUND_L_D fd fs)
  | .truncLS fd fs => some (Ops.TRUNC_L_S fd fs)
  | .truncLD fd fs => some (Ops.TRUNC_L_D fd fs)
  | .ceilLS fd fs => some (Ops.CEIL_L_S fd fs)
  | .ceilLD fd fs => some (Ops.CEIL_L_D fd fs)
  | .floorLS fd fs => some (Ops.FLOOR_L_S fd fs)
  | .floorLD fd fs => some (Ops.FLOOR_L_D fd fs)
  | .cvtSL fd fs => some (Ops.CVT_S_L fd fs)
  | .cvtDL fd fs => some (Ops.CVT_D_L fd fs)
  -- END R6-5

end Manual
