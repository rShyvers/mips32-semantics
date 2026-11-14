import Semantics.Manual.Ops.IntArith
import Semantics.Manual.Ops.Memory
import Semantics.Manual.Ops.Unaligned
import Semantics.Manual.Ops.Branch
import Semantics.Manual.Ops.BranchLikely
import Semantics.Manual.Ops.FpuArith
import Semantics.Manual.Ops.Cp0
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
  | _ => none

end Manual
