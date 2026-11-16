import Semantics.Refine.BridgeFpu

/-!
# Refine.FpuConvert — FP conversions against `execInstr` (7C S4a)

`ROUND/TRUNC/CEIL/FLOOR/CVT.W.fmt`, `CVT.D.S`, `CVT.D.W`, `CVT.S.D`, `CVT.S.W`, and (R6-5)
`ROUND/TRUNC/CEIL/FLOOR/CVT.L.fmt`, `CVT.S.L`, `CVT.D.L`. Every operand is flushed per `FCSR.FS`
(`fcsrFS_abs`). The fixed rounding
modes of `ROUND/TRUNC/CEIL/FLOOR` (MD00086 Vol II-A Rev 6.06, p.342, p.441, p.128, p.186: rounding mode
0/1/2/3) are the model's `.RN/.RZ/.RP/.RM`; the QNaN of `CVT.D.S`/`CVT.S.D` is the model's oracle
choice (`cvtDS_model`, `cvtSD_model`).
-/

namespace Refine

open Manual

theorem roundingMode_round : IEEE.roundingMode 0#2 = .RN := rfl
theorem roundingMode_trunc : IEEE.roundingMode 1#2 = .RZ := rfl
theorem roundingMode_ceil : IEEE.roundingMode 2#2 = .RP := rfl
theorem roundingMode_floor : IEEE.roundingMode 3#2 = .RM := rfl
-- R6-5: the rounding mode and `FCSR.FS` of the manual's state are the model's `fpEnv`.
theorem roundingMode_env (s : State) : IEEE.roundingMode (FCSR_RM (abs s)) = (fpEnv s).rm := rfl
theorem fcsrFS_abs (s : State) : FCSR_FS (abs s) = (fpEnv s).flush := rfl

/-- **ROUND.W.S refines.** -/
theorem roundWS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.roundWS fd fs) = some w) :
    Execute modelCtx w (.roundWS fd fs) (abs s) =
      some (abs (execInstr s (.roundWS fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.ROUND_W_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg, Pseudo.get, IEEE.toWordS, fcsrFS_abs, roundingMode_round]

/-- **ROUND.W.D refines.** -/
theorem roundWD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.roundWD fd fs) = some w) :
    Execute modelCtx w (.roundWD fd fs) (abs s) =
      some (abs (execInstr s (.roundWD fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.ROUND_W_D, bind, valueFPR64_model, readFpD_abs, Pseudo.get, IEEE.toWordD, fcsrFS_abs, roundingMode_round]

/-- **TRUNC.W.S refines.** -/
theorem truncWS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.truncWS fd fs) = some w) :
    Execute modelCtx w (.truncWS fd fs) (abs s) =
      some (abs (execInstr s (.truncWS fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.TRUNC_W_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg, Pseudo.get, IEEE.toWordS, fcsrFS_abs, roundingMode_trunc]

/-- **TRUNC.W.D refines.** -/
theorem truncWD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.truncWD fd fs) = some w) :
    Execute modelCtx w (.truncWD fd fs) (abs s) =
      some (abs (execInstr s (.truncWD fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.TRUNC_W_D, bind, valueFPR64_model, readFpD_abs, Pseudo.get, IEEE.toWordD, fcsrFS_abs, roundingMode_trunc]

/-- **CEIL.W.S refines.** -/
theorem ceilWS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.ceilWS fd fs) = some w) :
    Execute modelCtx w (.ceilWS fd fs) (abs s) =
      some (abs (execInstr s (.ceilWS fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.CEIL_W_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg, Pseudo.get, IEEE.toWordS, fcsrFS_abs, roundingMode_ceil]

/-- **CEIL.W.D refines.** -/
theorem ceilWD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.ceilWD fd fs) = some w) :
    Execute modelCtx w (.ceilWD fd fs) (abs s) =
      some (abs (execInstr s (.ceilWD fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.CEIL_W_D, bind, valueFPR64_model, readFpD_abs, Pseudo.get, IEEE.toWordD, fcsrFS_abs, roundingMode_ceil]

/-- **FLOOR.W.S refines.** -/
theorem floorWS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.floorWS fd fs) = some w) :
    Execute modelCtx w (.floorWS fd fs) (abs s) =
      some (abs (execInstr s (.floorWS fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.FLOOR_W_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg, Pseudo.get, IEEE.toWordS, fcsrFS_abs, roundingMode_floor]

/-- **FLOOR.W.D refines.** -/
theorem floorWD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.floorWD fd fs) = some w) :
    Execute modelCtx w (.floorWD fd fs) (abs s) =
      some (abs (execInstr s (.floorWD fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.FLOOR_W_D, bind, valueFPR64_model, readFpD_abs, Pseudo.get, IEEE.toWordD, fcsrFS_abs, roundingMode_floor]

/-- **CVT.W.S refines.** -/
theorem cvtWS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtWS fd fs) = some w) :
    Execute modelCtx w (.cvtWS fd fs) (abs s) =
      some (abs (execInstr s (.cvtWS fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.CVT_W_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg, Pseudo.get, IEEE.toWordS, fcsrFS_abs, roundingMode_env]

/-- **CVT.W.D refines.** -/
theorem cvtWD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtWD fd fs) = some w) :
    Execute modelCtx w (.cvtWD fd fs) (abs s) =
      some (abs (execInstr s (.cvtWD fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.CVT_W_D, bind, valueFPR64_model, readFpD_abs, Pseudo.get, IEEE.toWordD, fcsrFS_abs, roundingMode_env]

/-- **CVT.D.S (the model's QNaN result is `Oracle.cvtQNaNToD`) refines.** -/
theorem cvtDS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtDS fd fs) = some w) :
    Execute modelCtx w (.cvtDS fd fs) (abs s) =
      some (abs (execInstr s (.cvtDS fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.CVT_D_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg, Pseudo.get, Pseudo.oracle, modelCtx_oracle, cvtDS_model, fcsrFS_abs]

/-- **CVT.D.W refines.** -/
theorem cvtDW_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtDW fd fs) = some w) :
    Execute modelCtx w (.cvtDW fd fs) (abs s) =
      some (abs (execInstr s (.cvtDW fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.CVT_D_W, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg, IEEE.cvtDW]

/-- **CVT.S.D (the model's QNaN result is `Oracle.cvtQNaNToS`) refines.** -/
theorem cvtSD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtSD fd fs) = some w) :
    Execute modelCtx w (.cvtSD fd fs) (abs s) =
      some (abs (execInstr s (.cvtSD fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.CVT_S_D, bind, valueFPR64_model, readFpD_abs, Pseudo.get, env_abs, Pseudo.oracle, modelCtx_oracle, cvtSD_model]

/-- **CVT.S.W refines.** -/
theorem cvtSW_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtSW fd fs) = some w) :
    Execute modelCtx w (.cvtSW fd fs) (abs s) =
      some (abs (execInstr s (.cvtSW fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.CVT_S_W, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg, Pseudo.get, env_abs, IEEE.cvtSW]

/-- **ROUND.L.S refines.** -/
theorem roundLS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.roundLS fd fs) = some w) :
    Execute modelCtx w (.roundLS fd fs) (abs s) =
      some (abs (execInstr s (.roundLS fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.ROUND_L_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg, Pseudo.get, IEEE.toLongS, fcsrFS_abs, roundingMode_round]

/-- **ROUND.L.D refines.** -/
theorem roundLD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.roundLD fd fs) = some w) :
    Execute modelCtx w (.roundLD fd fs) (abs s) =
      some (abs (execInstr s (.roundLD fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.ROUND_L_D, bind, valueFPR64_model, readFpD_abs, Pseudo.get, IEEE.toLongD, fcsrFS_abs, roundingMode_round]

/-- **TRUNC.L.S refines.** -/
theorem truncLS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.truncLS fd fs) = some w) :
    Execute modelCtx w (.truncLS fd fs) (abs s) =
      some (abs (execInstr s (.truncLS fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.TRUNC_L_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg, Pseudo.get, IEEE.toLongS, fcsrFS_abs, roundingMode_trunc]

/-- **TRUNC.L.D refines.** -/
theorem truncLD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.truncLD fd fs) = some w) :
    Execute modelCtx w (.truncLD fd fs) (abs s) =
      some (abs (execInstr s (.truncLD fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.TRUNC_L_D, bind, valueFPR64_model, readFpD_abs, Pseudo.get, IEEE.toLongD, fcsrFS_abs, roundingMode_trunc]

/-- **CEIL.L.S refines.** -/
theorem ceilLS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.ceilLS fd fs) = some w) :
    Execute modelCtx w (.ceilLS fd fs) (abs s) =
      some (abs (execInstr s (.ceilLS fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.CEIL_L_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg, Pseudo.get, IEEE.toLongS, fcsrFS_abs, roundingMode_ceil]

/-- **CEIL.L.D refines.** -/
theorem ceilLD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.ceilLD fd fs) = some w) :
    Execute modelCtx w (.ceilLD fd fs) (abs s) =
      some (abs (execInstr s (.ceilLD fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.CEIL_L_D, bind, valueFPR64_model, readFpD_abs, Pseudo.get, IEEE.toLongD, fcsrFS_abs, roundingMode_ceil]

/-- **FLOOR.L.S refines.** -/
theorem floorLS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.floorLS fd fs) = some w) :
    Execute modelCtx w (.floorLS fd fs) (abs s) =
      some (abs (execInstr s (.floorLS fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.FLOOR_L_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg, Pseudo.get, IEEE.toLongS, fcsrFS_abs, roundingMode_floor]

/-- **FLOOR.L.D refines.** -/
theorem floorLD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.floorLD fd fs) = some w) :
    Execute modelCtx w (.floorLD fd fs) (abs s) =
      some (abs (execInstr s (.floorLD fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.FLOOR_L_D, bind, valueFPR64_model, readFpD_abs, Pseudo.get, IEEE.toLongD, fcsrFS_abs, roundingMode_floor]

/-- **CVT.L.S refines.** -/
theorem cvtLS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtLS fd fs) = some w) :
    Execute modelCtx w (.cvtLS fd fs) (abs s) =
      some (abs (execInstr s (.cvtLS fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.CVT_L_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg, Pseudo.get, IEEE.toLongS, fcsrFS_abs, roundingMode_env]

/-- **CVT.L.D refines.** -/
theorem cvtLD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtLD fd fs) = some w) :
    Execute modelCtx w (.cvtLD fd fs) (abs s) =
      some (abs (execInstr s (.cvtLD fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.CVT_L_D, bind, valueFPR64_model, readFpD_abs, Pseudo.get, IEEE.toLongD, fcsrFS_abs, roundingMode_env]

/-- **CVT.S.L refines.** -/
theorem cvtSL_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtSL fd fs) = some w) :
    Execute modelCtx w (.cvtSL fd fs) (abs s) =
      some (abs (execInstr s (.cvtSL fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.CVT_S_L, bind, valueFPR64_model, readFpD_abs, Pseudo.get, env_abs, IEEE.cvtSL]

/-- **CVT.D.L refines.** -/
theorem cvtDL_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtDL fd fs) = some w) :
    Execute modelCtx w (.cvtDL fd fs) (abs s) =
      some (abs (execInstr s (.cvtDL fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.CVT_D_L, bind, valueFPR64_model, readFpD_abs, Pseudo.get, env_abs, IEEE.cvtDL]

end Refine
