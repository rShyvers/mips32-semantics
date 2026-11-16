import Semantics.Refine.BridgeFpu

/-!
# Refine.FpuArith — FP arithmetic Operations against `execInstr`

`Refine.<ctor>_refines` for `ADD/SUB/MUL/DIV/SQRT/ABS/NEG/RECIP/RSQRT.fmt`, fmt = S, D (Release 6
removed `MADD/MSUB/NMADD/NMSUB.fmt`; Sub-wave 7A proved the pilot `add.s`; 7C S4a the rest and
re-proved the pilot through `Refine.BridgeFpu`). The FCSR bookkeeping (`Manual.FPResult`: Cause,
`CheckFPException`, Flags; MD00082 Vol I-A Rev 6.01 §6.7.1, p.98-99) against the model's
`fpFinishS`/`fpFinishD`/`fpThen` (`Mips.Fp.fpUpdate`) is `runAbs_FPResult`, proved once. The model's
choices enter as: `Impl.recipS/D`, `Impl.rsqrtS/D` (definitionally the core's `f32Recip` …) and
`Oracle.fprUpper` (a 32-bit result keeps the upper half of the FPR, `runAbs_store32`). ABS/NEG are
non-arithmetic (`FCSR.ABS2008 = 1`, `f32Abs_eq` …).
-/

namespace Refine

open Manual

/-- **ADD.S refines.** -/
theorem addS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.addS fd fs ft) = some w) :
    Execute modelCtx w (.addS fd fs ft) (abs s) =
      some (abs (execInstr s (.addS fd fs ft))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.ADD_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.addS]

/-- **SUB.S refines.** -/
theorem subS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.subS fd fs ft) = some w) :
    Execute modelCtx w (.subS fd fs ft) (abs s) =
      some (abs (execInstr s (.subS fd fs ft))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.SUB_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.subS]

/-- **MUL.S refines.** -/
theorem mulS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.mulS fd fs ft) = some w) :
    Execute modelCtx w (.mulS fd fs ft) (abs s) =
      some (abs (execInstr s (.mulS fd fs ft))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.MUL_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.mulS]

/-- **DIV.S refines.** -/
theorem divS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.divS fd fs ft) = some w) :
    Execute modelCtx w (.divS fd fs ft) (abs s) =
      some (abs (execInstr s (.divS fd fs ft))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.DIV_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.divS]

/-- **SQRT.S refines.** -/
theorem sqrtS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.sqrtS fd fs) = some w) :
    Execute modelCtx w (.sqrtS fd fs) (abs s) =
      some (abs (execInstr s (.sqrtS fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.SQRT_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.sqrtS]

/-- **ABS.S refines (non-arithmetic, `FCSR.ABS2008 = 1`).** -/
theorem absS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.absS fd fs) = some w) :
    Execute modelCtx w (.absS fd fs) (abs s) =
      some (abs (execInstr s (.absS fd fs))) := by
  fp_refine runAbs_store32 fd =>
    simp only [f32Abs_eq, Ops.ABS_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg]

/-- **NEG.S refines (non-arithmetic, `FCSR.ABS2008 = 1`).** -/
theorem negS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.negS fd fs) = some w) :
    Execute modelCtx w (.negS fd fs) (abs s) =
      some (abs (execInstr s (.negS fd fs))) := by
  fp_refine runAbs_store32 fd =>
    simp only [f32Neg_eq, Ops.NEG_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg]

/-- **RECIP.S refines (`Impl.recipS` of the model).** -/
theorem recipS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.recipS fd fs) = some w) :
    Execute modelCtx w (.recipS fd fs) (abs s) =
      some (abs (execInstr s (.recipS fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.RECIP_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs,
        Pseudo.impl, modelCtx_impl, modelImpl_recipS, Mips.Fp.f32Recip]

/-- **RSQRT.S refines (`Impl.rsqrtS` of the model).** -/
theorem rsqrtS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.rsqrtS fd fs) = some w) :
    Execute modelCtx w (.rsqrtS fd fs) (abs s) =
      some (abs (execInstr s (.rsqrtS fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.RSQRT_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs,
        Pseudo.impl, modelCtx_impl, modelImpl_rsqrtS, Mips.Fp.f32Rsqrt]

/-- **ADD.D refines.** -/
theorem addD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.addD fd fs ft) = some w) :
    Execute modelCtx w (.addD fd fs ft) (abs s) =
      some (abs (execInstr s (.addD fd fs ft))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.ADD_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.addD]

/-- **SUB.D refines.** -/
theorem subD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.subD fd fs ft) = some w) :
    Execute modelCtx w (.subD fd fs ft) (abs s) =
      some (abs (execInstr s (.subD fd fs ft))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.SUB_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.subD]

/-- **MUL.D refines.** -/
theorem mulD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.mulD fd fs ft) = some w) :
    Execute modelCtx w (.mulD fd fs ft) (abs s) =
      some (abs (execInstr s (.mulD fd fs ft))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.MUL_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.mulD]

/-- **DIV.D refines.** -/
theorem divD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.divD fd fs ft) = some w) :
    Execute modelCtx w (.divD fd fs ft) (abs s) =
      some (abs (execInstr s (.divD fd fs ft))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.DIV_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.divD]

/-- **SQRT.D refines.** -/
theorem sqrtD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.sqrtD fd fs) = some w) :
    Execute modelCtx w (.sqrtD fd fs) (abs s) =
      some (abs (execInstr s (.sqrtD fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.SQRT_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.sqrtD]

/-- **ABS.D refines (non-arithmetic, `FCSR.ABS2008 = 1`).** -/
theorem absD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.absD fd fs) = some w) :
    Execute modelCtx w (.absD fd fs) (abs s) =
      some (abs (execInstr s (.absD fd fs))) := by
  fp_refine runAbs_store64 fd =>
    simp only [f64Abs_eq, Ops.ABS_D, bind, valueFPR64_model, readFpD_abs]

/-- **NEG.D refines (non-arithmetic, `FCSR.ABS2008 = 1`).** -/
theorem negD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.negD fd fs) = some w) :
    Execute modelCtx w (.negD fd fs) (abs s) =
      some (abs (execInstr s (.negD fd fs))) := by
  fp_refine runAbs_store64 fd =>
    simp only [f64Neg_eq, Ops.NEG_D, bind, valueFPR64_model, readFpD_abs]

/-- **RECIP.D refines (`Impl.recipD` of the model).** -/
theorem recipD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.recipD fd fs) = some w) :
    Execute modelCtx w (.recipD fd fs) (abs s) =
      some (abs (execInstr s (.recipD fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.RECIP_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, Pseudo.impl,
        modelCtx_impl, modelImpl_recipD, Mips.Fp.f64Recip]

/-- **RSQRT.D refines (`Impl.rsqrtD` of the model).** -/
theorem rsqrtD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.rsqrtD fd fs) = some w) :
    Execute modelCtx w (.rsqrtD fd fs) (abs s) =
      some (abs (execInstr s (.rsqrtD fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.RSQRT_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, Pseudo.impl,
        modelCtx_impl, modelImpl_rsqrtD, Mips.Fp.f64Rsqrt]

end Refine
