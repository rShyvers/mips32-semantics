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

/-- The `ADD.S` word is in the COP1 space and not in the COP0 space. -/
theorem addS_word (fd fs ft : W32) :
    InCop1Space (rFormat 0x11#32 0x10#32 ft fs fd 0#32) = true ∧
    InCop0Space (rFormat 0x11#32 0x10#32 ft fs fd 0#32) = false := by
  simp [InCop1Space, InCop0Space, opcode_rFormat]

/-- **ADD.S refines.** -/
theorem addS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.addS fd fs ft) = some w) :
    Execute modelCtx w (.addS fd fs ft) (abs s) =
      some (abs (execInstr s (.addS fd fs ft))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.ADD_S fd fs ft) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.addS fd fs ft) =
      fpFinishS s fd (Mips.Fp.f32Add (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.ADD_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.addS]


/-- **SUB.S refines.** -/
theorem subS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.subS fd fs ft) = some w) :
    Execute modelCtx w (.subS fd fs ft) (abs s) =
      some (abs (execInstr s (.subS fd fs ft))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.SUB_S fd fs ft) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.subS fd fs ft) =
      fpFinishS s fd (Mips.Fp.f32Sub (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.SUB_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.subS]


/-- **MUL.S refines.** -/
theorem mulS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.mulS fd fs ft) = some w) :
    Execute modelCtx w (.mulS fd fs ft) (abs s) =
      some (abs (execInstr s (.mulS fd fs ft))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.MUL_S fd fs ft) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.mulS fd fs ft) =
      fpFinishS s fd (Mips.Fp.f32Mul (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.MUL_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.mulS]


/-- **DIV.S refines.** -/
theorem divS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.divS fd fs ft) = some w) :
    Execute modelCtx w (.divS fd fs ft) (abs s) =
      some (abs (execInstr s (.divS fd fs ft))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.DIV_S fd fs ft) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.divS fd fs ft) =
      fpFinishS s fd (Mips.Fp.f32Div (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.DIV_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.divS]


/-- **SQRT.S refines.** -/
theorem sqrtS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.sqrtS fd fs) = some w) :
    Execute modelCtx w (.sqrtS fd fs) (abs s) =
      some (abs (execInstr s (.sqrtS fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.SQRT_S fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.sqrtS fd fs) =
      fpFinishS s fd (Mips.Fp.f32Sqrt (fpEnv s) (readFpReg s (regIdx fs))) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.SQRT_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.sqrtS]


/-- **ABS.S refines (non-arithmetic, `FCSR.ABS2008 = 1`).** -/
theorem absS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.absS fd fs) = some w) :
    Execute modelCtx w (.absS fd fs) (abs s) =
      some (abs (execInstr s (.absS fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.ABS_S fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.absS fd fs) =
      mkNext s (writeFpReg s (regIdx fd) (Mips.Fp.f32Abs (readFpReg s (regIdx fs)))) from rfl]
  rw [f32Abs_eq, ← runAbs_store32 s hfsz fd]
  apply runAbs_congr
  simp only [Ops.ABS_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg]


/-- **NEG.S refines (non-arithmetic, `FCSR.ABS2008 = 1`).** -/
theorem negS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.negS fd fs) = some w) :
    Execute modelCtx w (.negS fd fs) (abs s) =
      some (abs (execInstr s (.negS fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.NEG_S fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.negS fd fs) =
      mkNext s (writeFpReg s (regIdx fd) (Mips.Fp.f32Neg (readFpReg s (regIdx fs)))) from rfl]
  rw [f32Neg_eq, ← runAbs_store32 s hfsz fd]
  apply runAbs_congr
  simp only [Ops.NEG_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg]


/-- **RECIP.S refines (`Impl.recipS` of the model).** -/
theorem recipS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.recipS fd fs) = some w) :
    Execute modelCtx w (.recipS fd fs) (abs s) =
      some (abs (execInstr s (.recipS fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.RECIP_S fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.recipS fd fs) =
      fpFinishS s fd (Mips.Fp.f32Recip (fpEnv s) (readFpReg s (regIdx fs))) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.RECIP_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs,
      Pseudo.impl, modelCtx_impl, modelImpl_recipS, Mips.Fp.f32Recip]


/-- **RSQRT.S refines (`Impl.rsqrtS` of the model).** -/
theorem rsqrtS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.rsqrtS fd fs) = some w) :
    Execute modelCtx w (.rsqrtS fd fs) (abs s) =
      some (abs (execInstr s (.rsqrtS fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.RSQRT_S fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.rsqrtS fd fs) =
      fpFinishS s fd (Mips.Fp.f32Rsqrt (fpEnv s) (readFpReg s (regIdx fs))) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.RSQRT_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs,
      Pseudo.impl, modelCtx_impl, modelImpl_rsqrtS, Mips.Fp.f32Rsqrt]


/-- **ADD.D refines.** -/
theorem addD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.addD fd fs ft) = some w) :
    Execute modelCtx w (.addD fd fs ft) (abs s) =
      some (abs (execInstr s (.addD fd fs ft))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.ADD_D fd fs ft) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.addD fd fs ft) =
      fpFinishD s fd (Mips.Fp.f64Add (fpEnv s) (readFpD s fs) (readFpD s ft)) from rfl]
  rw [← runAbs_finD s hfsz fd]
  apply runAbs_congr
  simp only [Ops.ADD_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.addD]


/-- **SUB.D refines.** -/
theorem subD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.subD fd fs ft) = some w) :
    Execute modelCtx w (.subD fd fs ft) (abs s) =
      some (abs (execInstr s (.subD fd fs ft))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.SUB_D fd fs ft) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.subD fd fs ft) =
      fpFinishD s fd (Mips.Fp.f64Sub (fpEnv s) (readFpD s fs) (readFpD s ft)) from rfl]
  rw [← runAbs_finD s hfsz fd]
  apply runAbs_congr
  simp only [Ops.SUB_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.subD]


/-- **MUL.D refines.** -/
theorem mulD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.mulD fd fs ft) = some w) :
    Execute modelCtx w (.mulD fd fs ft) (abs s) =
      some (abs (execInstr s (.mulD fd fs ft))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.MUL_D fd fs ft) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.mulD fd fs ft) =
      fpFinishD s fd (Mips.Fp.f64Mul (fpEnv s) (readFpD s fs) (readFpD s ft)) from rfl]
  rw [← runAbs_finD s hfsz fd]
  apply runAbs_congr
  simp only [Ops.MUL_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.mulD]


/-- **DIV.D refines.** -/
theorem divD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.divD fd fs ft) = some w) :
    Execute modelCtx w (.divD fd fs ft) (abs s) =
      some (abs (execInstr s (.divD fd fs ft))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.DIV_D fd fs ft) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.divD fd fs ft) =
      fpFinishD s fd (Mips.Fp.f64Div (fpEnv s) (readFpD s fs) (readFpD s ft)) from rfl]
  rw [← runAbs_finD s hfsz fd]
  apply runAbs_congr
  simp only [Ops.DIV_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.divD]


/-- **SQRT.D refines.** -/
theorem sqrtD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.sqrtD fd fs) = some w) :
    Execute modelCtx w (.sqrtD fd fs) (abs s) =
      some (abs (execInstr s (.sqrtD fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.SQRT_D fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.sqrtD fd fs) =
      fpFinishD s fd (Mips.Fp.f64Sqrt (fpEnv s) (readFpD s fs)) from rfl]
  rw [← runAbs_finD s hfsz fd]
  apply runAbs_congr
  simp only [Ops.SQRT_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.sqrtD]


/-- **ABS.D refines (non-arithmetic, `FCSR.ABS2008 = 1`).** -/
theorem absD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.absD fd fs) = some w) :
    Execute modelCtx w (.absD fd fs) (abs s) =
      some (abs (execInstr s (.absD fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.ABS_D fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.absD fd fs) =
      mkNext s (writeFpD s fd (Mips.Fp.f64Abs (readFpD s fs))) from rfl]
  rw [f64Abs_eq, ← runAbs_store64 s hfsz fd]
  apply runAbs_congr
  simp only [Ops.ABS_D, bind, valueFPR64_model, readFpD_abs]


/-- **NEG.D refines (non-arithmetic, `FCSR.ABS2008 = 1`).** -/
theorem negD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.negD fd fs) = some w) :
    Execute modelCtx w (.negD fd fs) (abs s) =
      some (abs (execInstr s (.negD fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.NEG_D fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.negD fd fs) =
      mkNext s (writeFpD s fd (Mips.Fp.f64Neg (readFpD s fs))) from rfl]
  rw [f64Neg_eq, ← runAbs_store64 s hfsz fd]
  apply runAbs_congr
  simp only [Ops.NEG_D, bind, valueFPR64_model, readFpD_abs]


/-- **RECIP.D refines (`Impl.recipD` of the model).** -/
theorem recipD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.recipD fd fs) = some w) :
    Execute modelCtx w (.recipD fd fs) (abs s) =
      some (abs (execInstr s (.recipD fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.RECIP_D fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.recipD fd fs) =
      fpFinishD s fd (Mips.Fp.f64Recip (fpEnv s) (readFpD s fs)) from rfl]
  rw [← runAbs_finD s hfsz fd]
  apply runAbs_congr
  simp only [Ops.RECIP_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, Pseudo.impl,
      modelCtx_impl, modelImpl_recipD, Mips.Fp.f64Recip]


/-- **RSQRT.D refines (`Impl.rsqrtD` of the model).** -/
theorem rsqrtD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.rsqrtD fd fs) = some w) :
    Execute modelCtx w (.rsqrtD fd fs) (abs s) =
      some (abs (execInstr s (.rsqrtD fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ rfl rfl hw
  refine execute_cop1 s w _ (Ops.RSQRT_D fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.rsqrtD fd fs) =
      fpFinishD s fd (Mips.Fp.f64Rsqrt (fpEnv s) (readFpD s fs)) from rfl]
  rw [← runAbs_finD s hfsz fd]
  apply runAbs_congr
  simp only [Ops.RSQRT_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, Pseudo.impl,
      modelCtx_impl, modelImpl_rsqrtD, Mips.Fp.f64Rsqrt]


end Refine
