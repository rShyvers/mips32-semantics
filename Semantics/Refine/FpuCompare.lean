import Semantics.Refine.BridgeFpu

/-!
# Refine.FpuCompare — `C.cond.fmt` against `execInstr` (7C S4a)

The Operation of `C.cond.S`/`C.cond.D` (MD00086 Vol II-A Rev 6.06, C.cond.fmt, p.112-113) is the
model's `Mips.Fp.f32Compare`/`f64Compare` (`f32Compare_eq`, `f64Compare_eq`), its Invalid Operation
goes through `FPResult` as the model's `fpFinishCmp` (`runAbs_FPResult`), and `SetFPConditionCode` on
the 3-bit `cc` field (p.110) is the model's `setCC` at `ccIdx` (`runAbs_setCC`).
-/

namespace Refine

open Manual

/-- **C.cond.S refines.** -/
theorem cCondS_refines (s : State) (_hg : Good s) (cond cc fs ft w : W32)
    (hw : enc (.cCondS cond cc fs ft) = some w) :
    Execute modelCtx w (.cCondS cond cc fs ft) (abs s) =
      some (abs (execInstr s (.cCondS cond cc fs ft))) := by
  obtain ⟨h1, h0⟩ := cop1_cCond _ _ _ _ _ rfl hw
  refine execute_cop1 s w _ (Ops.C_cond_S cond cc fs ft) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.cCondS cond cc fs ft) = fpFinishCmp s cc (Mips.Fp.f32Compare (cond.setWidth 4)
    (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))) from rfl, fpFinishCmp_eq, f32Compare_eq]
  refine Eq.trans ?_ (runAbs_FPResult s _ (fun b => SetFPConditionCode (low cc 3).toNat b) _
    fun _ => runAbs_setCC _ cc _)
  apply runAbs_congr
  simp only [Ops.C_cond_S, bind, ValueFPR32, abs_FPR, regIdx_eq_reg]

/-- **C.cond.D refines.** -/
theorem cCondD_refines (s : State) (_hg : Good s) (cond cc fs ft w : W32)
    (hw : enc (.cCondD cond cc fs ft) = some w) :
    Execute modelCtx w (.cCondD cond cc fs ft) (abs s) =
      some (abs (execInstr s (.cCondD cond cc fs ft))) := by
  obtain ⟨h1, h0⟩ := cop1_cCond _ _ _ _ _ rfl hw
  refine execute_cop1 s w _ (Ops.C_cond_D cond cc fs ft) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.cCondD cond cc fs ft) = fpFinishCmp s cc (Mips.Fp.f64Compare (cond.setWidth 4)
    (readFpD s fs) (readFpD s ft)) from rfl, fpFinishCmp_eq, f64Compare_eq]
  refine Eq.trans ?_ (runAbs_FPResult s _ (fun b => SetFPConditionCode (low cc 3).toNat b) _
    fun _ => runAbs_setCC _ cc _)
  apply runAbs_congr
  simp only [Ops.C_cond_D, bind, valueFPR64_model, readFpD_abs]

end Refine
