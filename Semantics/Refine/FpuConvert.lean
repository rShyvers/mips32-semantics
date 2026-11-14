import Semantics.Refine.BridgeFpu

/-!
# Refine.FpuConvert — FP conversions against `execInstr` (7C S4a)

`ROUND/TRUNC/CEIL/FLOOR/CVT.W.fmt`, `CVT.D.S`, `CVT.D.W`, `CVT.S.D`, `CVT.S.W`. The fixed rounding
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
theorem roundingMode_FCSR (s : State) :
    IEEE.roundingMode (FCSR_RM (abs s)) = Mips.Fp.getRM s.fcsr := rfl

/-- **ROUND.W.S refines.** -/
theorem roundWS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.roundWS fd fs) = some w) :
    Execute modelCtx w (.roundWS fd fs) (abs s) =
      some (abs (execInstr s (.roundWS fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ (.inl rfl) rfl hw
  refine execute_cop1 s w _ (Ops.ROUND_W_S fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.roundWS fd fs) =
      fpFinishS s fd (Mips.Fp.f32ToW32 .RN (readFpReg s (regIdx fs))) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.ROUND_W_S, bind, ValueFPR32, abs_FPR, regIdx_eq_reg, IEEE.toWordS,
      roundingMode_round]


/-- **ROUND.W.D refines.** -/
theorem roundWD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.roundWD fd fs) = some w) :
    Execute modelCtx w (.roundWD fd fs) (abs s) =
      some (abs (execInstr s (.roundWD fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ (.inl rfl) rfl hw
  refine execute_cop1 s w _ (Ops.ROUND_W_D fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.roundWD fd fs) =
      fpFinishS s fd (Mips.Fp.f64ToW32 .RN (readFpD s fs)) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.ROUND_W_D, bind, valueFPR64_model, readFpD_abs, IEEE.toWordD, roundingMode_round]


/-- **TRUNC.W.S refines.** -/
theorem truncWS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.truncWS fd fs) = some w) :
    Execute modelCtx w (.truncWS fd fs) (abs s) =
      some (abs (execInstr s (.truncWS fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ (.inl rfl) rfl hw
  refine execute_cop1 s w _ (Ops.TRUNC_W_S fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.truncWS fd fs) =
      fpFinishS s fd (Mips.Fp.f32ToW32 .RZ (readFpReg s (regIdx fs))) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.TRUNC_W_S, bind, ValueFPR32, abs_FPR, regIdx_eq_reg, IEEE.toWordS,
      roundingMode_trunc]


/-- **TRUNC.W.D refines.** -/
theorem truncWD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.truncWD fd fs) = some w) :
    Execute modelCtx w (.truncWD fd fs) (abs s) =
      some (abs (execInstr s (.truncWD fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ (.inl rfl) rfl hw
  refine execute_cop1 s w _ (Ops.TRUNC_W_D fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.truncWD fd fs) =
      fpFinishS s fd (Mips.Fp.f64ToW32 .RZ (readFpD s fs)) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.TRUNC_W_D, bind, valueFPR64_model, readFpD_abs, IEEE.toWordD, roundingMode_trunc]


/-- **CEIL.W.S refines.** -/
theorem ceilWS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.ceilWS fd fs) = some w) :
    Execute modelCtx w (.ceilWS fd fs) (abs s) =
      some (abs (execInstr s (.ceilWS fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ (.inl rfl) rfl hw
  refine execute_cop1 s w _ (Ops.CEIL_W_S fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.ceilWS fd fs) =
      fpFinishS s fd (Mips.Fp.f32ToW32 .RP (readFpReg s (regIdx fs))) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.CEIL_W_S, bind, ValueFPR32, abs_FPR, regIdx_eq_reg, IEEE.toWordS,
      roundingMode_ceil]


/-- **CEIL.W.D refines.** -/
theorem ceilWD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.ceilWD fd fs) = some w) :
    Execute modelCtx w (.ceilWD fd fs) (abs s) =
      some (abs (execInstr s (.ceilWD fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ (.inl rfl) rfl hw
  refine execute_cop1 s w _ (Ops.CEIL_W_D fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.ceilWD fd fs) =
      fpFinishS s fd (Mips.Fp.f64ToW32 .RP (readFpD s fs)) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.CEIL_W_D, bind, valueFPR64_model, readFpD_abs, IEEE.toWordD, roundingMode_ceil]


/-- **FLOOR.W.S refines.** -/
theorem floorWS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.floorWS fd fs) = some w) :
    Execute modelCtx w (.floorWS fd fs) (abs s) =
      some (abs (execInstr s (.floorWS fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ (.inl rfl) rfl hw
  refine execute_cop1 s w _ (Ops.FLOOR_W_S fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.floorWS fd fs) =
      fpFinishS s fd (Mips.Fp.f32ToW32 .RM (readFpReg s (regIdx fs))) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.FLOOR_W_S, bind, ValueFPR32, abs_FPR, regIdx_eq_reg, IEEE.toWordS,
      roundingMode_floor]


/-- **FLOOR.W.D refines.** -/
theorem floorWD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.floorWD fd fs) = some w) :
    Execute modelCtx w (.floorWD fd fs) (abs s) =
      some (abs (execInstr s (.floorWD fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ (.inl rfl) rfl hw
  refine execute_cop1 s w _ (Ops.FLOOR_W_D fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.floorWD fd fs) =
      fpFinishS s fd (Mips.Fp.f64ToW32 .RM (readFpD s fs)) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.FLOOR_W_D, bind, valueFPR64_model, readFpD_abs, IEEE.toWordD, roundingMode_floor]


/-- **CVT.W.S refines.** -/
theorem cvtWS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtWS fd fs) = some w) :
    Execute modelCtx w (.cvtWS fd fs) (abs s) =
      some (abs (execInstr s (.cvtWS fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ (.inl rfl) rfl hw
  refine execute_cop1 s w _ (Ops.CVT_W_S fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.cvtWS fd fs) =
      fpFinishS s fd (Mips.Fp.f32ToW32 (Mips.Fp.getRM s.fcsr) (readFpReg s (regIdx fs))) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.CVT_W_S, bind, ValueFPR32, Pseudo.get, abs_FPR, regIdx_eq_reg, IEEE.toWordS,
      roundingMode_FCSR]


/-- **CVT.W.D refines.** -/
theorem cvtWD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtWD fd fs) = some w) :
    Execute modelCtx w (.cvtWD fd fs) (abs s) =
      some (abs (execInstr s (.cvtWD fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ (.inl rfl) rfl hw
  refine execute_cop1 s w _ (Ops.CVT_W_D fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.cvtWD fd fs) =
      fpFinishS s fd (Mips.Fp.f64ToW32 (Mips.Fp.getRM s.fcsr) (readFpD s fs)) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.CVT_W_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, IEEE.toWordD,
      roundingMode_FCSR]


/-- **CVT.D.S refines (the model's QNaN result is `Oracle.cvtQNaNToD`).** -/
theorem cvtDS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtDS fd fs) = some w) :
    Execute modelCtx w (.cvtDS fd fs) (abs s) =
      some (abs (execInstr s (.cvtDS fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ (.inl rfl) rfl hw
  refine execute_cop1 s w _ (Ops.CVT_D_S fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.cvtDS fd fs) =
      fpFinishD s fd (Mips.Fp.f32ToF64 (readFpReg s (regIdx fs))) from rfl]
  rw [← runAbs_finD s hfsz fd]
  apply runAbs_congr
  simp only [Ops.CVT_D_S, bind, ValueFPR32, abs_FPR, regIdx_eq_reg, Pseudo.oracle,
      modelCtx_oracle, cvtDS_model]


/-- **CVT.D.W refines.** -/
theorem cvtDW_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtDW fd fs) = some w) :
    Execute modelCtx w (.cvtDW fd fs) (abs s) =
      some (abs (execInstr s (.cvtDW fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ (.inl rfl) rfl hw
  refine execute_cop1 s w _ (Ops.CVT_D_W fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.cvtDW fd fs) =
      fpFinishD s fd (Mips.Fp.w32ToF64F (readFpReg s (regIdx fs))) from rfl]
  rw [← runAbs_finD s hfsz fd]
  apply runAbs_congr
  simp only [Ops.CVT_D_W, bind, ValueFPR32, abs_FPR, regIdx_eq_reg, IEEE.cvtDW]


/-- **CVT.S.D refines (the model's QNaN result is `Oracle.cvtQNaNToS`).** -/
theorem cvtSD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtSD fd fs) = some w) :
    Execute modelCtx w (.cvtSD fd fs) (abs s) =
      some (abs (execInstr s (.cvtSD fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ (.inl rfl) rfl hw
  refine execute_cop1 s w _ (Ops.CVT_S_D fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.cvtSD fd fs) =
      fpFinishS s fd (Mips.Fp.f64ToF32 (fpEnv s) (readFpD s fs)) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.CVT_S_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, Pseudo.oracle,
      modelCtx_oracle, cvtSD_model]


/-- **CVT.S.W refines.** -/
theorem cvtSW_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.cvtSW fd fs) = some w) :
    Execute modelCtx w (.cvtSW fd fs) (abs s) =
      some (abs (execInstr s (.cvtSW fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  obtain ⟨h1, h0⟩ := cop1_rFormat _ _ _ _ _ _ (.inl rfl) rfl hw
  refine execute_cop1 s w _ (Ops.CVT_S_W fd fs) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.cvtSW fd fs) =
      fpFinishS s fd (Mips.Fp.w32ToF32 (fpEnv s) (readFpReg s (regIdx fs))) from rfl]
  rw [← runAbs_finS s hfsz fd]
  apply runAbs_congr
  simp only [Ops.CVT_S_W, bind, ValueFPR32, Pseudo.get, abs_FPR, regIdx_eq_reg, env_abs, IEEE.cvtSW]


end Refine
