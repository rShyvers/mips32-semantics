import Semantics.Refine.BridgeFpuMove

/-!
# Refine.FpuMove — FP moves against `execInstr`

`MFC1`, `MTC1`, `MFHC1`, `MTHC1`, `MOV.fmt` (S, D; Release 6 removed the conditional moves). With the
64-bit FPRs (`Status.FR = 1`) the double forms read and write one FPR (`valueFPR64_model`,
`storeFPR64_model`); a 32-bit store keeps the upper half (`Oracle.fprUpper` of the model,
`fprUpper_model`).
-/

namespace Refine

open Manual

/-- **MFC1 refines.** -/
theorem mfc1_refines (s : State) (hg : Good s) (rt fs w : W32)
    (hw : enc (.mfc1 rt fs) = some w) :
    Execute modelCtx w (.mfc1 rt fs) (abs s) = some (abs (execInstr s (.mfc1 rt fs))) := by
  obtain ⟨hsz, -, -⟩ := hg
  have hw' : w = rFormat 0x11#32 0x00#32 rt fs 0#32 0#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MFC1 rt fs) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.mfc1 rt fs) = mkNext s (writeReg s (regIdx rt) (readFpReg s (regIdx fs))) := rfl
  rw [hb, abs_mkNext_writeReg _ _ _ hsz]
  simp only [Pseudo.run, Ops.MFC1, bind, ValueFPR32, setGPR, complete_plain, abs_FPR, readFpReg_eq,
    regIdx_eq_reg]

/-- **MTC1 refines.** -/
theorem mtc1_refines (s : State) (hg : Good s) (rt fs w : W32)
    (hw : enc (.mtc1 rt fs) = some w) :
    Execute modelCtx w (.mtc1 rt fs) (abs s) = some (abs (execInstr s (.mtc1 rt fs))) := by
  obtain ⟨-, hfsz, h0⟩ := hg
  have hw' : w = rFormat 0x11#32 0x04#32 rt fs 0#32 0#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MTC1 rt fs) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.mtc1 rt fs) = mkNext s (writeFpReg s (regIdx fs) (readReg s (regIdx rt))) := rfl
  rw [hb, abs_mkNext_writeFpReg _ _ _ hfsz]
  simp only [Pseudo.run, Ops.MTC1, bind, GPR, readGPR_abs s h0, low_32, StoreFPR32, fprUpper_model,
    abs_FPR, complete_plain, regIdx_eq_reg]

/-- **MFHC1 refines** (bits 63..32 of the 64-bit FPR). -/
theorem mfhc1_refines (s : State) (hg : Good s) (rt fs w : W32)
    (hw : enc (.mfhc1 rt fs) = some w) :
    Execute modelCtx w (.mfhc1 rt fs) (abs s) = some (abs (execInstr s (.mfhc1 rt fs))) := by
  obtain ⟨hsz, -, -⟩ := hg
  have hw' : w = rFormat 0x11#32 0x03#32 rt fs 0#32 0#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MFHC1 rt fs) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.mfhc1 rt fs) =
      mkNext s (writeReg s (regIdx rt) ((readFpD s fs).extractLsb' 32 32)) := rfl
  rw [hb, abs_mkNext_writeReg _ _ _ hsz, readFpD_abs]
  simp only [Pseudo.run, Ops.MFHC1, bind, valueFPR64_model, bits, Nat.reduceAdd, Nat.reduceSub,
    setGPR, complete_plain, regIdx_eq_reg]

/-- **MTHC1 refines** (bits 63..32 of the 64-bit FPR, the low half kept). -/
theorem mthc1_refines (s : State) (hg : Good s) (rt fs w : W32)
    (hw : enc (.mthc1 rt fs) = some w) :
    Execute modelCtx w (.mthc1 rt fs) (abs s) = some (abs (execInstr s (.mthc1 rt fs))) := by
  obtain ⟨-, hfsz, h0⟩ := hg
  have hw' : w = rFormat 0x11#32 0x07#32 rt fs 0#32 0#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MTHC1 rt fs) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.mthc1 rt fs) =
      mkNext s (writeFpD s fs (readReg s (regIdx rt) ++ (readFpD s fs).extractLsb' 0 32)) := rfl
  rw [hb, abs_mkNext_writeFpD _ _ _ hfsz, readFpD_abs]
  simp only [Pseudo.run, Ops.MTHC1, bind, GPR, readGPR_abs s h0, valueFPR64_model, bits,
    Nat.reduceAdd, Nat.reduceSub, storeFPR64_model, complete_plain, regIdx_eq_reg]

/-- **MOV.S refines.** -/
theorem movS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.movS fd fs) = some w) :
    Execute modelCtx w (.movS fd fs) (abs s) = some (abs (execInstr s (.movS fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  have hw' : w = rFormat 0x11#32 0x10#32 0#32 fs fd 0x06#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MOV_S fd fs) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.movS fd fs) = mkNext s (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) := rfl
  rw [hb, abs_mkNext_writeFpReg _ _ _ hfsz]
  simp only [Pseudo.run, Ops.MOV_S, bind, ValueFPR32, StoreFPR32, fprUpper_model, complete_plain,
    abs_FPR, readFpReg_eq, regIdx_eq_reg]

/-- **MOV.D refines.** -/
theorem movD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.movD fd fs) = some w) :
    Execute modelCtx w (.movD fd fs) (abs s) = some (abs (execInstr s (.movD fd fs))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  have hw' : w = rFormat 0x11#32 0x11#32 0#32 fs fd 0x06#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MOV_D fd fs) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.movD fd fs) = mkNext s (writeFpD s fd (readFpD s fs)) := rfl
  rw [hb, abs_mkNext_writeFpD _ _ _ hfsz, readFpD_abs]
  simp only [Pseudo.run, Ops.MOV_D, bind, valueFPR64_model, storeFPR64_model, complete_plain]

end Refine
