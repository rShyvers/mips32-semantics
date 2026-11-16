import Semantics.Refine.BridgeFpuMove

/-!
# Refine.FpuMove — FP moves against `execInstr` (7C S4b)

`MFC1`, `MTC1`, `MFHC1`, `MTHC1`, `MOV.fmt` (S, D; Release 6 removed the conditional moves). The
double forms read and write the FPR pair through `ValueFPR64`/`StoreFPR64`, whose
odd-register outcomes under `modelOracle` are the even-register formula (`valueFPR64_model`,
`storeFPR64_model`); the "fd retains its previous value" arms store `ValueFPR(fd, fmt)` back
(`update_self`).
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
  simp only [Pseudo.run, Ops.MFC1, bind, ValueFPR32, setGPR, complete_plain, abs_FPR, regIdx_eq_reg]

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
  simp only [Pseudo.run, Ops.MTC1, bind, GPR, readGPR_abs s h0, low_32, StoreFPR32, Pseudo.modify,
    complete_plain, regIdx_eq_reg]

/-- **MFHC1 refines** (an odd `fs`: `Oracle.fprOddRead`, the model's pair `fs`, `fs + 1`). -/
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
      mkNext s (writeReg s (regIdx rt) (readFpReg s (regIdx (fs + 1#32)))) := rfl
  rw [hb, abs_mkNext_writeReg _ _ _ hsz]
  simp only [Pseudo.run, Ops.MFHC1, bind, valueFPR64_model, bits, Nat.reduceAdd, Nat.reduceSub,
    append_hi, setGPR, complete_plain, abs_FPR, regIdx_eq_reg, reg_succ]

/-- **MTHC1 refines** (an odd `fs`: `Oracle.fprOddRead`/`fprOddWrite`). -/
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
      mkNext s (writeFpReg s (regIdx (fs + 1#32)) (readReg s (regIdx rt))) := rfl
  rw [hb, abs_mkNext_writeFpReg _ _ _ hfsz]
  simp only [Pseudo.run, Ops.MTHC1, bind, GPR, readGPR_abs s h0, valueFPR64_model, bits,
    Nat.reduceAdd, Nat.reduceSub, append_lo, append_hi, storeFPR64_model, update_self,
    complete_plain, regIdx_eq_reg, reg_succ]

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
  simp only [Pseudo.run, Ops.MOV_S, bind, ValueFPR32, StoreFPR32, Pseudo.modify, complete_plain,
    abs_FPR, regIdx_eq_reg]

/-- **MOV.D refines** (odd registers: the oracle's pair formula). -/
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
  simp only [Pseudo.run, Ops.MOV_D, bind, valueFPR64_model, storeFPR64_model, complete_plain,
    append_lo, append_hi]

end Refine
