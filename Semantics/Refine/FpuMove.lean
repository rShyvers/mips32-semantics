import Semantics.Refine.BridgeFpuMove

/-!
# Refine.FpuMove — FP moves against `execInstr` (7C S4b)

`MFC1`, `MTC1`, `MFHC1`, `MTHC1`, `MOV.fmt`, `MOVF.fmt`, `MOVT.fmt`, `MOVN.fmt`, `MOVZ.fmt` (S, D) and the
GPR `MOVF`/`MOVT`. The double forms read and write the FPR pair through `ValueFPR64`/`StoreFPR64`, whose
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

/-- **MOVF.S refines.** -/
theorem movfS_refines (s : State) (hg : Good s) (fd fs cc w : W32)
    (hw : enc (.movfS fd fs cc) = some w) :
    Execute modelCtx w (.movfS fd fs cc) (abs s) = some (abs (execInstr s (.movfS fd fs cc))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  have hw' : w = fld 6 26 0x11#32 ||| fld 5 21 0x10#32 ||| fld 3 18 cc ||| fld 1 16 0#32 |||
      fld 5 11 fs ||| fld 5 6 fd ||| fld 6 0 0x11#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MOVF_S fd fs cc) rfl (by simp [InCop1Space, opcode_movcf])
    (by simp [InCop0Space, opcode_movcf]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.movfS fd fs cc) =
      if readFcc s cc then mkNext s s
      else mkNext s (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.MOVF_S, bind, fpcc_run, ValueFPR32, StoreFPR32, Pseudo.modify, abs_FCSR]
  rw [show Mips.Fp.getCC s.fcsr (ccIdx cc) = readFcc s cc from rfl]
  cases hc : readFcc s cc
  · simp only [beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
    rw [abs_mkNext_writeFpReg _ _ _ hfsz]
    simp only [abs_FPR, regIdx_eq_reg, complete_plain]
  · simp only [Bool.true_beq, Bool.false_eq_true, ↓reduceIte]
    rw [abs_mkNext_self]
    simp only [complete_plain, update_self]

/-- **MOVT.S refines.** -/
theorem movtS_refines (s : State) (hg : Good s) (fd fs cc w : W32)
    (hw : enc (.movtS fd fs cc) = some w) :
    Execute modelCtx w (.movtS fd fs cc) (abs s) = some (abs (execInstr s (.movtS fd fs cc))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  have hw' : w = fld 6 26 0x11#32 ||| fld 5 21 0x10#32 ||| fld 3 18 cc ||| fld 1 16 1#32 |||
      fld 5 11 fs ||| fld 5 6 fd ||| fld 6 0 0x11#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MOVT_S fd fs cc) rfl (by simp [InCop1Space, opcode_movcf])
    (by simp [InCop0Space, opcode_movcf]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.movtS fd fs cc) =
      if readFcc s cc then mkNext s (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs)))
      else mkNext s s := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.MOVT_S, bind, fpcc_run, ValueFPR32, StoreFPR32, Pseudo.modify, abs_FCSR]
  rw [show Mips.Fp.getCC s.fcsr (ccIdx cc) = readFcc s cc from rfl]
  cases hc : readFcc s cc
  · simp only [Bool.false_beq, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [abs_mkNext_self]
    simp only [complete_plain, update_self]
  · simp only [beq_self_eq_true, ↓reduceIte]
    rw [abs_mkNext_writeFpReg _ _ _ hfsz]
    simp only [abs_FPR, regIdx_eq_reg, complete_plain]

/-- **MOVF.D refines.** -/
theorem movfD_refines (s : State) (hg : Good s) (fd fs cc w : W32)
    (hw : enc (.movfD fd fs cc) = some w) :
    Execute modelCtx w (.movfD fd fs cc) (abs s) = some (abs (execInstr s (.movfD fd fs cc))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  have hw' : w = fld 6 26 0x11#32 ||| fld 5 21 0x11#32 ||| fld 3 18 cc ||| fld 1 16 0#32 |||
      fld 5 11 fs ||| fld 5 6 fd ||| fld 6 0 0x11#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MOVF_D fd fs cc) rfl (by simp [InCop1Space, opcode_movcf])
    (by simp [InCop0Space, opcode_movcf]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.movfD fd fs cc) =
      if readFcc s cc then mkNext s s
      else mkNext s (writeFpD s fd (readFpD s fs)) := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.MOVF_D, bind, fpcc_run, abs_FCSR]
  rw [show Mips.Fp.getCC s.fcsr (ccIdx cc) = readFcc s cc from rfl]
  cases hc : readFcc s cc
  · simp only [beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, valueFPR64_model, storeFPR64_model]
    rw [abs_mkNext_writeFpD _ _ _ hfsz]
    simp only [abs_FPR, complete_plain, append_lo, append_hi, readFpD_abs]
  · simp only [Bool.true_beq, Bool.false_eq_true, ↓reduceIte, valueFPR64_model, storeFPR64_model]
    rw [abs_mkNext_self]
    simp only [complete_plain, append_lo, append_hi, update_self]

/-- **MOVT.D refines.** -/
theorem movtD_refines (s : State) (hg : Good s) (fd fs cc w : W32)
    (hw : enc (.movtD fd fs cc) = some w) :
    Execute modelCtx w (.movtD fd fs cc) (abs s) = some (abs (execInstr s (.movtD fd fs cc))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  have hw' : w = fld 6 26 0x11#32 ||| fld 5 21 0x11#32 ||| fld 3 18 cc ||| fld 1 16 1#32 |||
      fld 5 11 fs ||| fld 5 6 fd ||| fld 6 0 0x11#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MOVT_D fd fs cc) rfl (by simp [InCop1Space, opcode_movcf])
    (by simp [InCop0Space, opcode_movcf]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.movtD fd fs cc) =
      if readFcc s cc then mkNext s (writeFpD s fd (readFpD s fs))
      else mkNext s s := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.MOVT_D, bind, fpcc_run, abs_FCSR]
  rw [show Mips.Fp.getCC s.fcsr (ccIdx cc) = readFcc s cc from rfl]
  cases hc : readFcc s cc
  · simp only [Bool.false_beq, Bool.not_true, Bool.false_eq_true, ↓reduceIte, valueFPR64_model, storeFPR64_model]
    rw [abs_mkNext_self]
    simp only [complete_plain, append_lo, append_hi, update_self]
  · simp only [beq_self_eq_true, ↓reduceIte, valueFPR64_model, storeFPR64_model]
    rw [abs_mkNext_writeFpD _ _ _ hfsz]
    simp only [abs_FPR, complete_plain, append_lo, append_hi, readFpD_abs]

/-- **MOVN.S refines.** -/
theorem movnS_refines (s : State) (hg : Good s) (fd fs rt w : W32)
    (hw : enc (.movnS fd fs rt) = some w) :
    Execute modelCtx w (.movnS fd fs rt) (abs s) = some (abs (execInstr s (.movnS fd fs rt))) := by
  obtain ⟨-, hfsz, h0⟩ := hg
  have hw' : w = rFormat 0x11#32 0x10#32 rt fs fd 0x13#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MOVN_S fd fs rt) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.movnS fd fs rt) =
      if readReg s (regIdx rt) != 0#32 then mkNext s (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) else mkNext s s := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.MOVN_S, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, ValueFPR32, StoreFPR32,
    Pseudo.modify]
  cases hc : (readReg s (regIdx rt) != 0#32)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [abs_mkNext_self]
    simp only [complete_plain, update_self]
  · simp only [↓reduceIte]
    rw [abs_mkNext_writeFpReg _ _ _ hfsz]
    simp only [abs_FPR, regIdx_eq_reg, complete_plain]

/-- **MOVZ.S refines.** -/
theorem movzS_refines (s : State) (hg : Good s) (fd fs rt w : W32)
    (hw : enc (.movzS fd fs rt) = some w) :
    Execute modelCtx w (.movzS fd fs rt) (abs s) = some (abs (execInstr s (.movzS fd fs rt))) := by
  obtain ⟨-, hfsz, h0⟩ := hg
  have hw' : w = rFormat 0x11#32 0x10#32 rt fs fd 0x12#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MOVZ_S fd fs rt) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.movzS fd fs rt) =
      if readReg s (regIdx rt) == 0#32 then mkNext s (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) else mkNext s s := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.MOVZ_S, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, ValueFPR32, StoreFPR32,
    Pseudo.modify]
  cases hc : (readReg s (regIdx rt) == 0#32)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [abs_mkNext_self]
    simp only [complete_plain, update_self]
  · simp only [↓reduceIte]
    rw [abs_mkNext_writeFpReg _ _ _ hfsz]
    simp only [abs_FPR, regIdx_eq_reg, complete_plain]

/-- **MOVN.D refines.** -/
theorem movnD_refines (s : State) (hg : Good s) (fd fs rt w : W32)
    (hw : enc (.movnD fd fs rt) = some w) :
    Execute modelCtx w (.movnD fd fs rt) (abs s) = some (abs (execInstr s (.movnD fd fs rt))) := by
  obtain ⟨-, hfsz, h0⟩ := hg
  have hw' : w = rFormat 0x11#32 0x11#32 rt fs fd 0x13#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MOVN_D fd fs rt) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.movnD fd fs rt) =
      if readReg s (regIdx rt) != 0#32 then mkNext s (writeFpD s fd (readFpD s fs)) else mkNext s s := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.MOVN_D, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg
    ]
  cases hc : (readReg s (regIdx rt) != 0#32)
  · simp only [Bool.false_eq_true, ↓reduceIte, valueFPR64_model, storeFPR64_model]
    rw [abs_mkNext_self]
    simp only [complete_plain, append_lo, append_hi, update_self]
  · simp only [↓reduceIte, valueFPR64_model, storeFPR64_model]
    rw [abs_mkNext_writeFpD _ _ _ hfsz]
    simp only [abs_FPR, regIdx_eq_reg, complete_plain, append_lo, append_hi, readFpD_abs]

/-- **MOVZ.D refines.** -/
theorem movzD_refines (s : State) (hg : Good s) (fd fs rt w : W32)
    (hw : enc (.movzD fd fs rt) = some w) :
    Execute modelCtx w (.movzD fd fs rt) (abs s) = some (abs (execInstr s (.movzD fd fs rt))) := by
  obtain ⟨-, hfsz, h0⟩ := hg
  have hw' : w = rFormat 0x11#32 0x11#32 rt fs fd 0x12#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MOVZ_D fd fs rt) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.movzD fd fs rt) =
      if readReg s (regIdx rt) == 0#32 then mkNext s (writeFpD s fd (readFpD s fs)) else mkNext s s := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.MOVZ_D, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg
    ]
  cases hc : (readReg s (regIdx rt) == 0#32)
  · simp only [Bool.false_eq_true, ↓reduceIte, valueFPR64_model, storeFPR64_model]
    rw [abs_mkNext_self]
    simp only [complete_plain, append_lo, append_hi, update_self]
  · simp only [↓reduceIte, valueFPR64_model, storeFPR64_model]
    rw [abs_mkNext_writeFpD _ _ _ hfsz]
    simp only [abs_FPR, regIdx_eq_reg, complete_plain, append_lo, append_hi, readFpD_abs]

/-- **MOVF refines** (the GPR conditional move on an FP condition code). -/
theorem movf_refines (s : State) (hg : Good s) (rs cc rd w : W32)
    (hw : enc (.movf rs cc rd) = some w) :
    Execute modelCtx w (.movf rs cc rd) (abs s) = some (abs (execInstr s (.movf rs cc rd))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = fld 6 26 0#32 ||| fld 5 21 rs ||| fld 3 18 cc ||| fld 1 16 0#32 ||| fld 5 11 rd |||
      fld 6 0 1#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MOVF rs cc rd) rfl
    (by simp [InCop1Space, opcode_movci, funct_movci]) (by simp [InCop0Space, opcode_movci]) rfl rfl
    rfl rfl
  intro _
  have hb : execBody s (.movf rs cc rd) =
      if readFcc s cc then mkNext s s
      else mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs))) := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.MOVF, bind, fpcc_run, abs_FCSR, GPR, ← regIdx_eq_reg,
    setGPR]
  rw [show Mips.Fp.getCC s.fcsr (ccIdx cc) = readFcc s cc from rfl]
  cases hc : readFcc s cc
  · simp only [beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
    rw [abs_mkNext_writeReg _ _ _ hsz]
    simp only [readGPR_abs s h0, complete_plain]
  · simp only [Bool.true_beq, Bool.false_eq_true, ↓reduceIte]
    rw [abs_mkNext_self]
    simp only [complete_plain, pure]

/-- **MOVT refines** (the GPR conditional move on an FP condition code). -/
theorem movt_refines (s : State) (hg : Good s) (rs cc rd w : W32)
    (hw : enc (.movt rs cc rd) = some w) :
    Execute modelCtx w (.movt rs cc rd) (abs s) = some (abs (execInstr s (.movt rs cc rd))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = fld 6 26 0#32 ||| fld 5 21 rs ||| fld 3 18 cc ||| fld 1 16 1#32 ||| fld 5 11 rd |||
      fld 6 0 1#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.MOVT rs cc rd) rfl
    (by simp [InCop1Space, opcode_movci, funct_movci]) (by simp [InCop0Space, opcode_movci]) rfl rfl
    rfl rfl
  intro _
  have hb : execBody s (.movt rs cc rd) =
      if readFcc s cc then mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs)))
      else mkNext s s := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.MOVT, bind, fpcc_run, abs_FCSR, GPR, ← regIdx_eq_reg,
    setGPR]
  rw [show Mips.Fp.getCC s.fcsr (ccIdx cc) = readFcc s cc from rfl]
  cases hc : readFcc s cc
  · simp only [Bool.false_beq, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [abs_mkNext_self]
    simp only [complete_plain, pure]
  · simp only [beq_self_eq_true, ↓reduceIte]
    rw [abs_mkNext_writeReg _ _ _ hsz]
    simp only [readGPR_abs s h0, complete_plain]

end Refine
