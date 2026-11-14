import Semantics.Refine.BridgeControl

/-!
# Refine.Cp0 — coprocessor 0 instructions against `execInstr`

Sub-wave 7A proves the pilot `mtc0`: the Coprocessor Unusable check of the COP0 encoding space
(MD00090 Vol III Rev 6.02 §6.2.22, p.100), each implemented register's write (`Manual.CPRWrite`
against the model's arm) and the UNDEFINED case (`Oracle.cp0Undefined`, the model's Reserved
Instruction).
-/

namespace Refine

open Manual

theorem mtc0_word (rt rd sel : W32) :
    InCop0Space (fld 6 26 0x10#32 ||| fld 5 21 0x04#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 3 0 sel) =
      true ∧
    InCop1Space (fld 6 26 0x10#32 ||| fld 5 21 0x04#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 3 0 sel) =
      false := by
  have hop : opcode (fld 6 26 0x10#32 ||| fld 5 21 0x04#32 ||| fld 5 16 rt ||| fld 5 11 rd |||
      fld 3 0 sel) = 0x10#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [opcode, fld, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_shiftLeft]
    rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega
  simp [InCop0Space, InCop1Space, hop]

theorem config_fields (v : W32) :
    v.extractLsb' 0 3 = v.setWidth 3 ∧ v.extractLsb' 28 3 = (v >>> 28).setWidth 3 ∧
      v.extractLsb' 25 3 = (v >>> 25).setWidth 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp [BitVec.getLsbD_ushiftRight, hi] <;> omega

theorem ebase_write (v : W32) :
    (1#32 <<< 31) ||| (v &&& fieldOnes 29 12) = (v &&& ebaseWriteMask) ||| ebaseFixedBits := by
  rw [fieldOnes_29_12, BitVec.or_comm]; rfl

/-- **MTC0 refines.** -/
theorem mtc0_refines (s : State) (hg : Good s) (rt rd sel w : W32)
    (hw : enc (.mtc0 rt rd sel) = some w) :
    Execute modelCtx w (.mtc0 rt rd sel) (abs s) = some (abs (execInstr s (.mtc0 rt rd sel))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = fld 6 26 0x10#32 ||| fld 5 21 0x04#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 3 0 sel := by
    have : enc (.mtc0 rt rd sel) =
      some (fld 6 26 0x10#32 ||| fld 5 21 0x04#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 3 0 sel) := rfl
    rw [this] at hw; exact (Option.some.inj hw).symm
  obtain ⟨hc0, hc1⟩ := mtc0_word rt rd sel
  rw [← hw'] at hc0 hc1
  have hex : execInstr s (.mtc0 rt rd sel) =
      (if (!cp0Usable s) = true then takeCop0Unusable s else execBody s (.mtc0 rt rd sel)) := by
    have h1 : isBranchLike (.mtc0 rt rd sel) = false := rfl
    have h2 : usesCop1 (.mtc0 rt rd sel) = false := rfl
    have h3 : usesCop0 (.mtc0 rt rd sel) = true := rfl
    unfold execInstr; rw [h1, h2, h3]; rfl
  rw [hex]
  have hcti : IsCTI (.mtc0 rt rd sel) = false := rfl
  simp only [Execute, Execute.runOperation, hcti, hc1, hc0, Bool.false_and, Bool.false_eq_true, ite_false,
    Bool.true_and, cp0usable_abs]
  cases hu : cp0Usable s
  · simp only [Bool.not_false, ↓reduceIte]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl,
      gep_eq s (.CoprocessorUnusable 0) (by intro h; cases h) (by intro u h; cases h; omega)]
    rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hop : Operation (.mtc0 rt rd sel) = some (Ops.MTC0 rt rd sel) := rfl
    rw [hop]
    have hb : execBody s (.mtc0 rt rd sel) =
      (match rd.toNat, sel.toNat with
      | 7, 0 => mkNext s { s with cp0HWREna := readReg s (regIdx rt) &&& hwrenaWriteMask }
      | 8, 0 => mkNext s s
      | 9, 0 => mkNext s { s with cp0Count := readReg s (regIdx rt) }
      | 11, 0 => mkNext s { s with cp0Compare := readReg s (regIdx rt), cp0TimerInt := false }
      | 12, 0 => mkNext s { s with cp0Status := readReg s (regIdx rt) &&& statusWriteMask }
      | 12, 1 => mkNext s s
      | 12, 2 => mkNext s s
      | 13, 0 => mkNext s { s with cp0Cause :=
                (s.cp0Cause &&& ~~~causeWriteMask) ||| (readReg s (regIdx rt) &&& causeWriteMask) }
      | 14, 0 => mkNext s { s with cp0Epc := readReg s (regIdx rt) }
      | 15, 0 => mkNext s s
      | 15, 1 => mkNext s { s with cp0EBase :=
                (readReg s (regIdx rt) &&& ebaseWriteMask) ||| ebaseFixedBits }
      | 16, 0 => mkNext s { s with cp0ConfigK0 := (readReg s (regIdx rt)).setWidth 3,
                                   cp0ConfigK23 := (readReg s (regIdx rt) >>> 28).setWidth 3,
                                   cp0ConfigKU := (readReg s (regIdx rt) >>> 25).setWidth 3 }
      | 16, 1 => mkNext s s
      | 30, 0 => mkNext s { s with cp0ErrorEpc := readReg s (regIdx rt) }
      | _, _ => takeException s excCodeRI) := rfl
    rw [hb]; clear hb hex hw hw' hc0 hc1 hop hcti
    simp only [Pseudo.run, Ops.MTC0, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg]
    obtain ⟨hk0, hk23, hku⟩ := config_fields (readReg s (regIdx rt))
    generalize readReg s (regIdx rt) = v at *
    generalize rd.toNat = r
    generalize sel.toNat = q
    by_cases hI : IsCoprocessorRegisterImplemented r q = true
    · have hEB : ∀ a d, modelCtx.oracle.ebaseWriteBEV0 a d = .proceed := fun _ _ => rfl
      simp only [hI, ↓reduceIte, Pseudo.get, Pseudo.oracle, hEB, unpredictableOr, ite_self,
        Pseudo.modify, complete_plain]
      split <;> simp only [IsCoprocessorRegisterImplemented] at hI <;>
        first
          | (simp only [CPRWrite, mkNext, statusWritable_eq, causeWritable_eq, hwrenaWritable_eq,
              ebase_write, hk0, hk23, hku]
             rw [abs_advance _ _ (by rfl)]; rfl)
          | (exfalso; simp at hI)
          | (exfalso; revert hI; split <;> simp_all)
    · have hund : ∀ a i, modelCtx.oracle.cp0Undefined a i = .signal .ReservedInstruction :=
        fun _ _ => rfl
      simp only [hI, Bool.false_eq_true, ↓reduceIte, Pseudo.oracle, Pseudo.get, resolve, hund]
      split
      all_goals first
        | (exfalso; apply hI; rfl)
        | (show some (GeneralExceptionProcessing modelImpl modelOracle .ReservedInstruction (abs s)) = _
           rw [gep_take s .ReservedInstruction rfl excCodeRI (by decide)])

-- 7C S3 control + system

/-- **MFC0 refines.** Each implemented register's value is `CPRRead` (`cprRead_*`, one lemma per
register); a register coprocessor 0 does not contain is UNDEFINED (`Oracle.cp0Undefined`, the
model's Reserved Instruction). -/
theorem mfc0_refines (s : State) (hg : Good s) (rt rd sel w : W32)
    (hw : enc (.mfc0 rt rd sel) = some w) :
    Execute modelCtx w (.mfc0 rt rd sel) (abs s) = some (abs (execInstr s (.mfc0 rt rd sel))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = fld 6 26 0x10#32 ||| fld 5 21 0x00#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 3 0 sel :=
    (Option.some.inj hw).symm
  have hc0 : InCop0Space w = true := by subst hw'; simp [InCop0Space, opcode_mfc0]
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_mfc0]
  rw [execute_cop0 w _ s _ (.inl rfl) hc1 hc0 rfl, execInstr_cop0 s _ (.inl rfl) rfl rfl]
  cases hu : cp0Usable s
  · rfl
  · simp only [↓reduceIte]
    have hb : execBody s (.mfc0 rt rd sel) =
      (match rd.toNat, sel.toNat with
      | 7, 0 => mkNext s (writeReg s (regIdx rt) s.cp0HWREna)
      | 8, 0 => mkNext s (writeReg s (regIdx rt) s.cp0BadVAddr)
      | 9, 0 => mkNext s (writeReg s (regIdx rt) s.cp0Count)
      | 11, 0 => mkNext s (writeReg s (regIdx rt) s.cp0Compare)
      | 12, 0 => mkNext s (writeReg s (regIdx rt) s.cp0Status)
      | 12, 1 => mkNext s (writeReg s (regIdx rt) intCtlValue)
      | 12, 2 => mkNext s (writeReg s (regIdx rt) srsCtlValue)
      | 13, 0 => mkNext s (writeReg s (regIdx rt) (causeValue s))
      | 14, 0 => mkNext s (writeReg s (regIdx rt) s.cp0Epc)
      | 15, 0 => mkNext s (writeReg s (regIdx rt) prIdValue)
      | 15, 1 => mkNext s (writeReg s (regIdx rt) (ebaseValue s))
      | 16, 0 => mkNext s (writeReg s (regIdx rt) (configValue s))
      | 16, 1 => mkNext s (writeReg s (regIdx rt) config1Value)
      | 30, 0 => mkNext s (writeReg s (regIdx rt) s.cp0ErrorEpc)
      | _, _ => takeException s excCodeRI) := rfl
    rw [hb]; clear hb hw hw' hc0 hc1
    simp only [Pseudo.run, Ops.MFC0, bind, Pseudo.impl, Pseudo.get, ← regIdx_eq_reg,
      show modelCtx.impl = modelImpl from rfl]
    generalize rd.toNat = r
    generalize sel.toNat = q
    by_cases hI : IsCoprocessorRegisterImplemented r q = true
    · simp only [hI, ↓reduceIte, setGPR]
      split <;> simp only [IsCoprocessorRegisterImplemented] at hI <;>
        first
          | (simp only [cprRead_hwrena, cprRead_badvaddr, cprRead_count, cprRead_compare,
              cprRead_status, cprRead_intctl, cprRead_srsctl, cprRead_cause, cprRead_epc, cprRead_prid,
              cprRead_ebase, cprRead_config, cprRead_config1, cprRead_errorepc]
             exact complete_writeReg s hsz _ _)
          | (exfalso; simp at hI)
          | (exfalso; revert hI; split <;> simp_all)
    · have hund : ∀ a i, modelCtx.oracle.cp0Undefined a i = .signal .ReservedInstruction :=
        fun _ _ => rfl
      simp only [hI, Bool.false_eq_true, ↓reduceIte, Pseudo.oracle, resolve, hund]
      split
      all_goals first
        | (exfalso; apply hI; rfl)
        | (show some (GeneralExceptionProcessing modelImpl modelOracle .ReservedInstruction (abs s)) = _
           rw [gep_take s .ReservedInstruction rfl excCodeRI (by decide)])

/-- `Status` with `IE` cleared/set, the manual's `1#32 <<< 0` against the model's mask. -/
theorem ie_mask : (1#32 <<< 0 : W32) = statusIeMask := by decide

/-- The order of `GPR[rt] ← Status` and the `Status.IE` write does not matter. -/
theorem writeGPR_status (a : Arch) (i : Fin 32) (v x : W32) :
    { writeGPR a i v with Status := x } = writeGPR { a with Status := x } i v := by
  unfold writeGPR; split <;> rfl

theorem abs_status (s : State) (x : W32) : abs { s with cp0Status := x } = { abs s with Status := x } :=
  rfl

/-- **DI refines.** -/
theorem di_refines (s : State) (hg : Good s) (rt w : W32) (hw : enc (.di rt) = some w) :
    Execute modelCtx w (.di rt) (abs s) = some (abs (execInstr s (.di rt))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = fld 6 26 0x10#32 ||| fld 5 21 0x0B#32 ||| fld 5 16 rt ||| fld 5 11 12#32 |||
      fld 1 5 0#32 := (Option.some.inj hw).symm
  have hc0 : InCop0Space w = true := by subst hw'; simp [InCop0Space, opcode_di]
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_di]
  rw [execute_cop0 w _ s _ (.inl rfl) hc1 hc0 rfl, execInstr_cop0 s _ (.inl rfl) rfl rfl]
  cases hu : cp0Usable s
  · rfl
  · simp only [↓reduceIte]
    show _ = some (abs (mkNext s (writeReg { s with cp0Status := s.cp0Status &&& ~~~statusIeMask }
      (regIdx rt) s.cp0Status)))
    simp only [Pseudo.run, Ops.DI, bind, Pseudo.get, setGPR, Pseudo.modify, ← regIdx_eq_reg]
    show some (Complete (abs s) { arch := { writeGPR (abs s) (regIdx rt) s.cp0Status with
      Status := (writeGPR (abs s) (regIdx rt) s.cp0Status).Status &&& ~~~(1#32 <<< 0) } }) = _
    have : (writeGPR (abs s) (regIdx rt) s.cp0Status).Status = s.cp0Status := by
      unfold writeGPR; split <;> rfl
    rw [this, writeGPR_status, ie_mask, ← abs_status]
    exact complete_writeReg' s { s with cp0Status := s.cp0Status &&& ~~~statusIeMask } hsz rfl rfl _ _

/-- **EI refines.** -/
theorem ei_refines (s : State) (hg : Good s) (rt w : W32) (hw : enc (.ei rt) = some w) :
    Execute modelCtx w (.ei rt) (abs s) = some (abs (execInstr s (.ei rt))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = fld 6 26 0x10#32 ||| fld 5 21 0x0B#32 ||| fld 5 16 rt ||| fld 5 11 12#32 |||
      fld 1 5 1#32 := (Option.some.inj hw).symm
  have hc0 : InCop0Space w = true := by subst hw'; simp [InCop0Space, opcode_ei]
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_ei]
  rw [execute_cop0 w _ s _ (.inl rfl) hc1 hc0 rfl, execInstr_cop0 s _ (.inl rfl) rfl rfl]
  cases hu : cp0Usable s
  · rfl
  · simp only [↓reduceIte]
    show _ = some (abs (mkNext s (writeReg { s with cp0Status := s.cp0Status ||| statusIeMask }
      (regIdx rt) s.cp0Status)))
    simp only [Pseudo.run, Ops.EI, bind, Pseudo.get, setGPR, Pseudo.modify, ← regIdx_eq_reg]
    show some (Complete (abs s) { arch := { writeGPR (abs s) (regIdx rt) s.cp0Status with
      Status := (writeGPR (abs s) (regIdx rt) s.cp0Status).Status ||| (1#32 <<< 0) } }) = _
    have : (writeGPR (abs s) (regIdx rt) s.cp0Status).Status = s.cp0Status := by
      unfold writeGPR; split <;> rfl
    rw [this, writeGPR_status, ie_mask, ← abs_status]
    exact complete_writeReg' s { s with cp0Status := s.cp0Status ||| statusIeMask } hsz rfl rfl _ _

/-- The model's `SRSCtl.PSS` is 0: the previous shadow set is the normal GPRs (MD00090 Vol III Rev
6.02, Chapter 7, p.103). -/
theorem pss_model : (Ops.SRSCtlPSS modelImpl == 0#4) = true := by decide

/-- **RDPGPR refines.** -/
theorem rdpgpr_refines (s : State) (hg : Good s) (rd rt w : W32) (hw : enc (.rdpgpr rd rt) = some w) :
    Execute modelCtx w (.rdpgpr rd rt) (abs s) = some (abs (execInstr s (.rdpgpr rd rt))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = fld 6 26 0x10#32 ||| fld 5 21 0x0A#32 ||| fld 5 16 rt ||| fld 5 11 rd :=
    (Option.some.inj hw).symm
  have hc0 : InCop0Space w = true := by subst hw'; simp [InCop0Space, opcode_rdpgpr]
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_rdpgpr]
  rw [execute_cop0 w _ s _ (.inl rfl) hc1 hc0 rfl, execInstr_cop0 s _ (.inl rfl) rfl rfl]
  cases hu : cp0Usable s
  · rfl
  · simp only [↓reduceIte]
    show _ = some (abs (mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt)))))
    simp only [Pseudo.run, Ops.RDPGPR, bind, Pseudo.impl, Ops.SGPR, GPR, setGPR,
      readGPR_abs s h0, ← regIdx_eq_reg]
    exact complete_writeReg s hsz _ _

/-- **WRPGPR refines.** -/
theorem wrpgpr_refines (s : State) (hg : Good s) (rd rt w : W32) (hw : enc (.wrpgpr rd rt) = some w) :
    Execute modelCtx w (.wrpgpr rd rt) (abs s) = some (abs (execInstr s (.wrpgpr rd rt))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = fld 6 26 0x10#32 ||| fld 5 21 0x0E#32 ||| fld 5 16 rt ||| fld 5 11 rd :=
    (Option.some.inj hw).symm
  have hc0 : InCop0Space w = true := by subst hw'; simp [InCop0Space, opcode_wrpgpr]
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_wrpgpr]
  rw [execute_cop0 w _ s _ (.inl rfl) hc1 hc0 rfl, execInstr_cop0 s _ (.inl rfl) rfl rfl]
  cases hu : cp0Usable s
  · rfl
  · simp only [↓reduceIte]
    show _ = some (abs (mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt)))))
    simp only [Pseudo.run, Ops.WRPGPR, bind, Pseudo.impl, Ops.setSGPR, GPR, setGPR,
      readGPR_abs s h0, ← regIdx_eq_reg]
    exact complete_writeReg s hsz _ _

end Refine
