import Semantics.Refine.BridgeControl

/-!
# Refine.Cp0 — coprocessor 0 instructions against `execInstr`

The Coprocessor Unusable check of the COP0 encoding space (MD00090 Vol III Rev 6.02 §6.2.22,
p.100), then each register through the spec's field tables (`Manual.CPRRead`/`CPRWrite`) against the
model's layout table (`cp0Layout`, `cp0Read`, `cp0Write`); a register neither implements reads 0
and ignores writes on both sides (Release 6, MFC0 p.266, MTC0 p.290).
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

-- BEGIN R6-2
/-! ## The coprocessor 0 register file: the spec's field tables against the model's layout table -/

/-- The registers the spec implements are the ones the model's layout names. -/
theorem impl_eq_layout (r q : Nat) :
    IsCoprocessorRegisterImplemented r q = (cp0Layout .r6 r q).isSome := by
  unfold IsCoprocessorRegisterImplemented
  split
  all_goals first
    | rfl
    | (unfold cp0Layout; split <;> simp_all)

theorem cprRead_userlocal (s : State) : CPRRead modelImpl 4 2 (abs s) = s.cp0UserLocal := rfl
theorem cprRead_config4 (s : State) : CPRRead modelImpl 16 4 (abs s) = config4Value := rfl

/-- `Config5` (16, 5): the fixed fields with `SBRI`. -/
theorem cprRead_config5 (s : State) : CPRRead modelImpl 16 5 (abs s) = config5Value s := by
  show Config5Read modelImpl (abs s) = config5Value s
  simp only [Config5Read, config5Value, abs]
  by_cases h : s.cp0Config5SBRI = true <;> simp only [h, ↓reduceIte] <;> decide

/-- **MFC0's value of a register the layout names**: `CPRRead` is the model's `cp0Read`. -/
theorem cprRead_layout (s : State) (r q : Nat) (c : Cp0Reg) (h : cp0Layout .r6 r q = some c) :
    CPRRead modelImpl r q (abs s) = cp0Read s c := by
  unfold cp0Layout at h
  split at h <;> cases h <;>
    first
      | rfl
      | exact cprRead_cause s
      | exact cprRead_ebase s
      | exact cprRead_config5 s

theorem config_fields (v : W32) :
    v.extractLsb' 0 3 = v.setWidth 3 ∧ v.extractLsb' 28 3 = (v >>> 28).setWidth 3 ∧
      v.extractLsb' 25 3 = (v >>> 25).setWidth 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp [BitVec.getLsbD_ushiftRight, hi] <;> omega

theorem ebase_write (v : W32) :
    (1#32 <<< 31) ||| (v &&& fieldOnes 29 12) = (v &&& ebaseWriteMask) ||| ebaseFixedBits := by
  rw [fieldOnes_29_12, BitVec.or_comm]; rfl

theorem bit_and_ne (v : W32) (i : Nat) (h : i < 32) : (v &&& BitVec.twoPow 32 i != 0#32) = bit v i := by
  rw [and_twoPow_ne _ _ h]; rfl

/-- **MTC0's write to a register the layout names**: `CPRWrite` is the model's `cp0Write`. -/
theorem cprWrite_layout (s : State) (r q : Nat) (c : Cp0Reg) (v : W32)
    (h : cp0Layout .r6 r q = some c) :
    CPRWrite modelImpl r q v (abs s) = abs (cp0Write s v c) := by
  obtain ⟨hk0, hk23, hku⟩ := config_fields v
  have h6 : (v &&& 0x40#32 != 0#32) = bit v 6 := by
    rw [show (0x40#32 : W32) = BitVec.twoPow 32 6 by decide]; exact bit_and_ne v 6 (by omega)
  have h0 : (v &&& 1#32 != 0#32) = bit v 0 := by
    rw [show (1#32 : W32) = BitVec.twoPow 32 0 by decide]; exact bit_and_ne v 0 (by omega)
  unfold cp0Layout at h
  split at h <;> cases h <;>
    simp only [CPRWrite, cp0Write, statusWritable_eq, causeWritable_eq, hwrenaWritable_eq,
      ebase_write, hk0, hk23, hku, h6, h0] <;>
    first
      | rfl
      | (simp only [abs, updateKScratch]; rfl)
-- END R6-2

/-- **MTC0 refines** (Release 6): a register the spec does not implement ignores the write on both
sides; an implemented one is written through its field table (`cprWrite_layout`); the UNDEFINED
`EBase` write with `BEV = 0` proceeds under the model's choice (`Oracle.ebaseWriteBEV0`). -/
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
  rw [execute_cop0 w _ s _ (.inl rfl) hc1 hc0 rfl, execInstr_cop0 s _ (.inl rfl) rfl rfl]
  cases hu : cp0Usable s
  · rfl
  · simp only [↓reduceIte]
    show _ = some (abs (mkNext s (cp0WriteAt s rd sel (readReg s (regIdx rt)))))
    simp only [Pseudo.run, Ops.MTC0, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg]
    unfold cp0WriteAt
    rw [show profile.release = .r6 from rfl]
    generalize readReg s (regIdx rt) = v
    generalize rd.toNat = r
    generalize sel.toNat = q
    have hI := impl_eq_layout r q
    cases hl : cp0Layout .r6 r q with
    | none =>
      rw [hl] at hI
      simp only [hI, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, pure, complete_plain,
        mkNext]
      rw [abs_advance _ _ rfl]; rfl
    | some c =>
      rw [hl] at hI
      have hEB : ∀ a d, modelCtx.oracle.ebaseWriteBEV0 a d = .proceed := fun _ _ => rfl
      simp only [hI, Option.isSome_some, ↓reduceIte, Pseudo.get, Pseudo.oracle, Pseudo.impl, hEB,
        unpredictableOr, ite_self, Pseudo.modify, complete_plain, mkNext,
        show modelCtx.impl = modelImpl from rfl, cprWrite_layout s r q c v hl]
      rw [abs_advance _ _ (by cases c <;> rfl)]
      cases c <;> rfl

-- 7C S3 control + system

/-- **MFC0 refines** (Release 6): a register the spec does not implement reads 0 on both sides; an
implemented one reads `CPRRead`, the model's `cp0Read` (`cprRead_layout`). -/
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
    show _ = some (abs (mkNext s (writeReg s (regIdx rt) (cp0ReadAt s rd sel))))
    simp only [Pseudo.run, Ops.MFC0, bind, Pseudo.impl, Pseudo.get, ← regIdx_eq_reg,
      show modelCtx.impl = modelImpl from rfl]
    unfold cp0ReadAt
    rw [show profile.release = .r6 from rfl]
    generalize rd.toNat = r
    generalize sel.toNat = q
    have hI := impl_eq_layout r q
    cases hl : cp0Layout .r6 r q with
    | none =>
      rw [hl] at hI
      simp only [hI, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, setGPR]
      exact complete_writeReg s hsz _ _
    | some c =>
      rw [hl] at hI
      simp only [hI, Option.isSome_some, ↓reduceIte, setGPR, cprRead_layout s r q c hl]
      exact complete_writeReg s hsz _ _

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
