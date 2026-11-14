import Semantics.Refine.BridgeFpuMove

/-!
# Refine.FpuBranch — branches on the FP condition code against `execInstr` (7C S4b)

`BC1F`, `BC1T`, `BC1FL`, `BC1TL`: a CTI in a delay slot is Reserved Instruction on both sides (checked
before the coprocessor, `cop1_cti_execute`); otherwise CU1 = 0 is Coprocessor Unusable; otherwise the
condition code (`fpcc_run`) selects the `I+1:` effect. The branch-likely forms nullify the delay slot
when not taken, on both sides (`I1 .nullify`, `State.nullified`), as the `beql` pilot. As the ordinary
branches, the statement assumes `s.nullified = false` (the spec's completion writes `Nullify`).
-/

namespace Refine

open Manual

/-- **BC1F refines.** -/
theorem bc1f_refines (s : State) (_hg : Good s) (hn : s.nullified = false) (cc off w : W32)
    (hw : enc (.bc1f cc off) = some w) :
    Execute modelCtx w (.bc1f cc off) (abs s) = some (abs (execInstr s (.bc1f cc off))) := by
  have hw' : w = fld 6 26 0x11#32 ||| fld 5 21 0x08#32 ||| fld 3 18 cc ||| fld 1 17 0#32 |||
      fld 1 16 0#32 ||| fld 16 0 off := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_cti_execute s _ _ (Ops.BC1F cc off) rfl rfl (by simp [InCop1Space, opcode_bc1])
    (by simp [InCop0Space, opcode_bc1]) rfl rfl rfl rfl
  intro _ _
  have hb : execBody s (.bc1f cc off) =
      if readFcc s cc then { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }
      else { s with pc := s.pc + 4#32,
                    pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) } := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.BC1F, bind, fpcc_run, abs_FCSR, PC, branch_offset]
  rw [show Mips.Fp.getCC s.fcsr (ccIdx cc) = readFcc s cc from rfl]
  cases readFcc s cc <;> simp [I1, Complete, abs, hn, readReg, readFpReg]

/-- **BC1T refines.** -/
theorem bc1t_refines (s : State) (_hg : Good s) (hn : s.nullified = false) (cc off w : W32)
    (hw : enc (.bc1t cc off) = some w) :
    Execute modelCtx w (.bc1t cc off) (abs s) = some (abs (execInstr s (.bc1t cc off))) := by
  have hw' : w = fld 6 26 0x11#32 ||| fld 5 21 0x08#32 ||| fld 3 18 cc ||| fld 1 17 0#32 |||
      fld 1 16 1#32 ||| fld 16 0 off := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_cti_execute s _ _ (Ops.BC1T cc off) rfl rfl (by simp [InCop1Space, opcode_bc1])
    (by simp [InCop0Space, opcode_bc1]) rfl rfl rfl rfl
  intro _ _
  have hb : execBody s (.bc1t cc off) =
      if readFcc s cc then
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
      else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.BC1T, bind, fpcc_run, abs_FCSR, PC, branch_offset]
  rw [show Mips.Fp.getCC s.fcsr (ccIdx cc) = readFcc s cc from rfl]
  cases readFcc s cc <;> simp [I1, Complete, abs, hn, readReg, readFpReg]

/-- **BC1FL refines** (not taken: the delay slot is nullified). -/
theorem bc1fl_refines (s : State) (_hg : Good s) (hn : s.nullified = false) (cc off w : W32)
    (hw : enc (.bc1fl cc off) = some w) :
    Execute modelCtx w (.bc1fl cc off) (abs s) = some (abs (execInstr s (.bc1fl cc off))) := by
  have hw' : w = fld 6 26 0x11#32 ||| fld 5 21 0x08#32 ||| fld 3 18 cc ||| fld 1 17 1#32 |||
      fld 1 16 0#32 ||| fld 16 0 off := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_cti_execute s _ _ (Ops.BC1FL cc off) rfl rfl (by simp [InCop1Space, opcode_bc1])
    (by simp [InCop0Space, opcode_bc1]) rfl rfl rfl rfl
  intro _ _
  have hb : execBody s (.bc1fl cc off) =
      if readFcc s cc then
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32), nullified := true }
      else { s with pc := s.pc + 4#32,
                    pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) } := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.BC1FL, bind, fpcc_run, abs_FCSR, PC, branch_offset]
  rw [show Mips.Fp.getCC s.fcsr (ccIdx cc) = readFcc s cc from rfl]
  cases readFcc s cc <;> simp [I1, Complete, abs, hn, readReg, readFpReg]

/-- **BC1TL refines** (not taken: the delay slot is nullified). -/
theorem bc1tl_refines (s : State) (_hg : Good s) (hn : s.nullified = false) (cc off w : W32)
    (hw : enc (.bc1tl cc off) = some w) :
    Execute modelCtx w (.bc1tl cc off) (abs s) = some (abs (execInstr s (.bc1tl cc off))) := by
  have hw' : w = fld 6 26 0x11#32 ||| fld 5 21 0x08#32 ||| fld 3 18 cc ||| fld 1 17 1#32 |||
      fld 1 16 1#32 ||| fld 16 0 off := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_cti_execute s _ _ (Ops.BC1TL cc off) rfl rfl (by simp [InCop1Space, opcode_bc1])
    (by simp [InCop0Space, opcode_bc1]) rfl rfl rfl rfl
  intro _ _
  have hb : execBody s (.bc1tl cc off) =
      if readFcc s cc then
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
      else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32), nullified := true } := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.BC1TL, bind, fpcc_run, abs_FCSR, PC, branch_offset]
  rw [show Mips.Fp.getCC s.fcsr (ccIdx cc) = readFcc s cc from rfl]
  cases readFcc s cc <;> simp [I1, Complete, abs, hn, readReg, readFpReg]

end Refine
