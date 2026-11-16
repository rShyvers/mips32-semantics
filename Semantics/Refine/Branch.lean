import Semantics.Refine.BridgeControl

/-!
# Refine.Branch — branches with a delay slot against `execInstr`

Sub-wave 7A proves the pilot `beq`; wave R6-1 the Release 6 `NAL` and `BAL` (Release 6 removed the
other forms of `BLTZAL`/`BGEZAL`).
-/

namespace Refine

open Manual

/-- **BEQ refines.** -/
theorem beq_refines (s : State) (hg : Good s) (rs rt off w : W32)
    (hw : enc (.beq rs rt off) = some w) :
    Execute modelCtx w (.beq rs rt off) (abs s) = some (abs (execInstr s (.beq rs rt off))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = iFormat 0x04#32 rs rt off := by
    have : enc (.beq rs rt off) = some (iFormat 0x04#32 rs rt off) := rfl
    rw [this] at hw; exact (Option.some.inj hw).symm
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_iFormat]
  have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_iFormat]
  have hbl : isBranchLike (.beq rs rt off) = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w _ s t rfl hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    rw [execute_cti_run w _ s (Ops.BEQ rs rt off) hpb hc1 hc0 rfl]
    have hex : execInstr s (.beq rs rt off) =
        (if readReg s (regIdx rs) == readReg s (regIdx rt) then
          { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
        else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
      unfold execInstr; rw [hbl, hpb]; rfl
    rw [hex]
    simp only [Pseudo.run, Ops.BEQ, bind, GPR, PC, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset]
    cases readReg s (regIdx rs) == readReg s (regIdx rt) <;>
      simp [I1, Complete, abs, readReg, readFpReg]

-- 7C S3 control + system

/-- **BNE refines.** -/
theorem bne_refines (s : State) (hg : Good s) (rs rt off w : W32)
    (hw : enc (.bne rs rt off) = some w) :
    Execute modelCtx w (.bne rs rt off) (abs s) = some (abs (execInstr s (.bne rs rt off))) := by
  branch_refine (.bne rs rt off) (iFormat 0x05#32 rs rt off) (Ops.BNE rs rt off)
    (if readReg s (regIdx rs) == readReg s (regIdx rt) then
      { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }
    else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }) =>
    simp only [Pseudo.run, Ops.BNE, bind, GPR, PC, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset, bne]
    cases readReg s (regIdx rs) == readReg s (regIdx rt) <;>
      simp [I1, Complete, abs, readReg, readFpReg]

/-- **BLEZ refines.** -/
theorem blez_refines (s : State) (hg : Good s) (rs off w : W32)
    (hw : enc (.blez rs off) = some w) :
    Execute modelCtx w (.blez rs off) (abs s) = some (abs (execInstr s (.blez rs off))) := by
  branch_refine (.blez rs off) (iFormat 0x06#32 rs 0#32 off) (Ops.BLEZ rs off)
    (if asSigned (readReg s (regIdx rs)) ≤ 0 then
      { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
    else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) =>
    simp only [Pseudo.run, Ops.BLEZ, bind, GPR, PC, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset,
      sle_zero]
    by_cases hc : asSigned (readReg s (regIdx rs)) ≤ 0 <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
      simp [I1, Complete, abs, readReg, readFpReg]

/-- **BGTZ refines.** -/
theorem bgtz_refines (s : State) (hg : Good s) (rs off w : W32)
    (hw : enc (.bgtz rs off) = some w) :
    Execute modelCtx w (.bgtz rs off) (abs s) = some (abs (execInstr s (.bgtz rs off))) := by
  branch_refine (.bgtz rs off) (iFormat 0x07#32 rs 0#32 off) (Ops.BGTZ rs off)
    (if 0 < asSigned (readReg s (regIdx rs)) then
      { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
    else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) =>
    simp only [Pseudo.run, Ops.BGTZ, bind, GPR, PC, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset,
      zero_slt]
    by_cases hc : 0 < asSigned (readReg s (regIdx rs)) <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
      simp [I1, Complete, abs, readReg, readFpReg]

/-- **BLTZ refines.** -/
theorem bltz_refines (s : State) (hg : Good s) (rs off w : W32)
    (hw : enc (.bltz rs off) = some w) :
    Execute modelCtx w (.bltz rs off) (abs s) = some (abs (execInstr s (.bltz rs off))) := by
  branch_refine (.bltz rs off) (iFormat 0x01#32 rs 0x00#32 off) (Ops.BLTZ rs off)
    (if asSigned (readReg s (regIdx rs)) < 0 then
      { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
    else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) =>
    simp only [Pseudo.run, Ops.BLTZ, bind, GPR, PC, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset,
      slt_zero]
    by_cases hc : asSigned (readReg s (regIdx rs)) < 0 <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
      simp [I1, Complete, abs, readReg, readFpReg]

/-- **BGEZ refines.** -/
theorem bgez_refines (s : State) (hg : Good s) (rs off w : W32)
    (hw : enc (.bgez rs off) = some w) :
    Execute modelCtx w (.bgez rs off) (abs s) = some (abs (execInstr s (.bgez rs off))) := by
  branch_refine (.bgez rs off) (iFormat 0x01#32 rs 0x01#32 off) (Ops.BGEZ rs off)
    (if 0 ≤ asSigned (readReg s (regIdx rs)) then
      { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
    else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) =>
    simp only [Pseudo.run, Ops.BGEZ, bind, GPR, PC, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset,
      zero_sle]
    by_cases hc : 0 ≤ asSigned (readReg s (regIdx rs)) <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
      simp [I1, Complete, abs, readReg, readFpReg]

/-- **NAL refines** (Release 6): the link `GPR[31] ← PC + 8`, and the delay slot of a not-taken
branch on both sides (`pendingBranch = some (pc + 8)`, `Delay.fallThrough`). -/
theorem nal_refines (s : State) (hg : Good s) (off w : W32)
    (hw : enc (.nal off) = some w) :
    Execute modelCtx w (.nal off) (abs s) = some (abs (execInstr s (.nal off))) := by
  branch_refine (.nal off) (iFormat 0x01#32 0#32 0x10#32 off) (Ops.NAL off)
    { writeReg s 31 (s.pc + 8#32) with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } =>
    simp only [Pseudo.run, Ops.NAL, bind, PC, setGPR]
    simp only [abs_pc_pb, abs_writeReg _ _ _ hsz]
    simp [I1, Complete, writeGPR, abs, readReg, readFpReg]

/-- **BAL refines** (Release 6): the link `GPR[31] ← PC + 8` and the jump to `PC + 4 + offset`. -/
theorem bal_refines (s : State) (hg : Good s) (off w : W32)
    (hw : enc (.bal off) = some w) :
    Execute modelCtx w (.bal off) (abs s) = some (abs (execInstr s (.bal off))) := by
  branch_refine (.bal off) (iFormat 0x01#32 0#32 0x11#32 off) (Ops.BAL off)
    { writeReg s 31 (s.pc + 4#32 + 4#32) with
        pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) } =>
    simp only [Pseudo.run, Ops.BAL, bind, PC, setGPR, branch_offset]
    simp only [abs_pc_pb, abs_writeReg _ _ _ hsz, pc_add_eight]
    simp [I1, Complete, writeGPR, abs, readReg, readFpReg]

end Refine
