import Semantics.Refine.BridgeControl

/-!
# Refine.Branch — branches with a delay slot against `execInstr`

Sub-wave 7A proves the pilot `beq`. The hypothesis `s.nullified = false` is part of every instruction
time that executes an instruction (`executesInstr`); the spec's completion of a branch writes
`Nullify` (`Manual.Complete`), the model's branch arm leaves it.
-/

namespace Refine

open Manual

/-- **BEQ refines.** -/
theorem beq_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs rt off w : W32)
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
    rw [execute_cti_slot w _ s t rfl rfl hpb]
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
      simp [I1, Complete, abs, hn, readReg, readFpReg]

-- 7C S3 control + system

/-- **BNE refines.** -/
theorem bne_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs rt off w : W32)
    (hw : enc (.bne rs rt off) = some w) :
    Execute modelCtx w (.bne rs rt off) (abs s) = some (abs (execInstr s (.bne rs rt off))) := by
  branch_refine (.bne rs rt off) (iFormat 0x05#32 rs rt off) (Ops.BNE rs rt off)
    (if readReg s (regIdx rs) == readReg s (regIdx rt) then
      { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }
    else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }) =>
    simp only [Pseudo.run, Ops.BNE, bind, GPR, PC, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset, bne]
    cases readReg s (regIdx rs) == readReg s (regIdx rt) <;>
      simp [I1, Complete, abs, hn, readReg, readFpReg]

/-- **BLEZ refines.** -/
theorem blez_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs off w : W32)
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
      simp [I1, Complete, abs, hn, readReg, readFpReg]

/-- **BGTZ refines.** -/
theorem bgtz_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs off w : W32)
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
      simp [I1, Complete, abs, hn, readReg, readFpReg]

/-- **BLTZ refines.** -/
theorem bltz_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs off w : W32)
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
      simp [I1, Complete, abs, hn, readReg, readFpReg]

/-- **BGEZ refines.** -/
theorem bgez_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs off w : W32)
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
      simp [I1, Complete, abs, hn, readReg, readFpReg]

/-- **BLTZAL refines.** The link is written whatever the condition; the model's
`linkSourceIs31` choice is `.proceed` (the Operation as written, `rs` read before the link). -/
theorem bltzal_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs off w : W32)
    (hw : enc (.bltzal rs off) = some w) :
    Execute modelCtx w (.bltzal rs off) (abs s) = some (abs (execInstr s (.bltzal rs off))) := by
  branch_refine (.bltzal rs off) (iFormat 0x01#32 rs 0x10#32 off) (Ops.BLTZAL rs off)
    (if asSigned (readReg s (regIdx rs)) < 0 then
      { writeReg s 31 (s.pc + 4#32 + 4#32) with
          pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
    else { writeReg s 31 (s.pc + 4#32 + 4#32) with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) =>
    simp only [Pseudo.run, Ops.BLTZAL, bind, Pseudo.oracle, Pseudo.get, modelOracle_linkSourceIs31,
      link31_proceed, GPR, PC, setGPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset, slt_zero]
    by_cases hc : asSigned (readReg s (regIdx rs)) < 0 <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
      simp only [abs_pc_pb, abs_writeReg _ _ _ hsz, pc_add_eight] <;>
      simp [I1, Complete, writeGPR, abs, hn, readReg, readFpReg]

/-- **BGEZAL refines.** The link is written whatever the condition; the model's
`linkSourceIs31` choice is `.proceed` (the Operation as written, `rs` read before the link). -/
theorem bgezal_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs off w : W32)
    (hw : enc (.bgezal rs off) = some w) :
    Execute modelCtx w (.bgezal rs off) (abs s) = some (abs (execInstr s (.bgezal rs off))) := by
  branch_refine (.bgezal rs off) (iFormat 0x01#32 rs 0x11#32 off) (Ops.BGEZAL rs off)
    (if 0 ≤ asSigned (readReg s (regIdx rs)) then
      { writeReg s 31 (s.pc + 4#32 + 4#32) with
          pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
    else { writeReg s 31 (s.pc + 4#32 + 4#32) with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) =>
    simp only [Pseudo.run, Ops.BGEZAL, bind, Pseudo.oracle, Pseudo.get, modelOracle_linkSourceIs31,
      link31_proceed, GPR, PC, setGPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset, zero_sle]
    by_cases hc : 0 ≤ asSigned (readReg s (regIdx rs)) <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
      simp only [abs_pc_pb, abs_writeReg _ _ _ hsz, pc_add_eight] <;>
      simp [I1, Complete, writeGPR, abs, hn, readReg, readFpReg]

end Refine
