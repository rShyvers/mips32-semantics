import Semantics.Refine.BridgeControl

/-!
# Refine.BranchLikely — branch-likely instructions against `execInstr`

Sub-wave 7A proves the pilot `beql`: the not-taken case nullifies the delay slot in its own
instruction time on both sides (`Manual.Delay.nullify`, `State.nullified`; SPEC-NOTES §9 item 1b).
-/

namespace Refine

open Manual

/-- **BEQL refines.** -/
theorem beql_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs rt off w : W32)
    (hw : enc (.beql rs rt off) = some w) :
    Execute modelCtx w (.beql rs rt off) (abs s) = some (abs (execInstr s (.beql rs rt off))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = iFormat 0x14#32 rs rt off := by
    have : enc (.beql rs rt off) = some (iFormat 0x14#32 rs rt off) := rfl
    rw [this] at hw; exact (Option.some.inj hw).symm
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_iFormat]
  have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_iFormat]
  have hbl : isBranchLike (.beql rs rt off) = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w _ s t rfl rfl hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    rw [execute_cti_run w _ s (Ops.BEQL rs rt off) hpb hc1 hc0 rfl]
    have hex : execInstr s (.beql rs rt off) =
        (if readReg s (regIdx rs) == readReg s (regIdx rt) then
          { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
        else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32), nullified := true }) := by
      unfold execInstr; rw [hbl, hpb]; rfl
    rw [hex]
    simp only [Pseudo.run, Ops.BEQL, bind, GPR, PC, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset]
    cases readReg s (regIdx rs) == readReg s (regIdx rt) <;>
      simp [I1, Complete, abs, hn, readReg, readFpReg]

-- 7C S3 control + system

/-- **BNEL refines.** -/
theorem bnel_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs rt off w : W32)
    (hw : enc (.bnel rs rt off) = some w) :
    Execute modelCtx w (.bnel rs rt off) (abs s) = some (abs (execInstr s (.bnel rs rt off))) := by
  branch_refine (.bnel rs rt off) (iFormat 0x15#32 rs rt off) (Ops.BNEL rs rt off)
    (if readReg s (regIdx rs) == readReg s (regIdx rt) then
      { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32), nullified := true }
    else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }) =>
    simp only [Pseudo.run, Ops.BNEL, bind, GPR, PC, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset, bne]
    cases readReg s (regIdx rs) == readReg s (regIdx rt) <;>
      simp [I1, Complete, abs, hn, readReg, readFpReg]

/-- **BLEZL refines.** -/
theorem blezl_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs off w : W32)
    (hw : enc (.blezl rs off) = some w) :
    Execute modelCtx w (.blezl rs off) (abs s) = some (abs (execInstr s (.blezl rs off))) := by
  branch_refine (.blezl rs off) (iFormat 0x16#32 rs 0#32 off) (Ops.BLEZL rs off)
    (if asSigned (readReg s (regIdx rs)) ≤ 0 then
      { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
    else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32), nullified := true }) =>
    simp only [Pseudo.run, Ops.BLEZL, bind, GPR, PC, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset,
      sle_zero]
    by_cases hc : asSigned (readReg s (regIdx rs)) ≤ 0 <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
      simp [I1, Complete, abs, hn, readReg, readFpReg]

/-- **BGTZL refines.** -/
theorem bgtzl_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs off w : W32)
    (hw : enc (.bgtzl rs off) = some w) :
    Execute modelCtx w (.bgtzl rs off) (abs s) = some (abs (execInstr s (.bgtzl rs off))) := by
  branch_refine (.bgtzl rs off) (iFormat 0x17#32 rs 0#32 off) (Ops.BGTZL rs off)
    (if 0 < asSigned (readReg s (regIdx rs)) then
      { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
    else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32), nullified := true }) =>
    simp only [Pseudo.run, Ops.BGTZL, bind, GPR, PC, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset,
      zero_slt]
    by_cases hc : 0 < asSigned (readReg s (regIdx rs)) <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
      simp [I1, Complete, abs, hn, readReg, readFpReg]

/-- **BLTZL refines.** -/
theorem bltzl_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs off w : W32)
    (hw : enc (.bltzl rs off) = some w) :
    Execute modelCtx w (.bltzl rs off) (abs s) = some (abs (execInstr s (.bltzl rs off))) := by
  branch_refine (.bltzl rs off) (iFormat 0x01#32 rs 0x02#32 off) (Ops.BLTZL rs off)
    (if asSigned (readReg s (regIdx rs)) < 0 then
      { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
    else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32), nullified := true }) =>
    simp only [Pseudo.run, Ops.BLTZL, bind, GPR, PC, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset,
      slt_zero]
    by_cases hc : asSigned (readReg s (regIdx rs)) < 0 <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
      simp [I1, Complete, abs, hn, readReg, readFpReg]

/-- **BGEZL refines.** -/
theorem bgezl_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs off w : W32)
    (hw : enc (.bgezl rs off) = some w) :
    Execute modelCtx w (.bgezl rs off) (abs s) = some (abs (execInstr s (.bgezl rs off))) := by
  branch_refine (.bgezl rs off) (iFormat 0x01#32 rs 0x03#32 off) (Ops.BGEZL rs off)
    (if 0 ≤ asSigned (readReg s (regIdx rs)) then
      { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
    else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32), nullified := true }) =>
    simp only [Pseudo.run, Ops.BGEZL, bind, GPR, PC, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset,
      zero_sle]
    by_cases hc : 0 ≤ asSigned (readReg s (regIdx rs)) <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
      simp [I1, Complete, abs, hn, readReg, readFpReg]

/-- **BLTZALL refines.** The link is written whatever the condition; the model's
`linkSourceIs31` choice is `.proceed` (the Operation as written, `rs` read before the link). -/
theorem bltzall_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs off w : W32)
    (hw : enc (.bltzall rs off) = some w) :
    Execute modelCtx w (.bltzall rs off) (abs s) = some (abs (execInstr s (.bltzall rs off))) := by
  branch_refine (.bltzall rs off) (iFormat 0x01#32 rs 0x12#32 off) (Ops.BLTZALL rs off)
    (if asSigned (readReg s (regIdx rs)) < 0 then
      { writeReg s 31 (s.pc + 4#32 + 4#32) with
          pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
    else
      { writeReg s 31 (s.pc + 4#32 + 4#32) with
          pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32), nullified := true }) =>
    simp only [Pseudo.run, Ops.BLTZALL, bind, Pseudo.oracle, Pseudo.get, modelOracle_linkSourceIs31,
      link31_proceed, GPR, PC, setGPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset, slt_zero]
    by_cases hc : asSigned (readReg s (regIdx rs)) < 0 <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
      simp only [abs_pc_pb_n, abs_writeReg _ _ _ hsz, pc_add_eight] <;>
      simp [I1, Complete, writeGPR, abs, hn, readReg, readFpReg, writeReg_nullified]

/-- **BGEZALL refines.** The link is written whatever the condition; the model's
`linkSourceIs31` choice is `.proceed` (the Operation as written, `rs` read before the link). -/
theorem bgezall_refines (s : State) (hg : Good s) (hn : s.nullified = false) (rs off w : W32)
    (hw : enc (.bgezall rs off) = some w) :
    Execute modelCtx w (.bgezall rs off) (abs s) = some (abs (execInstr s (.bgezall rs off))) := by
  branch_refine (.bgezall rs off) (iFormat 0x01#32 rs 0x13#32 off) (Ops.BGEZALL rs off)
    (if 0 ≤ asSigned (readReg s (regIdx rs)) then
      { writeReg s 31 (s.pc + 4#32 + 4#32) with
          pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
    else
      { writeReg s 31 (s.pc + 4#32 + 4#32) with
          pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32), nullified := true }) =>
    simp only [Pseudo.run, Ops.BGEZALL, bind, Pseudo.oracle, Pseudo.get, modelOracle_linkSourceIs31,
      link31_proceed, GPR, PC, setGPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset, zero_sle]
    by_cases hc : 0 ≤ asSigned (readReg s (regIdx rs)) <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
      simp only [abs_pc_pb_n, abs_writeReg _ _ _ hsz, pc_add_eight] <;>
      simp [I1, Complete, writeGPR, abs, hn, readReg, readFpReg, writeReg_nullified]

end Refine
