import Semantics.Refine.Bridge

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

end Refine
