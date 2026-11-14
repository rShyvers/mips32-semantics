import Semantics.Refine.Bridge

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

end Refine
