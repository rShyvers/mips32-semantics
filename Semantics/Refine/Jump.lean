import Semantics.Refine.BridgeControl

/-!
# Refine.Jump — jumps with a delay slot against `execInstr`

7C S3 proves `j` and `jal`. The target is the J format's 26-bit `instr_index` (MD00086 Vol II-A
Rev 6.06, J p.194, JAL p.195), the low 26 bits of the constructor's `target` on both sides
(`jump_target`). `jr` and `jalr` are deferred (their `hint` field encoding is being revised).
-/

namespace Refine

open Manual

/-- **J refines.** -/
theorem j_refines (s : State) (hg : Good s) (hn : s.nullified = false) (target w : W32)
    (hw : enc (.j target) = some w) :
    Execute modelCtx w (.j target) (abs s) = some (abs (execInstr s (.j target))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = fld 6 26 0x02#32 ||| fld 26 0 target := (Option.some.inj hw).symm
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_j]
  have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_j]
  have hbl : isBranchLike (.j target) = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w _ s t rfl rfl hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    rw [execute_cti_run w _ s (Ops.J target) hpb hc1 hc0 rfl]
    have hex : execInstr s (.j target) =
        { s with pc := s.pc + 4#32,
                 pendingBranch :=
                   some (((s.pc + 4#32) &&& 0xf0000000#32) ||| ((target &&& 0x3FFFFFF#32) <<< 2)) } := by
      unfold execInstr; rw [hbl, hpb]; rfl
    rw [hex]
    simp only [Pseudo.run, Ops.J, bind, PC, jump_target]
    simp [I1, Complete, abs, hn, readReg, readFpReg]

/-- **JAL refines.** -/
theorem jal_refines (s : State) (hg : Good s) (hn : s.nullified = false) (target w : W32)
    (hw : enc (.jal target) = some w) :
    Execute modelCtx w (.jal target) (abs s) = some (abs (execInstr s (.jal target))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = fld 6 26 0x03#32 ||| fld 26 0 target := (Option.some.inj hw).symm
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_jal]
  have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_jal]
  have hbl : isBranchLike (.jal target) = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w _ s t rfl rfl hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    rw [execute_cti_run w _ s (Ops.JAL target) hpb hc1 hc0 rfl]
    have hex : execInstr s (.jal target) =
        { writeReg s 31 (s.pc + 4#32 + 4#32) with
            pc := s.pc + 4#32,
            pendingBranch :=
              some (((s.pc + 4#32) &&& 0xf0000000#32) ||| ((target &&& 0x3FFFFFF#32) <<< 2)) } := by
      unfold execInstr; rw [hbl, hpb]; rfl
    rw [hex]
    simp only [Pseudo.run, Ops.JAL, bind, PC, setGPR, jump_target, abs_pc_pb, abs_writeReg _ _ _ hsz,
      pc_add_eight]
    simp [I1, Complete, writeGPR, abs, hn, readReg, readFpReg]

end Refine
