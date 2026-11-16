import Semantics.Refine.BridgeControl
import Semantics.Refine.BridgeIntAlu

/-!
# Refine.Jump — jumps with a delay slot against `execInstr`

`j` and `jal`. The target is the J format's 26-bit `instr_index` (MD00086 Vol II-A
Rev 6.06, J p.194, JAL p.195), the low 26 bits of the constructor's `target` on both sides
(`jump_target`). Also `jr`, `jalr` and the hazard-barrier forms `jrHb`, `jalrHb`
(JR p.206, JALR p.196, JR.HB p.208, JALR.HB p.198; hint 0 and hint `10000` are separate
constructors).
-/

namespace Refine

open Manual

/-- **J refines.** -/
theorem j_refines (s : State) (hg : Good s) (target w : W32)
    (hw : enc (.j target) = some w) :
    Execute modelCtx w (.j target) (abs s) = some (abs (execInstr s (.j target))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = fld 6 26 0x02#32 ||| fld 26 0 target := (Option.some.inj hw).symm
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_j]
  have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_j]
  have hbl : isBranchLike (.j target) = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w _ s t rfl hpb]
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
    simp [I1, Complete, abs, readReg, readFpReg64]

/-- **JAL refines.** -/
theorem jal_refines (s : State) (hg : Good s) (target w : W32)
    (hw : enc (.jal target) = some w) :
    Execute modelCtx w (.jal target) (abs s) = some (abs (execInstr s (.jal target))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = fld 6 26 0x03#32 ||| fld 26 0 target := (Option.some.inj hw).symm
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_jal]
  have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_jal]
  have hbl : isBranchLike (.jal target) = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w _ s t rfl hpb]
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
    simp [I1, Complete, writeGPR, abs, readReg, readFpReg64]

/-- The model's oracle lets `JALR`/`JALR.HB` with `rs = rd` proceed: `temp` is read before
`GPR[rd]` is written, the model's order too. -/
theorem modelOracle_jalrRsIsRd (a : Arch) (i : Instruction) :
    modelCtx.oracle.jalrRsIsRd a i = .proceed := rfl

/-- An UNPREDICTABLE condition resolved as `.proceed` leaves the body. -/
theorem unpredictable_proceed (p : Prop) [Decidable p] (body : Pseudo Unit) :
    (if p then unpredictableOr .proceed body else body) = body := by
  split <;> rfl

/-- `Config1.CA` (bit 2) is 0 in `modelImpl`: no MIPS16e, so `JR`/`JALR` jump to `temp`. -/
theorem config1_ca : bit modelImpl.Config1 2 = false := rfl

/-- **JALR refines**, `rs = rd` included (`modelOracle_jalrRsIsRd`). -/
theorem jalr_refines (s : State) (hg : Good s) (rs rd w : W32)
    (hw : enc (.jalr rs rd) = some w) :
    Execute modelCtx w (.jalr rs rd) (abs s) = some (abs (execInstr s (.jalr rs rd))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  obtain rfl : rFormat 0#32 rs 0#32 rd 0#32 0x09#32 = w := Option.some.inj hw
  have hbl : isBranchLike (.jalr rs rd) = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot _ _ s t rfl hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    rw [execute_cti_run _ _ s (Ops.JALR rs rd) hpb (by alu_space) (by alu_space) rfl]
    have hex : execInstr s (.jalr rs rd) =
        { writeReg s (regIdx rd) (s.pc + 4#32 + 4#32) with
            pc := s.pc + 4#32, pendingBranch := some (readReg s (regIdx rs)) } := by
      unfold execInstr; rw [hbl, hpb]; rfl
    rw [hex]
    simp only [Pseudo.run, Ops.JALR, bind, Pseudo.impl, Pseudo.oracle, Pseudo.get, GPR, PC, setGPR,
      show modelCtx.impl = modelImpl from rfl, modelOracle_jalrRsIsRd, unpredictable_proceed,
      config1_ca, Bool.not_false, ↓reduceIte, readGPR_abs s h0, ← regIdx_eq_reg, abs_pc_pb,
      abs_writeReg _ _ _ hsz, pc_add_eight]
    by_cases hd : regIdx rd = 0 <;> simp [I1, Complete, writeGPR, abs, readReg, readFpReg64, hd]

/-- **JALR.HB refines**, `rs = rd` included. -/
theorem jalrHb_refines (s : State) (hg : Good s) (rs rd w : W32)
    (hw : enc (.jalrHb rs rd) = some w) :
    Execute modelCtx w (.jalrHb rs rd) (abs s) = some (abs (execInstr s (.jalrHb rs rd))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  obtain rfl : rFormat 0#32 rs 0#32 rd 0x10#32 0x09#32 = w := Option.some.inj hw
  have hbl : isBranchLike (.jalrHb rs rd) = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot _ _ s t rfl hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    rw [execute_cti_run _ _ s (Ops.JALR_HB rs rd) hpb (by alu_space) (by alu_space) rfl]
    have hex : execInstr s (.jalrHb rs rd) =
        { writeReg s (regIdx rd) (s.pc + 4#32 + 4#32) with
            pc := s.pc + 4#32, pendingBranch := some (readReg s (regIdx rs)) } := by
      unfold execInstr; rw [hbl, hpb]; rfl
    rw [hex]
    simp only [Pseudo.run, Ops.JALR_HB, bind, Pseudo.impl, Pseudo.oracle, Pseudo.get, GPR, PC, setGPR,
      show modelCtx.impl = modelImpl from rfl, modelOracle_jalrRsIsRd, unpredictable_proceed,
      config1_ca, Bool.not_false, ↓reduceIte, readGPR_abs s h0, ← regIdx_eq_reg, abs_pc_pb,
      abs_writeReg _ _ _ hsz, pc_add_eight]
    by_cases hd : regIdx rd = 0 <;> simp [I1, Complete, writeGPR, abs, readReg, readFpReg64, hd]

/-! ## The Release 6 compact jumps (JIC p.205, JIALC p.203)

No delay slot and no forbidden slot: `PC ← temp` at time `I` on both sides. `modelImpl` has
`Config3.ISA = 0` and `Config1.CA = 0` (`compact_isa`), so the first arm of the Operation is taken. -/

/-- `(Config3ISA = 0) and (Config1CA = 0)` in `modelImpl`. -/
theorem compact_isa : (bits modelImpl.Config3 15 14 == 0#2 && !bit modelImpl.Config1 2) = true := by
  decide

/-- **JIC refines.** -/
theorem jic_refines (s : State) (hg : Good s) (rt off w : W32) (hw : enc (.jic rt off) = some w) :
    Execute modelCtx w (.jic rt off) (abs s) = some (abs (execInstr s (.jic rt off))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = iFormat 0x36#32 0#32 rt off := (Option.some.inj hw).symm
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_iFormat]
  have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_iFormat]
  have hbl : isBranchLike (.jic rt off) = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w _ s t rfl hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    rw [execute_cti_run w _ s (Ops.JIC rt off) hpb hc1 hc0 rfl]
    have hex : execInstr s (.jic rt off) =
        { s with pc := readReg s (regIdx rt) + signExt16 off, pendingBranch := none } := by
      unfold execInstr; rw [hbl, hpb]; rfl
    rw [hex]
    simp only [Pseudo.run, Ops.JIC, bind, Pseudo.impl, GPR, readGPR_abs s h0, ← regIdx_eq_reg, offset16,
      show modelCtx.impl = modelImpl from rfl, compact_isa, ↓reduceIte, setPC, abs_pc_pb]
    simp [Complete]

/-- **JIALC refines** (`temp` is read before `GPR[31]` is written, on both sides). -/
theorem jialc_refines (s : State) (hg : Good s) (rt off w : W32) (hw : enc (.jialc rt off) = some w) :
    Execute modelCtx w (.jialc rt off) (abs s) = some (abs (execInstr s (.jialc rt off))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = iFormat 0x3E#32 0#32 rt off := (Option.some.inj hw).symm
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_iFormat]
  have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_iFormat]
  have hbl : isBranchLike (.jialc rt off) = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w _ s t rfl hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    rw [execute_cti_run w _ s (Ops.JIALC rt off) hpb hc1 hc0 rfl]
    have hex : execInstr s (.jialc rt off) =
        { writeReg s 31 (s.pc + 4#32) with
            pc := readReg s (regIdx rt) + signExt16 off, pendingBranch := none } := by
      unfold execInstr; rw [hbl, hpb]; rfl
    rw [hex]
    simp only [Pseudo.run, Ops.JIALC, bind, Pseudo.impl, GPR, readGPR_abs s h0, ← regIdx_eq_reg,
      offset16, PC, setGPR, abs_PC, show modelCtx.impl = modelImpl from rfl, compact_isa, ↓reduceIte,
      setPC, abs_pc_pb]
    rw [← abs_writeReg _ _ _ hsz]
    simp [Complete]

end Refine
