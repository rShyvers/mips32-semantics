import Semantics.Refine.BridgeControl
import Semantics.Refine.BridgeIntAlu
import Semantics.Refine.Jump
import Semantics.Refine.DecodeDiagram

/-!
# Refine.CompactBranch — the Release 6 compact branches against `execInstr`

`<ctor>_refines` for BC, BALC, the twelve B<cond>C, the six B*ZALC, BOVC and BNVC (JIC/JIALC are in
`Refine/Jump.lean`). Each proof has the shape of `branch_refine` (`Refine/BridgeControl.lean`): in a
delay slot or forbidden slot both sides raise Reserved Instruction (`execute_cti_slot`); otherwise
the Operation runs and its `PC` assignment at time `I` (taken) or `Delay.forbiddenSlot` (not taken)
is the model's arm (`pc := target, pendingBranch := none` or `pc := pc + 4, pendingBranch :=
some (pc + 8)`). The conditions are matched by `slt_w`, `sle_w`, `ule_not_ult`, the comparisons with
zero of `BridgeControl`, and `add_ovf_bne` (BOVC/BNVC).
-/

namespace Refine

open Manual

/-! ## Offsets, comparisons, encodings -/

/-- `sign_extend` of a word is the word. -/
theorem sign_extend_w32 (x : W32) : sign_extend x = x := by
  simp [sign_extend]

/-- `sign_extend(offset || 0^2)` of the 21-bit offset is the model's `signExt21 off <<< 2`. -/
theorem branch_offset21 (off : W32) : sign_extend (bits off 20 0 ++ 0#2) = signExt21 off <<< 2 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [sign_extend, bits, signExt21, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb, BitVec.msb_append]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- `sign_extend(offset || 0^2)` of the 26-bit offset is the model's `signExt26 off <<< 2`. -/
theorem branch_offset26 (off : W32) : sign_extend (bits off 25 0 ++ 0#2) = signExt26 off <<< 2 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [sign_extend, bits, signExt26, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb, BitVec.msb_append]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem sle_w (x y : W32) : x.sle y = decide (asSigned x ≤ asSigned y) := rfl

theorem ule_not_ult (x y : W32) : BitVec.ule y x = !BitVec.ult x y := by
  simp only [BitVec.ule, BitVec.ult]
  by_cases h : x.toNat < y.toNat <;> simp [h] <;> omega

theorem opcode_bc (op off : W32) : opcode (fld 6 26 op ||| fld 26 0 off) = op &&& 0x3F#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [opcode, fld, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem opcode_off21 (op rs off : W32) :
    opcode (fld 6 26 op ||| fld 5 21 rs ||| fld 21 0 off) = op &&& 0x3F#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [opcode, fld, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- The model's oracle lets a compact branch-and-link with `rt = 31` proceed: the Operation as
written (the link, then `GPR[rt]`), the model's order too. -/
theorem modelOracle_linkSourceIs31 (a : Arch) (i : Instruction) :
    modelCtx.oracle.linkSourceIs31 a i = .proceed := rfl

/-- `$zero` still reads 0 after a write (`writeReg` ignores register 0). -/
theorem readReg_zero_writeReg (s : State) (i : Fin 32) (v : W32) (hsz : s.regs.size = 32)
    (h0 : readReg s 0 = 0#32) : readReg (writeReg s i v) 0 = 0#32 := by
  rw [readReg_writeReg s i 0 v hsz]
  split
  · rename_i h; exact absurd h.1.symm h.2
  · exact h0

/-! ## The shape of a compact branch's refinement proof -/

set_option hygiene false in
/-- The common part of the refinement proof of a compact branch `i` (diagram `word`, Operation
`op`): the slot case (Reserved Instruction on both sides), then `fin` on the run of the Operation
against the model's arm (`execBody`, unfolded). Expects `s hg w hw` in scope. -/
macro "cb_refine " i:term:max word:term:max op:term:max " => " fin:tacticSeq : tactic =>
  `(tactic| (
    obtain ⟨hsz, -, h0⟩ := hg
    have hw' : w = $word := by
      first | exact (Option.some.inj hw).symm | exact (encIf_some hw).2.symm
    have hc1 : InCop1Space w = false := by
      subst hw'; simp [InCop1Space, opcode_iFormat, opcode_bc, opcode_off21]
    have hc0 : InCop0Space w = false := by
      subst hw'; simp [InCop0Space, opcode_iFormat, opcode_bc, opcode_off21]
    have hbl : isBranchLike $i = true := rfl
    cases hpb : s.pendingBranch with
    | some t =>
      rw [execute_cti_slot w _ s t rfl hpb]
      unfold execInstr; rw [hbl, hpb]; rfl
    | none =>
      rw [execute_cti_run w _ s $op hpb hc1 hc0 rfl]
      have hex : execInstr s $i = execBody s $i := by
        unfold execInstr; rw [hbl, hpb]; rfl
      rw [hex]
      exec_unfold
      ($fin)))

set_option hygiene false in
/-- Close a conditional compact branch once its condition is the same Boolean `c` on both sides. -/
macro "cb_close " c:term:max : tactic => `(tactic| (
  cases _hc : $c:term <;>
    simp [Ops.CompactIf, Ops.ForbiddenSlot, bind, PC, setPC, I1, Complete, hpb, writeReg_pc,
      writeReg_pendingBranch, abs_pc_pb, _hc]))

/-! ## BC, BALC -/

/-- **BC refines.** -/
theorem bc_refines (s : State) (hg : Good s) (off w : W32) (hw : enc (.bc off) = some w) :
    Execute modelCtx w (.bc off) (abs s) = some (abs (execInstr s (.bc off))) := by
  cb_refine (.bc off) (fld 6 26 0x32#32 ||| fld 26 0 off) (Ops.BC off) =>
    simp only [Pseudo.run, Ops.BC, bind, PC, setPC, branch_offset26, sign_extend_w32]
    simp [Complete, abs, readReg, readFpReg64, hpb]

/-- **BALC refines.** -/
theorem balc_refines (s : State) (hg : Good s) (off w : W32) (hw : enc (.balc off) = some w) :
    Execute modelCtx w (.balc off) (abs s) = some (abs (execInstr s (.balc off))) := by
  cb_refine (.balc off) (fld 6 26 0x3A#32 ||| fld 26 0 off) (Ops.BALC off) =>
    simp only [Pseudo.run, Ops.BALC, bind, PC, setPC, setGPR, branch_offset26, sign_extend_w32]
    rw [← abs_writeReg _ _ _ hsz]
    simp [Complete, abs, readReg, readFpReg64, writeReg_pc]

/-! ## B<cond>C -/

/-- **BEQC refines.** -/
theorem beqc_refines (s : State) (hg : Good s) (rs rt off w : W32) (hw : enc (.beqc rs rt off) = some w) :
    Execute modelCtx w (.beqc rs rt off) (abs s) = some (abs (execInstr s (.beqc rs rt off))) := by
  cb_refine (.beqc rs rt off) (iFormat 0x08#32 rs rt off) (Ops.BEQC rs rt off) =>
    simp only [Pseudo.run, Ops.BEQC, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset]
    cb_close (readReg s (regIdx rs) == readReg s (regIdx rt))

/-- **BNEC refines.** -/
theorem bnec_refines (s : State) (hg : Good s) (rs rt off w : W32) (hw : enc (.bnec rs rt off) = some w) :
    Execute modelCtx w (.bnec rs rt off) (abs s) = some (abs (execInstr s (.bnec rs rt off))) := by
  cb_refine (.bnec rs rt off) (iFormat 0x18#32 rs rt off) (Ops.BNEC rs rt off) =>
    simp only [Pseudo.run, Ops.BNEC, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset]
    cb_close (readReg s (regIdx rs) != readReg s (regIdx rt))

/-- **BLTC refines.** -/
theorem bltc_refines (s : State) (hg : Good s) (rs rt off w : W32) (hw : enc (.bltc rs rt off) = some w) :
    Execute modelCtx w (.bltc rs rt off) (abs s) = some (abs (execInstr s (.bltc rs rt off))) := by
  cb_refine (.bltc rs rt off) (iFormat 0x17#32 rs rt off) (Ops.BLTC rs rt off) =>
    simp only [Pseudo.run, Ops.BLTC, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset, slt_w]
    cb_close (decide (asSigned (readReg s (regIdx rs)) < asSigned (readReg s (regIdx rt))))

/-- **BGEC refines.** -/
theorem bgec_refines (s : State) (hg : Good s) (rs rt off w : W32) (hw : enc (.bgec rs rt off) = some w) :
    Execute modelCtx w (.bgec rs rt off) (abs s) = some (abs (execInstr s (.bgec rs rt off))) := by
  cb_refine (.bgec rs rt off) (iFormat 0x16#32 rs rt off) (Ops.BGEC rs rt off) =>
    simp only [Pseudo.run, Ops.BGEC, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset, sle_w]
    cb_close (decide (asSigned (readReg s (regIdx rt)) ≤ asSigned (readReg s (regIdx rs))))

/-- **BLTUC refines.** -/
theorem bltuc_refines (s : State) (hg : Good s) (rs rt off w : W32) (hw : enc (.bltuc rs rt off) = some w) :
    Execute modelCtx w (.bltuc rs rt off) (abs s) = some (abs (execInstr s (.bltuc rs rt off))) := by
  cb_refine (.bltuc rs rt off) (iFormat 0x07#32 rs rt off) (Ops.BLTUC rs rt off) =>
    simp only [Pseudo.run, Ops.BLTUC, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset]
    cb_close (BitVec.ult (readReg s (regIdx rs)) (readReg s (regIdx rt)))

/-- **BGEUC refines.** -/
theorem bgeuc_refines (s : State) (hg : Good s) (rs rt off w : W32) (hw : enc (.bgeuc rs rt off) = some w) :
    Execute modelCtx w (.bgeuc rs rt off) (abs s) = some (abs (execInstr s (.bgeuc rs rt off))) := by
  cb_refine (.bgeuc rs rt off) (iFormat 0x06#32 rs rt off) (Ops.BGEUC rs rt off) =>
    simp only [Pseudo.run, Ops.BGEUC, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset, ule_not_ult]
    cb_close (BitVec.ult (readReg s (regIdx rs)) (readReg s (regIdx rt)))

/-- **BLEZC refines.** -/
theorem blezc_refines (s : State) (hg : Good s) (rt off w : W32) (hw : enc (.blezc rt off) = some w) :
    Execute modelCtx w (.blezc rt off) (abs s) = some (abs (execInstr s (.blezc rt off))) := by
  cb_refine (.blezc rt off) (iFormat 0x16#32 0#32 rt off) (Ops.BLEZC rt off) =>
    simp only [Pseudo.run, Ops.BLEZC, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset, sle_zero]
    cb_close (decide (asSigned (readReg s (regIdx rt)) ≤ 0))

/-- **BGEZC refines.** -/
theorem bgezc_refines (s : State) (hg : Good s) (rt off w : W32) (hw : enc (.bgezc rt off) = some w) :
    Execute modelCtx w (.bgezc rt off) (abs s) = some (abs (execInstr s (.bgezc rt off))) := by
  cb_refine (.bgezc rt off) (iFormat 0x16#32 rt rt off) (Ops.BGEZC rt off) =>
    simp only [Pseudo.run, Ops.BGEZC, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset, zero_sle]
    cb_close (decide (0 ≤ asSigned (readReg s (regIdx rt))))

/-- **BGTZC refines.** -/
theorem bgtzc_refines (s : State) (hg : Good s) (rt off w : W32) (hw : enc (.bgtzc rt off) = some w) :
    Execute modelCtx w (.bgtzc rt off) (abs s) = some (abs (execInstr s (.bgtzc rt off))) := by
  cb_refine (.bgtzc rt off) (iFormat 0x17#32 0#32 rt off) (Ops.BGTZC rt off) =>
    simp only [Pseudo.run, Ops.BGTZC, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset, zero_slt]
    cb_close (decide (0 < asSigned (readReg s (regIdx rt))))

/-- **BLTZC refines.** -/
theorem bltzc_refines (s : State) (hg : Good s) (rt off w : W32) (hw : enc (.bltzc rt off) = some w) :
    Execute modelCtx w (.bltzc rt off) (abs s) = some (abs (execInstr s (.bltzc rt off))) := by
  cb_refine (.bltzc rt off) (iFormat 0x17#32 rt rt off) (Ops.BLTZC rt off) =>
    simp only [Pseudo.run, Ops.BLTZC, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset, slt_zero]
    cb_close (decide (asSigned (readReg s (regIdx rt)) < 0))

/-- **BEQZC refines.** -/
theorem beqzc_refines (s : State) (hg : Good s) (rs off w : W32) (hw : enc (.beqzc rs off) = some w) :
    Execute modelCtx w (.beqzc rs off) (abs s) = some (abs (execInstr s (.beqzc rs off))) := by
  cb_refine (.beqzc rs off) (fld 6 26 0x36#32 ||| fld 5 21 rs ||| fld 21 0 off) (Ops.BEQZC rs off) =>
    simp only [Pseudo.run, Ops.BEQZC, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset21]
    cb_close (readReg s (regIdx rs) == 0#32)

/-- **BNEZC refines.** -/
theorem bnezc_refines (s : State) (hg : Good s) (rs off w : W32) (hw : enc (.bnezc rs off) = some w) :
    Execute modelCtx w (.bnezc rs off) (abs s) = some (abs (execInstr s (.bnezc rs off))) := by
  cb_refine (.bnezc rs off) (fld 6 26 0x3E#32 ||| fld 5 21 rs ||| fld 21 0 off) (Ops.BNEZC rs off) =>
    simp only [Pseudo.run, Ops.BNEZC, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, branch_offset21]
    cb_close (readReg s (regIdx rs) != 0#32)

/-! ## B{LE,GE,GT,LT,EQ,NE}ZALC

The link is written first, then `GPR[rt]` is read (`rt = 31`: `Oracle.linkSourceIs31`, which the
model resolves as `.proceed`: the Operation as written, `modelOracle_linkSourceIs31`). -/

/-- **BLEZALC refines.** -/
theorem blezalc_refines (s : State) (hg : Good s) (rt off w : W32) (hw : enc (.blezalc rt off) = some w) :
    Execute modelCtx w (.blezalc rt off) (abs s) = some (abs (execInstr s (.blezalc rt off))) := by
  cb_refine (.blezalc rt off) (iFormat 0x06#32 0#32 rt off) (Ops.BLEZALC rt off) =>
    simp only [Pseudo.run, Ops.BLEZALC, Ops.BZALC, bind, Pseudo.oracle, Pseudo.get,
      modelOracle_linkSourceIs31, unpredictable_proceed, PC, setGPR, GPR, branch_offset,
      sign_extend_w32, abs_PC]
    rw [← abs_writeReg _ _ _ hsz, readGPR_abs _ (readReg_zero_writeReg s 31 _ hsz h0),
      ← regIdx_eq_reg]
    try simp only [sle_zero]
    cb_close (decide (asSigned (readReg (writeReg s 31 (s.pc + 4#32)) (regIdx rt)) ≤ 0))

/-- **BGEZALC refines.** -/
theorem bgezalc_refines (s : State) (hg : Good s) (rt off w : W32) (hw : enc (.bgezalc rt off) = some w) :
    Execute modelCtx w (.bgezalc rt off) (abs s) = some (abs (execInstr s (.bgezalc rt off))) := by
  cb_refine (.bgezalc rt off) (iFormat 0x06#32 rt rt off) (Ops.BGEZALC rt off) =>
    simp only [Pseudo.run, Ops.BGEZALC, Ops.BZALC, bind, Pseudo.oracle, Pseudo.get,
      modelOracle_linkSourceIs31, unpredictable_proceed, PC, setGPR, GPR, branch_offset,
      sign_extend_w32, abs_PC]
    rw [← abs_writeReg _ _ _ hsz, readGPR_abs _ (readReg_zero_writeReg s 31 _ hsz h0),
      ← regIdx_eq_reg]
    try simp only [zero_sle]
    cb_close (decide (0 ≤ asSigned (readReg (writeReg s 31 (s.pc + 4#32)) (regIdx rt))))

/-- **BGTZALC refines.** -/
theorem bgtzalc_refines (s : State) (hg : Good s) (rt off w : W32) (hw : enc (.bgtzalc rt off) = some w) :
    Execute modelCtx w (.bgtzalc rt off) (abs s) = some (abs (execInstr s (.bgtzalc rt off))) := by
  cb_refine (.bgtzalc rt off) (iFormat 0x07#32 0#32 rt off) (Ops.BGTZALC rt off) =>
    simp only [Pseudo.run, Ops.BGTZALC, Ops.BZALC, bind, Pseudo.oracle, Pseudo.get,
      modelOracle_linkSourceIs31, unpredictable_proceed, PC, setGPR, GPR, branch_offset,
      sign_extend_w32, abs_PC]
    rw [← abs_writeReg _ _ _ hsz, readGPR_abs _ (readReg_zero_writeReg s 31 _ hsz h0),
      ← regIdx_eq_reg]
    try simp only [zero_slt]
    cb_close (decide (0 < asSigned (readReg (writeReg s 31 (s.pc + 4#32)) (regIdx rt))))

/-- **BLTZALC refines.** -/
theorem bltzalc_refines (s : State) (hg : Good s) (rt off w : W32) (hw : enc (.bltzalc rt off) = some w) :
    Execute modelCtx w (.bltzalc rt off) (abs s) = some (abs (execInstr s (.bltzalc rt off))) := by
  cb_refine (.bltzalc rt off) (iFormat 0x07#32 rt rt off) (Ops.BLTZALC rt off) =>
    simp only [Pseudo.run, Ops.BLTZALC, Ops.BZALC, bind, Pseudo.oracle, Pseudo.get,
      modelOracle_linkSourceIs31, unpredictable_proceed, PC, setGPR, GPR, branch_offset,
      sign_extend_w32, abs_PC]
    rw [← abs_writeReg _ _ _ hsz, readGPR_abs _ (readReg_zero_writeReg s 31 _ hsz h0),
      ← regIdx_eq_reg]
    try simp only [slt_zero]
    cb_close (decide (asSigned (readReg (writeReg s 31 (s.pc + 4#32)) (regIdx rt)) < 0))

/-- **BEQZALC refines.** -/
theorem beqzalc_refines (s : State) (hg : Good s) (rt off w : W32) (hw : enc (.beqzalc rt off) = some w) :
    Execute modelCtx w (.beqzalc rt off) (abs s) = some (abs (execInstr s (.beqzalc rt off))) := by
  cb_refine (.beqzalc rt off) (iFormat 0x08#32 0#32 rt off) (Ops.BEQZALC rt off) =>
    simp only [Pseudo.run, Ops.BEQZALC, Ops.BZALC, bind, Pseudo.oracle, Pseudo.get,
      modelOracle_linkSourceIs31, unpredictable_proceed, PC, setGPR, GPR, branch_offset,
      sign_extend_w32, abs_PC]
    rw [← abs_writeReg _ _ _ hsz, readGPR_abs _ (readReg_zero_writeReg s 31 _ hsz h0),
      ← regIdx_eq_reg]
    try simp only [beq_self_eq_true]
    cb_close (readReg (writeReg s 31 (s.pc + 4#32)) (regIdx rt) == 0#32)

/-- **BNEZALC refines.** -/
theorem bnezalc_refines (s : State) (hg : Good s) (rt off w : W32) (hw : enc (.bnezalc rt off) = some w) :
    Execute modelCtx w (.bnezalc rt off) (abs s) = some (abs (execInstr s (.bnezalc rt off))) := by
  cb_refine (.bnezalc rt off) (iFormat 0x18#32 0#32 rt off) (Ops.BNEZALC rt off) =>
    simp only [Pseudo.run, Ops.BNEZALC, Ops.BZALC, bind, Pseudo.oracle, Pseudo.get,
      modelOracle_linkSourceIs31, unpredictable_proceed, PC, setGPR, GPR, branch_offset,
      sign_extend_w32, abs_PC]
    rw [← abs_writeReg _ _ _ hsz, readGPR_abs _ (readReg_zero_writeReg s 31 _ hsz h0),
      ← regIdx_eq_reg]
    try simp only [beq_self_eq_true]
    cb_close (readReg (writeReg s 31 (s.pc + 4#32)) (regIdx rt) != 0#32)

/-! ## BOVC, BNVC -/

/-- **BOVC refines.** -/
theorem bovc_refines (s : State) (hg : Good s) (rs rt off w : W32) (hw : enc (.bovc rs rt off) = some w) :
    Execute modelCtx w (.bovc rs rt off) (abs s) = some (abs (execInstr s (.bovc rs rt off))) := by
  cb_refine (.bovc rs rt off) (iFormat 0x08#32 rs rt off) (Ops.BOVC rs rt off) =>
    simp only [Pseudo.run, Ops.BOVC, Ops.SumOverflow, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg,
      branch_offset, add_ovf_bne]
    cb_close (addOverflows (asSigned (readReg s (regIdx rs))) (asSigned (readReg s (regIdx rt)))
      (asSigned (readReg s (regIdx rs) + readReg s (regIdx rt))))

/-- **BNVC refines.** -/
theorem bnvc_refines (s : State) (hg : Good s) (rs rt off w : W32) (hw : enc (.bnvc rs rt off) = some w) :
    Execute modelCtx w (.bnvc rs rt off) (abs s) = some (abs (execInstr s (.bnvc rs rt off))) := by
  cb_refine (.bnvc rs rt off) (iFormat 0x18#32 rs rt off) (Ops.BNVC rs rt off) =>
    simp only [Pseudo.run, Ops.BNVC, Ops.SumOverflow, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg,
      branch_offset, add_ovf_bne]
    cb_close (addOverflows (asSigned (readReg s (regIdx rs))) (asSigned (readReg s (regIdx rt)))
      (asSigned (readReg s (regIdx rs) + readReg s (regIdx rt))))

end Refine
