import Semantics.Refine.Fetch

/-!
# Refine.BridgeControl — bridge lemmas for the control and system instructions (7C S3)

Facts used by `Refine/{Branch,BranchLikely,Jump,Cp0,System}.lean`: the signed comparisons with zero
(`BitVec.sle`/`slt` against the model's `asSigned`), the jump-target concatenation, the encoding
spaces of the COP0/SPECIAL3/J-format words, `Execute` for a COP0 instruction, and the value of each
coprocessor 0 register as `MFC0` reads it (`Manual.CPRRead` against the model's `mfc0` arm).
-/

namespace Refine

open Manual

/-! ## Signed comparisons with zero -/

theorem sle_zero (x : W32) : x.sle 0#32 = decide (asSigned x ≤ 0) := by
  rw [Bool.eq_iff_iff]; simp only [BitVec.sle, asSigned, BitVec.toInt_zero, decide_eq_true_eq]
  exact ⟨decide_eq_true, of_decide_eq_true⟩

theorem zero_slt (x : W32) : BitVec.slt 0#32 x = decide (0 < asSigned x) := by
  rw [Bool.eq_iff_iff]; simp only [BitVec.slt, asSigned, BitVec.toInt_zero, decide_eq_true_eq]
  exact ⟨decide_eq_true, of_decide_eq_true⟩

theorem slt_zero (x : W32) : x.slt 0#32 = decide (asSigned x < 0) := by
  rw [Bool.eq_iff_iff]; simp only [BitVec.slt, asSigned, BitVec.toInt_zero, decide_eq_true_eq]
  exact ⟨decide_eq_true, of_decide_eq_true⟩

theorem zero_sle (x : W32) : BitVec.sle 0#32 x = decide (0 ≤ asSigned x) := by
  rw [Bool.eq_iff_iff]; simp only [BitVec.sle, asSigned, BitVec.toInt_zero, decide_eq_true_eq]
  exact ⟨decide_eq_true, of_decide_eq_true⟩

theorem pc_add_eight (p : W32) : p + 4#32 + 4#32 = p + 8#32 := by
  rw [BitVec.add_assoc]; rfl

/-! ## The model's UNPREDICTABLE choices of the control instructions -/

/-- `linkSourceIs31` of the model is `.proceed`: the body of a branch-and-link runs as written. -/
theorem link31_proceed (c : Bool) (body : Pseudo Unit) :
    (if c = true then unpredictableOr .proceed body else body) = body := by
  split <;> rfl

theorem modelOracle_linkSourceIs31 (a : Arch) (i : Instruction) :
    modelCtx.oracle.linkSourceIs31 a i = .proceed := rfl

theorem writeReg_nullified (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).nullified = s.nullified := by
  unfold writeReg; split <;> rfl

/-- The model's state with a new `pc` and `pendingBranch`, seen through `abs`. -/
theorem abs_pc_pb (s : State) (p : W32) (b : Option W32) :
    abs { s with pc := p, pendingBranch := b } = { abs s with PC := p, BranchDelay := b } := rfl

/-- The model's state with a new `pc`, `pendingBranch` and `nullified`, seen through `abs`. -/
theorem abs_pc_pb_n (s : State) (p : W32) (b : Option W32) (n : Bool) :
    abs { s with pc := p, pendingBranch := b, nullified := n } =
      { abs s with PC := p, BranchDelay := b, Nullify := n } := rfl

/-! ## The shape of a branch's refinement proof -/

set_option hygiene false in
/-- The common part of the refinement proof of an I-format branch `i` (encoded as `word`, Operation
`op`, the model's arm outside a delay slot `hex`): the delay-slot case (Reserved Instruction on both
sides), then `fin` on the run of the Operation against `hex`. Expects `s hg hn w hw` in scope. -/
macro "branch_refine " i:term:max word:term:max op:term:max hex:term:max " => " fin:tacticSeq : tactic =>
  `(tactic| (
    obtain ⟨hsz, -, h0⟩ := hg
    have hw' : w = $word := (Option.some.inj hw).symm
    have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_iFormat]
    have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_iFormat]
    have hbl : isBranchLike $i = true := rfl
    cases hpb : s.pendingBranch with
    | some t =>
      rw [execute_cti_slot w _ s t rfl rfl hpb]
      unfold execInstr; rw [hbl, hpb]; rfl
    | none =>
      rw [execute_cti_run w _ s $op hpb hc1 hc0 rfl]
      have hex : execInstr s $i = $hex := by
        unfold execInstr; rw [hbl, hpb]; rfl
      rw [hex]
      ($fin)))

/-! ## Encoding spaces -/

/-- Bit-blast the opcode of a concrete format diagram. -/
macro "opcode_tac" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [opcode, fld, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega))

theorem opcode_mfc0 (rt rd sel : W32) :
    opcode (fld 6 26 0x10#32 ||| fld 5 21 0x00#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 3 0 sel) =
      0x10#32 := by opcode_tac

theorem opcode_di (rt : W32) :
    opcode (fld 6 26 0x10#32 ||| fld 5 21 0x0B#32 ||| fld 5 16 rt ||| fld 5 11 12#32 ||| fld 1 5 0#32) =
      0x10#32 := by opcode_tac

theorem opcode_ei (rt : W32) :
    opcode (fld 6 26 0x10#32 ||| fld 5 21 0x0B#32 ||| fld 5 16 rt ||| fld 5 11 12#32 ||| fld 1 5 1#32) =
      0x10#32 := by opcode_tac

theorem opcode_eret : opcode (fld 6 26 0x10#32 ||| fld 1 25 1#32 ||| fld 6 0 0x18#32) = 0x10#32 := by
  opcode_tac

theorem opcode_wait (code : W32) :
    opcode (fld 6 26 0x10#32 ||| fld 1 25 1#32 ||| fld 19 6 code ||| fld 6 0 0x20#32) = 0x10#32 := by
  opcode_tac

theorem opcode_rdpgpr (rd rt : W32) :
    opcode (fld 6 26 0x10#32 ||| fld 5 21 0x0A#32 ||| fld 5 16 rt ||| fld 5 11 rd) = 0x10#32 := by
  opcode_tac

theorem opcode_wrpgpr (rd rt : W32) :
    opcode (fld 6 26 0x10#32 ||| fld 5 21 0x0E#32 ||| fld 5 16 rt ||| fld 5 11 rd) = 0x10#32 := by
  opcode_tac

theorem opcode_rdhwr (rt rd : W32) :
    opcode (fld 6 26 0x1F#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 6 0 0x3B#32) = 0x1F#32 := by
  opcode_tac

theorem opcode_j (target : W32) : opcode (fld 6 26 0x02#32 ||| fld 26 0 target) = 0x02#32 := by
  opcode_tac

theorem opcode_jal (target : W32) : opcode (fld 6 26 0x03#32 ||| fld 26 0 target) = 0x03#32 := by
  opcode_tac

/-! ## Jumps -/

/-- The J-format target `PC_{31..28} || instr_index || 0^2` is the model's mask-and-or. -/
theorem jump_target (p t : W32) :
    (bits p 31 28 ++ bits t 25 0 ++ 0#2 : BitVec 32) =
      (p &&& 0xf0000000#32) ||| ((t &&& 0x3FFFFFF#32) <<< 2) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bits, BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb']
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-! ## Coprocessor 0 instructions -/

theorem gep_cpu0 (s : State) :
    GeneralExceptionProcessing modelImpl modelOracle (.CoprocessorUnusable 0) (abs s) = abs (takeCop0Unusable s) := by
  rw [gep_eq s (.CoprocessorUnusable 0) (by intro h; cases h) (by intro u h; cases h; omega)]; rfl

/-- `Execute` of an instruction of the COP0 encoding space, outside a delay slot or not a CTI: the
Coprocessor Unusable check (MD00090 Vol III Rev 6.02 §6.2.22, p.100), then the Operation. -/
theorem execute_cop0 (w : W32) (i : Instruction) (s : State) (op : Pseudo Unit)
    (hslot : IsCTI i = false ∨ s.pendingBranch = none) (h1 : InCop1Space w = false)
    (h0 : InCop0Space w = true) (hop : Operation i = some op) :
    Execute modelCtx w i (abs s) =
      if cp0Usable s then
        match op.run modelCtx { arch := abs s } with
        | (.ok (), f) => some (Complete (abs s) f)
        | (.signal e, f) => some (GeneralExceptionProcessing modelCtx.impl modelCtx.oracle e f.arch)
      else some (abs (takeCop0Unusable s)) := by
  have hb : (IsCTI i && (abs s).BranchDelay.isSome) = false := by
    rcases hslot with h | h <;> simp [h, abs]
  simp only [Execute, hb, Bool.false_eq_true, ite_false, Execute.runOperation, h1, h0,
    Bool.false_and, Bool.true_and, cp0usable_abs, hop]
  cases cp0Usable s
  · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_cpu0]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rfl

/-- The model's `execInstr` of a coprocessor-0 instruction outside a delay slot or not a CTI. -/
theorem execInstr_cop0 (s : State) (i : Instruction)
    (hslot : isBranchLike i = false ∨ s.pendingBranch = none) (h1 : usesCop1 i = false)
    (h0 : usesCop0 i = true) :
    execInstr s i = if cp0Usable s then execBody s i else takeCop0Unusable s := by
  have hb : (isBranchLike i && s.pendingBranch.isSome) = false := by
    rcases hslot with h | h <;> simp [h]
  unfold execInstr; rw [hb, h1, h0]; cases cp0Usable s <;> rfl

theorem writeReg_pendingBranch (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).pendingBranch = s.pendingBranch := by
  unfold writeReg; split <;> rfl

theorem writeReg_pc (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).pc = s.pc := by
  unfold writeReg; split <;> rfl

/-- **Completion of an Operation that wrote one GPR** of the state `t` (the instruction's other
effects on `s`) is the model's `mkNext` of `writeReg`. -/
theorem complete_writeReg' (s t : State) (hsz : t.regs.size = 32)
    (hpb : t.pendingBranch = s.pendingBranch) (hpc : t.pc = s.pc) (i : Fin 32) (v : W32) :
    some (Complete (abs s) { arch := writeGPR (abs t) i v }) = some (abs (mkNext s (writeReg t i v))) := by
  rw [complete_plain, mkNext, abs_advance _ _ (by rw [writeReg_pendingBranch, hpb]),
    abs_writeReg _ _ _ hsz, writeReg_pc, hpc]
  rfl

theorem complete_writeReg (s : State) (hsz : s.regs.size = 32) (i : Fin 32) (v : W32) :
    some (Complete (abs s) { arch := writeGPR (abs s) i v }) = some (abs (mkNext s (writeReg s i v))) :=
  complete_writeReg' s s hsz rfl rfl i v

/-! ## The coprocessor 0 registers as `MFC0` reads them (`CPRRead` against the model's arm) -/

theorem cprRead_hwrena (s : State) : CPRRead modelImpl 7 0 (abs s) = s.cp0HWREna := rfl
theorem cprRead_badvaddr (s : State) : CPRRead modelImpl 8 0 (abs s) = s.cp0BadVAddr := rfl
theorem cprRead_count (s : State) : CPRRead modelImpl 9 0 (abs s) = s.cp0Count := rfl
theorem cprRead_compare (s : State) : CPRRead modelImpl 11 0 (abs s) = s.cp0Compare := rfl
theorem cprRead_status (s : State) : CPRRead modelImpl 12 0 (abs s) = s.cp0Status := rfl
theorem cprRead_intctl (s : State) : CPRRead modelImpl 12 1 (abs s) = intCtlValue := rfl
theorem cprRead_srsctl (s : State) : CPRRead modelImpl 12 2 (abs s) = srsCtlValue := rfl
theorem cprRead_epc (s : State) : CPRRead modelImpl 14 0 (abs s) = s.cp0Epc := rfl
theorem cprRead_prid (s : State) : CPRRead modelImpl 15 0 (abs s) = prIdValue := rfl
theorem cprRead_config1 (s : State) : CPRRead modelImpl 16 1 (abs s) = config1Value := rfl
theorem cprRead_config2 (s : State) : CPRRead modelImpl 16 2 (abs s) = config2Value := rfl
theorem cprRead_config3 (s : State) : CPRRead modelImpl 16 3 (abs s) = config3Value := rfl
theorem cprRead_errorepc (s : State) : CPRRead modelImpl 30 0 (abs s) = s.cp0ErrorEpc := rfl

/-- `Cause` (13, 0): the stored bits, `HW5..HW0` in `IP7..IP2`, and the timer request in `TI` and
`IP[IntCtl.IPTI]` = `IP7` (`modelImpl.IntCtl` has `IPTI = 7`). -/
theorem cprRead_cause (s : State) : CPRRead modelImpl 13 0 (abs s) = causeValue s := by
  have hipti : IntCtlIPTI modelImpl = 7 := by decide
  show CauseRead modelImpl (abs s) = causeValue s
  simp only [CauseRead, causeValue, hipti, hwIntBits, abs]
  cases s.cp0TimerInt <;> rfl

/-- `EBase` (15, 1): bit 31 reads 1, the Exception Base (29..12) as stored. -/
theorem cprRead_ebase (s : State) : CPRRead modelImpl 15 1 (abs s) = ebaseValue s := by
  show EBaseRead (abs s) = ebaseValue s
  rw [EBaseRead, ebaseValue, fieldOnes_29_12, BitVec.or_comm]; rfl

/-- `Config` (16, 0): the fixed fields with `K23`, `KU`, `K0`. -/
theorem cprRead_config (s : State) : CPRRead modelImpl 16 0 (abs s) = configValue s := rfl

end Refine
