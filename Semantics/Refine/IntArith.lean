import Semantics.Refine.Bridge
-- 7C S1
import Semantics.Refine.BridgeIntAlu

/-!
# Refine.IntArith — the integer arithmetic Operations against `execInstr`

`Refine.<ctor>_refines`: executing the instruction in the spec (`Manual.Execute`, from the fetched
word `w` whose format diagram is the instruction's) is the model's `execInstr`, seen through `abs`.
Sub-wave 7A proves the pilot `add`; sub-wave 7C S1 the rest of the family, through the shared
steps of `Refine/BridgeIntAlu.lean`.
-/

namespace Refine

open Manual

/-- **ADD refines.** -/
theorem add_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.add rs rt rd) = some w) :
    Execute modelCtx w (.add rs rt rd) (abs s) = some (abs (execInstr s (.add rs rt rd))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = rFormat 0#32 rs rt rd 0#32 0x20#32 := by
    have : enc (.add rs rt rd) = some (rFormat 0#32 rs rt rd 0#32 0x20#32) := rfl
    rw [this] at hw; exact (Option.some.inj hw).symm
  have hc1 : InCop1Space w = false := by
    subst hw'; simp only [InCop1Space, opcode_rFormat, funct_rFormat]; decide
  have hc0 : InCop0Space w = false := by
    subst hw'; simp only [InCop0Space, opcode_rFormat]; decide
  have hex : execInstr s (.add rs rt rd) =
      (let av := readReg s (regIdx rs)
       let bv := readReg s (regIdx rt)
       if addOverflows (asSigned av) (asSigned bv) (asSigned (av + bv)) then takeException s excCodeOv
       else mkNext s (writeReg s (regIdx rd) (av + bv))) := by
    have h1 : isBranchLike (.add rs rt rd) = false := rfl
    have h2 : usesCop1 (.add rs rt rd) = false := rfl
    have h3 : usesCop0 (.add rs rt rd) = false := rfl
    unfold execInstr; rw [h1, h2, h3]; rfl
  rw [hex, execute_run modelCtx w _ _ (Ops.ADD rs rt rd) rfl hc1 hc0 rfl]
  simp only [Pseudo.run, Ops.ADD, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg]
  have hov := add_ovf (readReg s (regIdx rs)) (readReg s (regIdx rt))
  cases h : addOverflows (asSigned (readReg s (regIdx rs))) (asSigned (readReg s (regIdx rt)))
      (asSigned (readReg s (regIdx rs) + readReg s (regIdx rt))) <;> rw [h] at hov
  · simp only [of_decide_eq_false hov, ↓reduceIte, Bool.false_eq_true, add33_low]
    show some (Complete (abs s) { arch := writeGPR (abs s) (regIdx rd) _ }) = _
    rw [complete_plain, mkNext, abs_advance _ _ (by unfold writeReg; split <;> rfl),
      abs_writeReg _ _ _ hsz]
    have hpc : (writeReg s (regIdx rd) (readReg s (regIdx rs) + readReg s (regIdx rt))).pc = s.pc := by
      unfold writeReg; split <;> rfl
    rw [hpc]; rfl
  · have hP := of_decide_eq_true hov
    simp only [ne_eq] at hP ⊢
    simp only [hP, not_false_eq_true, ↓reduceIte]
    show some (GeneralExceptionProcessing modelImpl modelOracle .IntegerOverflow (abs s)) = _
    rw [gep_take s .IntegerOverflow rfl excCodeOv (by decide)]

-- 7C S1 integer ALU: begin

/-- **ADDU refines.** -/
theorem addu_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.addu rs rt rd) = some w) :
    Execute modelCtx w (.addu rs rt rd) (abs s) = some (abs (execInstr s (.addu rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x21#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.ADDU rs rt rd) rd
    (readReg s (regIdx rs) + readReg s (regIdx rt)) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.ADDU, readGPR_abs s hg.2.2]

/-- **SUB refines.** -/
theorem sub_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.sub rs rt rd) = some w) :
    Execute modelCtx w (.sub rs rt rd) (abs s) = some (abs (execInstr s (.sub rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x22#32 = w := Option.some.inj hw
  have hov := sub_ovf (readReg s (regIdx rs)) (readReg s (regIdx rt))
  cases h : subOverflows (asSigned (readReg s (regIdx rs))) (asSigned (readReg s (regIdx rt)))
      (asSigned (readReg s (regIdx rs) - readReg s (regIdx rt))) <;> rw [h] at hov
  · refine refine_gpr s hg _ _ (Ops.SUB rs rt rd) rd (readReg s (regIdx rs) - readReg s (regIdx rt))
      (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ ?_
    · alu_run [Ops.SUB, readGPR_abs s hg.2.2, hov, sub33_low]
    · rw [execInstr_body s _ rfl rfl rfl]; simp only [execBody, h]; rfl
  · refine refine_exc s _ _ (Ops.SUB rs rt rd) .IntegerOverflow excCodeOv (fun h => nomatch h)
      (by alu_space) (by alu_space) rfl ?_ rfl rfl ?_
    · alu_run [Ops.SUB, readGPR_abs s hg.2.2, hov]; rfl
    · rw [execInstr_body s _ rfl rfl rfl]; simp only [execBody, h]; rfl

/-- **SUBU refines.** -/
theorem subu_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.subu rs rt rd) = some w) :
    Execute modelCtx w (.subu rs rt rd) (abs s) = some (abs (execInstr s (.subu rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x23#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SUBU rs rt rd) rd
    (readReg s (regIdx rs) - readReg s (regIdx rt)) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.SUBU, readGPR_abs s hg.2.2]

/-- **AND refines.** -/
theorem and_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.and rs rt rd) = some w) :
    Execute modelCtx w (.and rs rt rd) (abs s) = some (abs (execInstr s (.and rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x24#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.AND rs rt rd) rd
    (readReg s (regIdx rs) &&& readReg s (regIdx rt)) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.AND, readGPR_abs s hg.2.2]

/-- **OR refines.** -/
theorem or_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.or rs rt rd) = some w) :
    Execute modelCtx w (.or rs rt rd) (abs s) = some (abs (execInstr s (.or rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x25#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.OR rs rt rd) rd
    (readReg s (regIdx rs) ||| readReg s (regIdx rt)) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.OR, readGPR_abs s hg.2.2]

/-- **XOR refines.** -/
theorem xor_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.xor rs rt rd) = some w) :
    Execute modelCtx w (.xor rs rt rd) (abs s) = some (abs (execInstr s (.xor rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x26#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.XOR rs rt rd) rd
    (readReg s (regIdx rs) ^^^ readReg s (regIdx rt)) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.XOR, readGPR_abs s hg.2.2]

/-- **NOR refines.** -/
theorem nor_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.nor rs rt rd) = some w) :
    Execute modelCtx w (.nor rs rt rd) (abs s) = some (abs (execInstr s (.nor rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x27#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.NOR rs rt rd) rd
    (~~~(readReg s (regIdx rs) ||| readReg s (regIdx rt))) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.NOR, readGPR_abs s hg.2.2]

/-- **SLT refines.** -/
theorem slt_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.slt rs rt rd) = some w) :
    Execute modelCtx w (.slt rs rt rd) (abs s) = some (abs (execInstr s (.slt rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x2A#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SLT rs rt rd) rd
    (if asSigned (readReg s (regIdx rs)) < asSigned (readReg s (regIdx rt)) then 1#32 else 0#32) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  by_cases hc : asSigned (readReg s (regIdx rs)) < asSigned (readReg s (regIdx rt)) <;>
    alu_run [Ops.SLT, readGPR_abs s hg.2.2, slt_w, one_w, hc, decide_true, decide_false] <;> rfl

/-- **SLTU refines.** -/
theorem sltu_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.sltu rs rt rd) = some w) :
    Execute modelCtx w (.sltu rs rt rd) (abs s) = some (abs (execInstr s (.sltu rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x2B#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SLTU rs rt rd) rd
    (if (readReg s (regIdx rs)).toNat < (readReg s (regIdx rt)).toNat then 1#32 else 0#32) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  by_cases hc : (readReg s (regIdx rs)).toNat < (readReg s (regIdx rt)).toNat <;>
    alu_run [Ops.SLTU, readGPR_abs s hg.2.2, ult_w, one_w, hc, decide_true, decide_false] <;> rfl

/-- **MOVN refines.** -/
theorem movn_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.movn rs rt rd) = some w) :
    Execute modelCtx w (.movn rs rt rd) (abs s) = some (abs (execInstr s (.movn rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x0B#32 = w := Option.some.inj hw
  cases h : readReg s (regIdx rt) != 0#32
  · refine refine_ok s s _ _ (Ops.MOVN rs rt rd) (fun h => nomatch h) (by alu_space) (by alu_space) rfl
      ?_ ?_ rfl rfl
    · alu_run [Ops.MOVN, readGPR_abs s hg.2.2, h]; rfl
    · rw [execInstr_body s _ rfl rfl rfl]; simp only [execBody, h]; rfl
  · refine refine_gpr s hg _ _ (Ops.MOVN rs rt rd) rd (readReg s (regIdx rs))
      (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ ?_
    · alu_run [Ops.MOVN, readGPR_abs s hg.2.2, h]
    · rw [execInstr_body s _ rfl rfl rfl]; simp only [execBody, h]; rfl

/-- **MOVZ refines.** -/
theorem movz_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.movz rs rt rd) = some w) :
    Execute modelCtx w (.movz rs rt rd) (abs s) = some (abs (execInstr s (.movz rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x0A#32 = w := Option.some.inj hw
  cases h : readReg s (regIdx rt) == 0#32
  · refine refine_ok s s _ _ (Ops.MOVZ rs rt rd) (fun h => nomatch h) (by alu_space) (by alu_space) rfl
      ?_ ?_ rfl rfl
    · alu_run [Ops.MOVZ, readGPR_abs s hg.2.2, h]; rfl
    · rw [execInstr_body s _ rfl rfl rfl]; simp only [execBody, h]; rfl
  · refine refine_gpr s hg _ _ (Ops.MOVZ rs rt rd) rd (readReg s (regIdx rs))
      (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ ?_
    · alu_run [Ops.MOVZ, readGPR_abs s hg.2.2, h]
    · rw [execInstr_body s _ rfl rfl rfl]; simp only [execBody, h]; rfl

-- 7C S1 integer ALU: end

end Refine
