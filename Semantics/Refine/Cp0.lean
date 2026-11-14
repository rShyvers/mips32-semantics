import Semantics.Refine.Bridge

/-!
# Refine.Cp0 — coprocessor 0 instructions against `execInstr`

Sub-wave 7A proves the pilot `mtc0`: the Coprocessor Unusable check of the COP0 encoding space
(MD00090 Vol III Rev 6.02 §6.2.22, p.100), each implemented register's write (`Manual.CPRWrite`
against the model's arm) and the UNDEFINED case (`Oracle.cp0Undefined`, the model's Reserved
Instruction).
-/

namespace Refine

open Manual

theorem mtc0_word (rt rd sel : W32) :
    InCop0Space (fld 6 26 0x10#32 ||| fld 5 21 0x04#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 3 0 sel) =
      true ∧
    InCop1Space (fld 6 26 0x10#32 ||| fld 5 21 0x04#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 3 0 sel) =
      false := by
  have hop : opcode (fld 6 26 0x10#32 ||| fld 5 21 0x04#32 ||| fld 5 16 rt ||| fld 5 11 rd |||
      fld 3 0 sel) = 0x10#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [opcode, fld, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_shiftLeft]
    rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega
  simp [InCop0Space, InCop1Space, hop]

theorem config_fields (v : W32) :
    v.extractLsb' 0 3 = v.setWidth 3 ∧ v.extractLsb' 28 3 = (v >>> 28).setWidth 3 ∧
      v.extractLsb' 25 3 = (v >>> 25).setWidth 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp [BitVec.getLsbD_ushiftRight, hi] <;> omega

theorem ebase_write (v : W32) :
    (1#32 <<< 31) ||| (v &&& fieldOnes 29 12) = (v &&& ebaseWriteMask) ||| ebaseFixedBits := by
  rw [fieldOnes_29_12, BitVec.or_comm]; rfl

/-- **MTC0 refines.** -/
theorem mtc0_refines (s : State) (hg : Good s) (rt rd sel w : W32)
    (hw : enc (.mtc0 rt rd sel) = some w) :
    Execute modelCtx w (.mtc0 rt rd sel) (abs s) = some (abs (execInstr s (.mtc0 rt rd sel))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = fld 6 26 0x10#32 ||| fld 5 21 0x04#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 3 0 sel := by
    have : enc (.mtc0 rt rd sel) =
      some (fld 6 26 0x10#32 ||| fld 5 21 0x04#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 3 0 sel) := rfl
    rw [this] at hw; exact (Option.some.inj hw).symm
  obtain ⟨hc0, hc1⟩ := mtc0_word rt rd sel
  rw [← hw'] at hc0 hc1
  have hex : execInstr s (.mtc0 rt rd sel) =
      (if (!cp0Usable s) = true then takeCop0Unusable s else execBody s (.mtc0 rt rd sel)) := by
    have h1 : isBranchLike (.mtc0 rt rd sel) = false := rfl
    have h2 : usesCop1 (.mtc0 rt rd sel) = false := rfl
    have h3 : usesCop0 (.mtc0 rt rd sel) = true := rfl
    unfold execInstr; rw [h1, h2, h3]; rfl
  rw [hex]
  have hcti : IsCTI (.mtc0 rt rd sel) = false := rfl
  simp only [Execute, Execute.runOperation, hcti, hc1, hc0, Bool.false_and, Bool.false_eq_true, ite_false,
    Bool.true_and, cp0usable_abs]
  cases hu : cp0Usable s
  · simp only [Bool.not_false, ↓reduceIte]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl,
      gep_eq s (.CoprocessorUnusable 0) (by intro h; cases h) (by intro u h; cases h; omega)]
    rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hop : Operation (.mtc0 rt rd sel) = some (Ops.MTC0 rt rd sel) := rfl
    rw [hop]
    have hb : execBody s (.mtc0 rt rd sel) =
      (match rd.toNat, sel.toNat with
      | 7, 0 => mkNext s { s with cp0HWREna := readReg s (regIdx rt) &&& hwrenaWriteMask }
      | 8, 0 => mkNext s s
      | 9, 0 => mkNext s { s with cp0Count := readReg s (regIdx rt) }
      | 11, 0 => mkNext s { s with cp0Compare := readReg s (regIdx rt), cp0TimerInt := false }
      | 12, 0 => mkNext s { s with cp0Status := readReg s (regIdx rt) &&& statusWriteMask }
      | 12, 1 => mkNext s s
      | 12, 2 => mkNext s s
      | 13, 0 => mkNext s { s with cp0Cause :=
                (s.cp0Cause &&& ~~~causeWriteMask) ||| (readReg s (regIdx rt) &&& causeWriteMask) }
      | 14, 0 => mkNext s { s with cp0Epc := readReg s (regIdx rt) }
      | 15, 0 => mkNext s s
      | 15, 1 => mkNext s { s with cp0EBase :=
                (readReg s (regIdx rt) &&& ebaseWriteMask) ||| ebaseFixedBits }
      | 16, 0 => mkNext s { s with cp0ConfigK0 := (readReg s (regIdx rt)).setWidth 3,
                                   cp0ConfigK23 := (readReg s (regIdx rt) >>> 28).setWidth 3,
                                   cp0ConfigKU := (readReg s (regIdx rt) >>> 25).setWidth 3 }
      | 16, 1 => mkNext s s
      | 30, 0 => mkNext s { s with cp0ErrorEpc := readReg s (regIdx rt) }
      | _, _ => takeException s excCodeRI) := rfl
    rw [hb]; clear hb hex hw hw' hc0 hc1 hop hcti
    simp only [Pseudo.run, Ops.MTC0, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg]
    obtain ⟨hk0, hk23, hku⟩ := config_fields (readReg s (regIdx rt))
    generalize readReg s (regIdx rt) = v at *
    generalize rd.toNat = r
    generalize sel.toNat = q
    by_cases hI : IsCoprocessorRegisterImplemented r q = true
    · have hEB : ∀ a d, modelCtx.oracle.ebaseWriteBEV0 a d = .proceed := fun _ _ => rfl
      simp only [hI, ↓reduceIte, Pseudo.get, Pseudo.oracle, hEB, unpredictableOr, ite_self,
        Pseudo.modify, complete_plain]
      split <;> simp only [IsCoprocessorRegisterImplemented] at hI <;>
        first
          | (simp only [CPRWrite, mkNext, statusWritable_eq, causeWritable_eq, hwrenaWritable_eq,
              ebase_write, hk0, hk23, hku]
             rw [abs_advance _ _ (by rfl)]; rfl)
          | (exfalso; simp at hI)
          | (exfalso; revert hI; split <;> simp_all)
    · have hund : ∀ a i, modelCtx.oracle.cp0Undefined a i = .signal .ReservedInstruction :=
        fun _ _ => rfl
      simp only [hI, Bool.false_eq_true, ↓reduceIte, Pseudo.oracle, Pseudo.get, resolve, hund]
      split
      all_goals first
        | (exfalso; apply hI; rfl)
        | (show some (GeneralExceptionProcessing modelImpl modelOracle .ReservedInstruction (abs s)) = _
           rw [gep_take s .ReservedInstruction rfl excCodeRI (by decide)])

end Refine
