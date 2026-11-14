import Semantics.Refine.Bridge

/-!
# Refine.FpuArith — FP arithmetic Operations against `execInstr`

Sub-wave 7A proves the pilot `add.s`: the manual's FCSR bookkeeping (`Manual.FPResult`: Cause,
`CheckFPException`, Flags; MD00082 Vol I-A Rev 6.01 §6.7.1) against the model's `fpFinishS` /
`Mips.Fp.fpUpdate`, and the Coprocessor Unusable check of the COP1 space.
-/

namespace Refine

open Manual

theorem fcsr1_fields (F : W32) (b : BitVec 5) :
    bit ((F &&& ~~~(0x3F#32 <<< 12)) ||| (b.setWidth 32 <<< 12)) 17 = false ∧
    ((F &&& ~~~(0x3F#32 <<< 12)) ||| (b.setWidth 32 <<< 12)).extractLsb' 12 5 = b ∧
    ((F &&& ~~~(0x3F#32 <<< 12)) ||| (b.setWidth 32 <<< 12)).extractLsb' 7 5 = F.extractLsb' 7 5 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [bit]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    rcases i with _|_|_|_|_|i <;> simp <;> omega
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    rcases i with _|_|_|_|_|i <;> simp <;> omega

/-- **`FPResult` in closed form**: Cause written, then the trap check on the new FCSR, then Flags. -/
theorem FPResult_run {α : Type} (r : α × Mips.Fp.Flags) (c : Ctx) (f : Frame) :
    FPResult r c f =
      if (r.2.toBits &&& f.arch.FCSR.extractLsb' 7 5) != 0#5 then
        (.signal .FloatingPoint, { f with arch := { f.arch with FCSR :=
          (f.arch.FCSR &&& ~~~(0x3F#32 <<< 12)) ||| (r.2.toBits.setWidth 32 <<< 12) } })
      else
        (.ok r.1, { f with arch := { f.arch with FCSR :=
          ((f.arch.FCSR &&& ~~~(0x3F#32 <<< 12)) ||| (r.2.toBits.setWidth 32 <<< 12)) |||
            (r.2.toBits.setWidth 32 <<< 2) } }) := by
  obtain ⟨h17, hcause, hen⟩ := fcsr1_fields f.arch.FCSR r.2.toBits
  simp only [FPResult, bind, Pseudo.modify, CheckFPException, Pseudo.get, h17, hcause, hen,
    Bool.false_or]
  cases (r.2.toBits &&& f.arch.FCSR.extractLsb' 7 5 != 0#5) <;> rfl

theorem addS_word (fd fs ft : W32) :
    InCop1Space (rFormat 0x11#32 0x10#32 ft fs fd 0#32) = true ∧
    InCop0Space (rFormat 0x11#32 0x10#32 ft fs fd 0#32) = false := by
  simp [InCop1Space, InCop0Space, opcode_rFormat]

/-- **ADD.S refines.** -/
theorem addS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.addS fd fs ft) = some w) :
    Execute modelCtx w (.addS fd fs ft) (abs s) = some (abs (execInstr s (.addS fd fs ft))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  have hw' : w = rFormat 0x11#32 0x10#32 ft fs fd 0#32 := by
    have : enc (.addS fd fs ft) = some (rFormat 0x11#32 0x10#32 ft fs fd 0#32) := rfl
    rw [this] at hw; exact (Option.some.inj hw).symm
  obtain ⟨hc1, hc0⟩ := addS_word fd fs ft
  rw [← hw'] at hc1 hc0
  have hex : execInstr s (.addS fd fs ft) =
      (if (!cu1Enabled s) = true then takeCoprocessorUnusable s
       else fpFinishS s fd (Mips.Fp.f32Add (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
    have h1 : isBranchLike (.addS fd fs ft) = false := rfl
    have h2 : usesCop1 (.addS fd fs ft) = true := rfl
    have h3 : usesCop0 (.addS fd fs ft) = false := rfl
    unfold execInstr; rw [h1, h2, h3]; simp only [Bool.true_and, Bool.false_and, Bool.false_eq_true,
      ite_false]; rfl
  rw [hex]
  have hcti : IsCTI (.addS fd fs ft) = false := rfl
  simp only [Execute, Execute.runOperation, hcti, hc1, hc0, Bool.false_and, Bool.false_eq_true, ite_false,
    Bool.true_and, cu1_abs]
  cases hu : cu1Enabled s
  · simp only [Bool.not_false, ↓reduceIte]
    rw [show modelCtx.oracle = modelOracle from rfl,
      gep_eq s (.CoprocessorUnusable 1) (by intro h; cases h) (by intro u h; cases h; omega)]
    rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hop : Operation (.addS fd fs ft) = some (Ops.ADD_S fd fs ft) := rfl
    rw [hop]
    have henv : IEEE.env (abs s) = fpEnv s := rfl
    simp only [Pseudo.run, Ops.ADD_S, bind, ValueFPR32, Pseudo.get, IEEE.addS, FPResult_run]
    simp only [henv]
    unfold fpFinishS Mips.Fp.fpUpdate Mips.Fp.fpeEnabled
    simp only [abs_FCSR, abs_FPR, ← regIdx_eq_reg]
    cases hX : ((Mips.Fp.f32Add (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft))).2.toBits &&&
        s.fcsr.extractLsb' 7 5) != 0#5
    · simp only [Bool.false_eq_true, ↓reduceIte, StoreFPR32, Pseudo.modify]
      rw [complete_plain, mkNext, abs_advance _ _ (by rfl), abs_writeFpReg _ _ _ (by exact hfsz)]
      rfl
    · simp only [↓reduceIte]
      rw [show modelCtx.oracle = modelOracle from rfl]
      rw [← gep_take _ .FloatingPoint rfl excCodeFPE (by decide)]
      rfl
end Refine
