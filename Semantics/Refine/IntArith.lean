import Semantics.Refine.Bridge

/-!
# Refine.IntArith — the integer arithmetic Operations against `execInstr`

`Refine.<ctor>_refines`: executing the instruction in the spec (`Manual.Execute`, from the fetched
word `w` whose format diagram is the instruction's) is the model's `execInstr`, seen through `abs`.
Sub-wave 7A proves the pilot `add`.
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
    show some (GeneralExceptionProcessing modelOracle .IntegerOverflow (abs s)) = _
    rw [gep_take s .IntegerOverflow rfl excCodeOv (by decide)]

end Refine
