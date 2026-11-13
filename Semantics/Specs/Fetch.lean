import Semantics.Specs.Lemmas

/-!
# Fetch — fetch and decode failures

What `step` does when there is no instruction to run: misaligned `pc`, no word at `pc`,
a word `decode` rejects (Reserved Instruction, or Coprocessor Unusable for COP1 words), and the
simulator-level halt at the unhandled exception vector.

## Theorems in this file (6)

  `step_misaligned_pc` `step_undecodable` `step_reserved_instruction` `step_reserved_cop1_unusable`
  `step_unhandled_exception` `step_no_instruction`
-/

set_option maxRecDepth 4000

/-! ## Fetch and decode failures -/

/-- **A misaligned `pc` raises Address Error (AdEL)** with `BadVAddr = pc`
(and `EPC = pc`, by `exceptionEntry_*`). -/
theorem step_misaligned_pc (p : Program) (s : State) (h : s.pc.toNat % 4 ≠ 0) :
    step p s = takeAddressException s excCodeAdEL s.pc := by
  unfold step
  rw [show fetchWord p s.pc = none by unfold fetchWord; rw [ite_of_pos h]]
  dsimp only
  rw [ite_of_pos h]

/-- **A word that does not decode** raises Reserved Instruction (ExcCode
10) — unless it lies in a coprocessor's encoding space and that coprocessor
is unusable, in which case Coprocessor Unusable takes precedence (MD00090
Vol III Rev 6.02 §6.2.21, p.99): coprocessor 1 (`isCop1Word`) when
`Status.CU1 = 0`, with `Cause.CE = 1`; coprocessor 2 (`isCop2Word`), which
the model does not have, always, with `Cause.CE = 2`. -/
theorem step_undecodable (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = none) :
    step p s =
      if isCop1Word w && !cu1Enabled s then StepResult.next (exceptionEntry s excCodeCpU 1#32)
      else if isCop2Word w then StepResult.next (exceptionEntry s excCodeCpU 2#32)
      else takeException s excCodeRI := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  rfl

/-- **A word that does not decode and is in no coprocessor's encoding space
raises Reserved Instruction** (ExcCode 10). -/
theorem step_reserved_instruction (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = none)
    (hc1 : isCop1Word w = false) (hc2 : isCop2Word w = false) :
    step p s = takeException s excCodeRI := by
  rw [step_undecodable p s w hfetch hdecode, hc1, hc2]
  rfl

/-- **A reserved coprocessor-1 encoding with `Status.CU1 = 0` raises
Coprocessor Unusable**, not Reserved Instruction. -/
theorem step_reserved_cop1_unusable (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = none)
    (hc1 : isCop1Word w = true) (hcu : cu1Enabled s = false) :
    step p s = takeCoprocessorUnusable s := by
  rw [step_undecodable p s w hfetch hdecode, hc1, hcu]
  rfl

/-- **No handler installed** (model-level convention): if an exception has
been taken (`Status.EXL = 1`) and `pc` is the exception vector but the
program holds no instruction there, `step` halts with
`unhandledException`, reporting `Cause.ExcCode`, `EPC` and `BadVAddr`. -/
theorem step_unhandled_exception (p : Program) (s : State)
    (hfetch : fetchWord p s.pc = none) (haligned : s.pc.toNat % 4 = 0)
    (hvec : atUnhandledVector s = true) :
    step p s = StepResult.halt (.unhandledException (causeExcCode s) s.cp0Epc s.cp0BadVAddr) := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [ite_of_neg (by omega), ite_of_pos hvec]

/-- **Running off the program** (model boundary): an aligned `pc` holding
no instruction, when not at the exception vector with `EXL = 1`, halts with
`noInstruction pc`. -/
theorem step_no_instruction (p : Program) (s : State)
    (hfetch : fetchWord p s.pc = none) (haligned : s.pc.toNat % 4 = 0)
    (hvec : atUnhandledVector s = false) :
    step p s = StepResult.halt (.noInstruction s.pc) := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [ite_of_neg (by omega), ite_of_neg (by simp [hvec])]
