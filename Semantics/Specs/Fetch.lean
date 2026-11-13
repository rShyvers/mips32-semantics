import Semantics.Specs.Lemmas

/-!
# Fetch — instruction fetch from memory, and fetch / decode failures

`step` fetches the big-endian word at `pc` from `State.mem` (`readMemWord s s.pc`). What happens
when that word is not an instruction: misaligned `pc` (Address Error), a word `decode` rejects
(Reserved Instruction, or Coprocessor Unusable for an unusable coprocessor's encoding space). There
is no "no instruction" case in the processor: memory that was never written reads as 0
(`sll $0, $0, 0`). The hosted run's stopping conventions are in `Hosted.lean`.

Self-modifying code (a store to the next instruction changes what executes next) is in
`SelfModifying.lean`.

## Theorems in this file (5)

  `step_misaligned_pc` `step_fetches_from_memory` `step_undecodable` `step_reserved_instruction`
  `step_reserved_cop1_unusable`
-/

set_option maxRecDepth 4000

/-! ## Fetch and decode failures -/

/-- **A misaligned `pc` raises Address Error (AdEL)** with `BadVAddr = pc`
(and `EPC = pc`, by `exceptionEntry_*`). The fetch is a word read, which fails exactly for a
misaligned address. -/
theorem step_misaligned_pc (s : State) (h : s.pc.toNat % 4 ≠ 0) :
    step s = takeAddressException s excCodeAdEL s.pc := by
  unfold step
  rw [readMemWord_misaligned s s.pc h]

/-- **`step` executes the word in memory at `pc`**: if the big-endian word at `pc` decodes to
`instr`, the step is `execInstr s instr`, whatever else memory holds. -/
theorem step_fetches_from_memory (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr) :
    step s = execInstr s instr := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]

/-- **A word that does not decode** raises Reserved Instruction (ExcCode
10) — unless it lies in a coprocessor's encoding space and that coprocessor
is unusable, in which case Coprocessor Unusable takes precedence (MD00090
Vol III Rev 6.02 §6.2.21, p.99): coprocessor 1 (`isCop1Word`) when
`Status.CU1 = 0`, with `Cause.CE = 1`; coprocessor 2 (`isCop2Word`), which
the model does not have, always, with `Cause.CE = 2`. -/
theorem step_undecodable (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = none) :
    step s =
      if isCop1Word w && !cu1Enabled s then (exceptionEntry s excCodeCpU 1#32)
      else if isCop2Word w then (exceptionEntry s excCodeCpU 2#32)
      else takeException s excCodeRI := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  rfl

/-- **A word that does not decode and is in no coprocessor's encoding space
raises Reserved Instruction** (ExcCode 10). -/
theorem step_reserved_instruction (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = none)
    (hc1 : isCop1Word w = false) (hc2 : isCop2Word w = false) :
    step s = takeException s excCodeRI := by
  rw [step_undecodable s w hfetch hdecode, hc1, hc2]
  rfl

/-- **A reserved coprocessor-1 encoding with `Status.CU1 = 0` raises
Coprocessor Unusable**, not Reserved Instruction. -/
theorem step_reserved_cop1_unusable (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = none)
    (hc1 : isCop1Word w = true) (hcu : cu1Enabled s = false) :
    step s = takeCoprocessorUnusable s := by
  rw [step_undecodable s w hfetch hdecode, hc1, hcu]
  rfl
