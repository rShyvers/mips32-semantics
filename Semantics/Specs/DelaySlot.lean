import Semantics.Specs.Lemmas

/-!
# DelaySlot — what a delay slot changes

`delay_slot_commits_target` lifts every `hpb : s.pendingBranch = none` theorem to the delay-slot case;
`branch_in_delay_slot_reserved_instruction` covers a control transfer in a delay slot. `DelaySlotRel`,
`DelaySlotRel_ite` and `execInstr_delaySlotRel` are proof devices for the general theorem.

## Theorems in this file (7)

  `advance_not_in_delay_slot` `advance_in_delay_slot` `DelaySlotRel_ite` `execInstr_delaySlotRel`
  `execInstr_delay_slot` `delay_slot_commits_target` `branch_in_delay_slot_reserved_instruction`
-/

set_option maxRecDepth 4000

/-! ## What `advance` does -/

/-- Outside a delay slot, completing an instruction advances `pc` by 4. -/
theorem advance_not_in_delay_slot (orig result : State) (h : orig.pendingBranch = none) :
    advance orig result = { result with pc := result.pc + 4#32 } := by
  unfold advance; rw [h]

/-- **In a delay slot, completing an instruction commits the pending
target**: `pc` becomes `t` and the machine is no longer in a delay slot.
`result` — the instruction's effect on registers, memory and everything
else — is used exactly as computed. -/
theorem advance_in_delay_slot (orig result : State) (t : W32) (h : orig.pendingBranch = some t) :
    advance orig result = { result with pc := t, pendingBranch := none } := by
  unfold advance; rw [h]

/-! ## The general delay-slot theorem

For a non-control-transfer instruction, being in a delay slot changes
nothing about what the instruction *does*; it only changes where `pc` goes
afterwards. Formally: run the instruction once **not** in a delay slot
(`pendingBranch := none`) and once **in** one with pending target `t`
(`pendingBranch := some t`), from otherwise the same state. If the first
run completes normally — it yields a state `s'` with `s'.pc = s.pc + 4` —
then the second run yields exactly `{ s' with pc := t }`: the same
registers, memory, `hi`/`lo`, FP state, CP0 state and `LLbit`, with
`pc` on the branch target and no branch pending.

"Completes normally" is expressed as `s'.pc = s.pc + 4`. Exception entry
puts `pc` on the exception vector instead, so the side condition
`s.pc + 4 ≠ exceptionVector s` (the delay slot is not the word just below
the vector) makes that test exact. The exception case is covered by
`exceptionEntry_exl0_in_delay_slot`; a control-transfer instruction in a
delay slot by `branch_in_delay_slot_reserved_instruction`.

`DelaySlotRel`, `DelaySlotRel_ite` and `execInstr_delaySlotRel` are proof devices; the
statements to read are `execInstr_delay_slot` and `delay_slot_commits_target`. -/

/-- `DelaySlotRel pcNext t r0 r1`: if `r0` is normal completion at
`pcNext`, then `r1` is the same state with `pc := t`. (Proof device for
`execInstr_delay_slot`.) -/
def DelaySlotRel (pcNext t : W32) (r0 r1 : State) : Prop :=
  r0.pc = pcNext → r1 = { r0 with pc := t }

theorem DelaySlotRel_ite (c : Prop) [Decidable c] (pcNext t : W32) (a b a' b' : State)
    (h1 : c → DelaySlotRel pcNext t a a') (h2 : ¬ c → DelaySlotRel pcNext t b b') :
    DelaySlotRel pcNext t (if c then a else b) (if c then a' else b') := by
  by_cases h : c
  · rw [ite_of_pos h, ite_of_pos h]; exact h1 h
  · rw [ite_of_neg h, ite_of_neg h]; exact h2 h

set_option maxHeartbeats 0 in
/-- The delay-slot relation holds for every non-control-transfer
instruction. Proved structurally: after unfolding, both runs have the same
shape and are compared leaf by leaf. -/
theorem execInstr_delaySlotRel (s : State) (t : W32) (instr : Instruction)
    (hnb : isBranchLike instr = false) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } instr)
      (execInstr { s with pendingBranch := some t } instr) := by
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  cases instr <;> first | exact Bool.noConfusion (hnb : true = false) | skip
  all_goals (
    unfold execInstr execBody
    dsimp only [isBranchLike]
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, mkNext, advance,
      takeException, takeAddressException, readReg, readFpReg, readMemWord, readMemHalf, readMemByte,
      writeMemWord, writeMemHalf, writeMemByte, writeFpReg, readFpD, writeFpD, fpFinishS, fpFinishD,
      fpFinishCmp, takeCoprocessorUnusable, readFcc,
      Option.getD_some, writeReg_proj_pc, writeReg_proj_hi, writeReg_proj_lo,
      writeReg_proj_fpRegs, writeReg_proj_fcsr, writeReg_proj_mem,
      writeReg_proj_pendingBranch, writeReg_proj_llBit, writeReg_proj_cp0Status,
      writeReg_proj_cp0Cause, writeReg_proj_cp0Epc, writeReg_proj_cp0BadVAddr,
      writeReg_proj_cp0ErrorEpc, writeReg_proj_llAddr, writeReg_proj_cp0EBase, writeReg_proj_regs]
    repeat' (first
      | (show (_ : State).pc = _ → _ = _
         intro hnorm
         first
          | exact absurd hnorm.symm hvec
          | rfl)
      | refine DelaySlotRel_ite _ _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      | split
      | (rename_i h; obtain ⟨_, rfl⟩ : _ ∧ _ = _ := by simpa using h)
      | (rename_i h; obtain rfl : _ = _ := by simpa using h)
      | (simp_all <;> (repeat (obtain ⟨_, rfl⟩ := ‹_ ∧ _›)) <;> try subst_vars)))

/-- **The general delay-slot theorem** (at the level of `execInstr`): see
the section comment above. -/
theorem execInstr_delay_slot (s : State) (t : W32) (instr : Instruction) (s' : State)
    (hnb : isBranchLike instr = false) (hvec : s.pc + 4#32 ≠ exceptionVector s)
    (h0 : execInstr { s with pendingBranch := none } instr = s')
    (hnormal : s'.pc = s.pc + 4#32) :
    execInstr { s with pendingBranch := some t } instr = { s' with pc := t } := by
  have h := execInstr_delaySlotRel s t instr hnb hvec
  rw [h0] at h
  exact h hnormal

/-- **The general delay-slot theorem, for `step`.** If the instruction at
`pc` is not a control transfer and, executed outside a delay slot, it
completes normally with result `s'`, then executed in a delay slot with
pending branch target `t` it produces `{ s' with pc := t }`: **the
resulting `pc` is `t`, and every other effect is identical.** This lifts
every `hpb : s.pendingBranch = none` theorem in this file to the
delay-slot case. -/
theorem delay_slot_commits_target (s : State) (t w : W32) (instr : Instruction)
    (s' : State)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (hnb : isBranchLike instr = false) (hvec : s.pc + 4#32 ≠ exceptionVector s)
    (h0 : step { s with pendingBranch := none } = s')
    (hnormal : s'.pc = s.pc + 4#32) :
    step { s with pendingBranch := some t } = { s' with pc := t } := by
  unfold step at h0 ⊢
  rw [show readMemWord ({ s with pendingBranch := none } : State) ({ s with pendingBranch := none } : State).pc = some w from hfetch] at h0
  rw [show readMemWord ({ s with pendingBranch := some t } : State) ({ s with pendingBranch := some t } : State).pc = some w from hfetch]
  dsimp only at h0 ⊢
  rw [hdecode] at h0 ⊢
  exact execInstr_delay_slot s t instr s' hnb hvec h0 hnormal

/-- **A control transfer in a branch delay slot raises Reserved Instruction** (pin). The
architecture makes a branch, jump, `eret` or `wait` in a delay slot UNPREDICTABLE (pre-Release-6
branches/jumps: MD00086 Vol II-A Rev 6.06, BEQ, p.72) or UNDEFINED (ERET, p.177; WAIT, p.442),
and "UNPREDICTABLE operations may cause arbitrary exceptions" (§1.2.1, p.3); Release 6 requires
exactly this exception (MD00082 Vol I-A Rev 6.01 §5.3.2.1, p.62). Whenever the instruction about
to execute is in a delay slot (`s.pendingBranch = some _` — set by *every* branch/jump, taken or
not) and is one of the 26 instructions of `isBranchLike` (`isBranchLikeSpec` is that same
definition), `step` takes the Reserved Instruction exception from the delay slot (so `EPC` is the
branch and `Cause.BD = 1`, `exceptionEntry_exl0_in_delay_slot`). -/
theorem branch_in_delay_slot_reserved_instruction (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (hpb : s.pendingBranch.isSome = true) (hbr : isBranchLikeSpec instr = true) :
    step s = takeException s excCodeRI := by
  have hbr' : isBranchLike instr = true := hbr
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  unfold execInstr
  simp only [hpb, hbr', Bool.and_self, ↓reduceIte]
