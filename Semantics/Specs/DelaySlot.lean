import Semantics.Specs.Lemmas

/-!
# DelaySlot — what a delay slot changes

`delay_slot_commits_target` lifts every `hpb : s.pendingBranch = none` theorem to the delay-slot case;
`branch_in_delay_slot_reserved_instruction` covers a control transfer in a delay slot. `DelaySlotRel`,
`DelaySlotRel_ite` and `execInstr_delaySlotRel` are proof devices for the general theorem.

## Theorems in this file (34)

  `advance_not_in_delay_slot` `advance_in_delay_slot` `DelaySlotRel_ite` `execInstr_delaySlotRel`
  `execInstr_delay_slot` `delay_slot_commits_target` `branch_in_delay_slot_reserved_instruction`
  `readMemByte_pb` `readReg_pb` `writeReg_pb` `writeMemByte_pb` `writeMemByte_getD_pb`
  `takeAddressException_pc_pb` `writeMemWord_pb` `writeMemHalf_pb` `readFpReg_pb` `cu1Enabled_pb`
  `takeCoprocessorUnusable_pc_pb` `delaySlotRel_lwl` `delaySlotRel_lwr` `delaySlotRel_swl`
  `delaySlotRel_swr` `delaySlotRel_sw` `delaySlotRel_sh` `delaySlotRel_sb` `delaySlotRel_sc`
  `delaySlotRel_swc1` `delaySlotRel_swxc1` `delaySlotRel_sdc1` `delaySlotRel_sdxc1` `hwrValue_pb`
  `rdhwrAllowed_pb` `takeException_pc_pb` `delaySlotRel_rdhwr`
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

/-! ### Memory instructions in a delay slot

For the stores and `lwl`/`lwr`/`swl`/`swr`, whose step can raise the MMU's Address Error, the
relation is proved directly: every memory access of `{ s with pendingBranch := x }` is that of `s`
(the translation reads only `Status`), so both runs make the same access; the Address Error case
ends at the exception vector, which `hvec` excludes. (Proof devices for `execInstr_delaySlotRel`.) -/

theorem readMemByte_pb (s : State) (x : Option W32) (a : W32) :
    readMemByte { s with pendingBranch := x } a = readMemByte s a := rfl

theorem readReg_pb (s : State) (x : Option W32) (i : Fin 32) :
    readReg { s with pendingBranch := x } i = readReg s i := rfl

theorem writeReg_pb (s : State) (x : Option W32) (i : Fin 32) (v : W32) :
    writeReg { s with pendingBranch := x } i v = { writeReg s i v with pendingBranch := x } := by
  unfold writeReg; split <;> rfl

theorem writeMemByte_pb (s : State) (x : Option W32) (a : W32) (b : UInt8) :
    writeMemByte { s with pendingBranch := x } a b =
      (writeMemByte s a b).map (fun s' => { s' with pendingBranch := x }) := by
  have h : translate { s with pendingBranch := x } a = translate s a := rfl
  unfold writeMemByte; rw [h]; cases translate s a <;> rfl

theorem writeMemByte_getD_pb (s d : State) (x : Option W32) (a : W32) (b : UInt8) :
    (writeMemByte { s with pendingBranch := x } a b).getD { d with pendingBranch := x } =
      { (writeMemByte s a b).getD d with pendingBranch := x } := by
  rw [writeMemByte_pb]; cases writeMemByte s a b <;> rfl

theorem takeAddressException_pc_pb (s : State) (x : Option W32) (c a : W32) :
    (takeAddressException { s with pendingBranch := x } c a).pc = exceptionVector s := rfl

theorem writeMemWord_pb (s : State) (x : Option W32) (a v : W32) :
    writeMemWord { s with pendingBranch := x } a v =
      (writeMemWord s a v).map (fun s' => { s' with pendingBranch := x }) := by
  have h : translate { s with pendingBranch := x } a = translate s a := rfl
  unfold writeMemWord; rw [h]; split
  · rfl
  · cases translate s a <;> rfl

theorem writeMemHalf_pb (s : State) (x : Option W32) (a v : W32) :
    writeMemHalf { s with pendingBranch := x } a v =
      (writeMemHalf s a v).map (fun s' => { s' with pendingBranch := x }) := by
  have h : translate { s with pendingBranch := x } a = translate s a := rfl
  unfold writeMemHalf; rw [h]; split
  · rfl
  · cases translate s a <;> rfl

theorem readFpReg_pb (s : State) (x : Option W32) (i : Fin 32) :
    readFpReg { s with pendingBranch := x } i = readFpReg s i := rfl

theorem cu1Enabled_pb (s : State) (x : Option W32) :
    cu1Enabled { s with pendingBranch := x } = cu1Enabled s := rfl

theorem takeCoprocessorUnusable_pc_pb (s : State) (x : Option W32) :
    (takeCoprocessorUnusable { s with pendingBranch := x }).pc = exceptionVector s := rfl

theorem hwrValue_pb (s : State) (x : Option W32) (rd : W32) :
    hwrValue { s with pendingBranch := x } rd = hwrValue s rd := rfl

theorem rdhwrAllowed_pb (s : State) (x : Option W32) (rd : W32) :
    rdhwrAllowed { s with pendingBranch := x } rd = rdhwrAllowed s rd := rfl

theorem takeException_pc_pb (s : State) (x : Option W32) (c : W32) :
    (takeException { s with pendingBranch := x } c).pc = exceptionVector s := rfl

theorem delaySlotRel_rdhwr (s : State) (t : W32) (rt rd : W32)
    (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } (.rdhwr rt rd))
      (execInstr { s with pendingBranch := some t } (.rdhwr rt rd)) := by
  rw [execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl),
    execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)]
  simp only [execBody, hwrValue_pb, rdhwrAllowed_pb]
  split
  · refine DelaySlotRel_ite _ _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
    · intro _; simp only [mkNext, advance, writeReg_pb]
    · intro h; exact absurd (h.symm.trans (takeException_pc_pb _ _ _)) hvec
  · intro h; exact absurd (h.symm.trans (takeException_pc_pb _ _ _)) hvec

theorem delaySlotRel_lwl (s : State) (t : W32) (rs rt imm : W32) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } (.lwl rs rt imm))
      (execInstr { s with pendingBranch := some t } (.lwl rs rt imm)) := by
  rw [execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl),
    execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)]
  simp only [execBody, readMemByte_pb, readReg_pb]
  cases readMemByte s (readReg s (regIdx rs) + signExt16 imm) with
  | none => intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
  | some b0 => intro _; simp only [mkNext, advance, writeReg_pb]

theorem delaySlotRel_lwr (s : State) (t : W32) (rs rt imm : W32) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } (.lwr rs rt imm))
      (execInstr { s with pendingBranch := some t } (.lwr rs rt imm)) := by
  rw [execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl),
    execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)]
  simp only [execBody, readMemByte_pb, readReg_pb]
  cases readMemByte s (readReg s (regIdx rs) + signExt16 imm) with
  | none => intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
  | some b0 => intro _; simp only [mkNext, advance, writeReg_pb]

theorem delaySlotRel_swl (s : State) (t : W32) (rs rt imm : W32) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } (.swl rs rt imm))
      (execInstr { s with pendingBranch := some t } (.swl rs rt imm)) := by
  rw [execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl),
    execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)]
  simp only [execBody, readReg_pb, writeMemByte_pb]
  cases writeMemByte s (readReg s (regIdx rs) + signExt16 imm) (getByteSlot (readReg s (regIdx rt)) 0) with
  | none => intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
  | some s1 =>
    intro _
    simp only [Option.map_some, writeMemByte_getD_pb, mkNext, advance]
    split <;> rfl

theorem delaySlotRel_swr (s : State) (t : W32) (rs rt imm : W32) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } (.swr rs rt imm))
      (execInstr { s with pendingBranch := some t } (.swr rs rt imm)) := by
  rw [execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl),
    execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)]
  simp only [execBody, readReg_pb, writeMemByte_pb]
  cases writeMemByte s (readReg s (regIdx rs) + signExt16 imm) (getByteSlot (readReg s (regIdx rt)) 3) with
  | none => intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
  | some s1 =>
    intro _
    simp only [Option.map_some, writeMemByte_getD_pb, mkNext, advance]
    split <;> rfl

theorem delaySlotRel_sw (s : State) (t : W32) (a b c : W32) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } (.sw a b c))
      (execInstr { s with pendingBranch := some t } (.sw a b c)) := by
  rw [execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl),
    execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)]
  simp only [execBody, readReg_pb, writeMemWord_pb]
  cases writeMemWord s (readReg s (regIdx a) + signExt16 c) (readReg s (regIdx b)) with
  | none => intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
  | some s1 => intro _; simp only [Option.map_some, mkNext, advance]

theorem delaySlotRel_sh (s : State) (t : W32) (a b c : W32) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } (.sh a b c))
      (execInstr { s with pendingBranch := some t } (.sh a b c)) := by
  rw [execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl),
    execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)]
  simp only [execBody, readReg_pb, writeMemHalf_pb]
  cases writeMemHalf s (readReg s (regIdx a) + signExt16 c) (readReg s (regIdx b)) with
  | none => intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
  | some s1 => intro _; simp only [Option.map_some, mkNext, advance]

theorem delaySlotRel_sb (s : State) (t : W32) (a b c : W32) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } (.sb a b c))
      (execInstr { s with pendingBranch := some t } (.sb a b c)) := by
  rw [execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl),
    execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)]
  simp only [execBody, readReg_pb, writeMemByte_pb]
  cases writeMemByte s (readReg s (regIdx a) + signExt16 c) (readReg s (regIdx b) &&& 0xff#32).toNat.toUInt8 with
  | none => intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
  | some s1 => intro _; simp only [Option.map_some, mkNext, advance]

theorem delaySlotRel_sc (s : State) (t : W32) (a b c : W32) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } (.sc a b c))
      (execInstr { s with pendingBranch := some t } (.sc a b c)) := by
  rw [execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl),
    execInstr_eq_body _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)]
  simp only [execBody, readReg_pb, writeMemWord_pb]
  cases writeMemWord s (readReg s (regIdx a) + signExt16 c) (readReg s (regIdx b)) with
  | none => intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
  | some s1 =>
    simp only [Option.map_some]
    refine DelaySlotRel_ite _ _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_) <;>
      (intro _; simp only [mkNext, advance, writeReg_pb])

theorem delaySlotRel_swc1 (s : State) (t : W32) (a b c : W32) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } (.swc1 a b c))
      (execInstr { s with pendingBranch := some t } (.swc1 a b c)) := by
  by_cases hcu : cu1Enabled s = true
  case neg =>
    have hf : cu1Enabled s = false := by simpa using hcu
    intro h
    have e : execInstr { s with pendingBranch := none } (.swc1 a b c) =
        takeCoprocessorUnusable { s with pendingBranch := none } := by
      unfold execInstr
      simp only [show isBranchLike (Instruction.swc1 a b c) = false from rfl,
        show usesCop1 (Instruction.swc1 a b c) = true from rfl, cu1Enabled_pb, hf, Bool.false_and,
        Bool.not_false, Bool.and_self, ↓reduceIte, Bool.false_eq_true]
    rw [e] at h
    exact absurd (h.symm.trans (takeCoprocessorUnusable_pc_pb _ _)) hvec
  rw [execInstr_eq_body { s with pendingBranch := none } _ (Or.inl rfl) (Or.inr hcu) (Or.inl rfl),
    execInstr_eq_body { s with pendingBranch := some t } _ (Or.inl rfl) (Or.inr hcu) (Or.inl rfl)]
  simp only [execBody, readReg_pb, readFpReg_pb, writeMemWord_pb]
  cases writeMemWord s (readReg s (regIdx a) + signExt16 c) (readFpReg s (regIdx b)) with
  | none => intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
  | some s1 => intro _; simp only [Option.map_some, mkNext, advance]

theorem delaySlotRel_swxc1 (s : State) (t : W32) (a b c : W32) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } (.swxc1 a b c))
      (execInstr { s with pendingBranch := some t } (.swxc1 a b c)) := by
  by_cases hcu : cu1Enabled s = true
  case neg =>
    have hf : cu1Enabled s = false := by simpa using hcu
    intro h
    have e : execInstr { s with pendingBranch := none } (.swxc1 a b c) =
        takeCoprocessorUnusable { s with pendingBranch := none } := by
      unfold execInstr
      simp only [show isBranchLike (Instruction.swxc1 a b c) = false from rfl,
        show usesCop1 (Instruction.swxc1 a b c) = true from rfl, cu1Enabled_pb, hf, Bool.false_and,
        Bool.not_false, Bool.and_self, ↓reduceIte, Bool.false_eq_true]
    rw [e] at h
    exact absurd (h.symm.trans (takeCoprocessorUnusable_pc_pb _ _)) hvec
  rw [execInstr_eq_body { s with pendingBranch := none } _ (Or.inl rfl) (Or.inr hcu) (Or.inl rfl),
    execInstr_eq_body { s with pendingBranch := some t } _ (Or.inl rfl) (Or.inr hcu) (Or.inl rfl)]
  simp only [execBody, readReg_pb, readFpReg_pb, writeMemWord_pb]
  cases writeMemWord s (readReg s (regIdx c) + readReg s (regIdx b)) (readFpReg s (regIdx a)) with
  | none => intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
  | some s1 => intro _; simp only [Option.map_some, mkNext, advance]

theorem delaySlotRel_sdc1 (s : State) (t : W32) (a b c : W32) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } (.sdc1 a b c))
      (execInstr { s with pendingBranch := some t } (.sdc1 a b c)) := by
  by_cases hcu : cu1Enabled s = true
  case neg =>
    have hf : cu1Enabled s = false := by simpa using hcu
    intro h
    have e : execInstr { s with pendingBranch := none } (.sdc1 a b c) =
        takeCoprocessorUnusable { s with pendingBranch := none } := by
      unfold execInstr
      simp only [show isBranchLike (Instruction.sdc1 a b c) = false from rfl,
        show usesCop1 (Instruction.sdc1 a b c) = true from rfl, cu1Enabled_pb, hf, Bool.false_and,
        Bool.not_false, Bool.and_self, ↓reduceIte, Bool.false_eq_true]
    rw [e] at h
    exact absurd (h.symm.trans (takeCoprocessorUnusable_pc_pb _ _)) hvec
  rw [execInstr_eq_body { s with pendingBranch := none } _ (Or.inl rfl) (Or.inr hcu) (Or.inl rfl),
    execInstr_eq_body { s with pendingBranch := some t } _ (Or.inl rfl) (Or.inr hcu) (Or.inl rfl)]
  simp only [execBody, readReg_pb, readFpReg_pb, writeMemWord_pb]
  split
  · intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
  cases writeMemWord s (readReg s (regIdx a) + signExt16 c) (readFpReg s (regIdx (b + 1#32))) with
  | none => intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
  | some s1 =>
    simp only [Option.map_some, writeMemWord_pb]
    cases writeMemWord s1 ((readReg s (regIdx a) + signExt16 c) + 4#32) (readFpReg s (regIdx b)) with
    | none => intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
    | some s2 => intro _; simp only [Option.map_some, mkNext, advance]

theorem delaySlotRel_sdxc1 (s : State) (t : W32) (a b c : W32) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } (.sdxc1 a b c))
      (execInstr { s with pendingBranch := some t } (.sdxc1 a b c)) := by
  by_cases hcu : cu1Enabled s = true
  case neg =>
    have hf : cu1Enabled s = false := by simpa using hcu
    intro h
    have e : execInstr { s with pendingBranch := none } (.sdxc1 a b c) =
        takeCoprocessorUnusable { s with pendingBranch := none } := by
      unfold execInstr
      simp only [show isBranchLike (Instruction.sdxc1 a b c) = false from rfl,
        show usesCop1 (Instruction.sdxc1 a b c) = true from rfl, cu1Enabled_pb, hf, Bool.false_and,
        Bool.not_false, Bool.and_self, ↓reduceIte, Bool.false_eq_true]
    rw [e] at h
    exact absurd (h.symm.trans (takeCoprocessorUnusable_pc_pb _ _)) hvec
  rw [execInstr_eq_body { s with pendingBranch := none } _ (Or.inl rfl) (Or.inr hcu) (Or.inl rfl),
    execInstr_eq_body { s with pendingBranch := some t } _ (Or.inl rfl) (Or.inr hcu) (Or.inl rfl)]
  simp only [execBody, readReg_pb, readFpReg_pb, writeMemWord_pb]
  split
  · intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
  cases writeMemWord s (readReg s (regIdx c) + readReg s (regIdx b)) (readFpReg s (regIdx (a + 1#32))) with
  | none => intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
  | some s1 =>
    simp only [Option.map_some, writeMemWord_pb]
    cases writeMemWord s1 ((readReg s (regIdx c) + readReg s (regIdx b)) + 4#32) (readFpReg s (regIdx a)) with
    | none => intro h; exact absurd (h.symm.trans (takeAddressException_pc_pb _ _ _ _)) hvec
    | some s2 => intro _; simp only [Option.map_some, mkNext, advance]


set_option maxHeartbeats 0 in
/-- The delay-slot relation holds for every non-control-transfer
instruction. Proved structurally: after unfolding, both runs have the same
shape and are compared leaf by leaf. -/
theorem execInstr_delaySlotRel (s : State) (t : W32) (instr : Instruction)
    (hnb : isBranchLike instr = false) (hvec : s.pc + 4#32 ≠ exceptionVector s) :
    DelaySlotRel (s.pc + 4#32) t
      (execInstr { s with pendingBranch := none } instr)
      (execInstr { s with pendingBranch := some t } instr) := by
  cases instr <;> first | exact Bool.noConfusion (hnb : true = false) | skip
  case rdhwr rt rd => exact delaySlotRel_rdhwr s t rt rd hvec
  case lwl rs rt imm => exact delaySlotRel_lwl s t rs rt imm hvec
  case lwr rs rt imm => exact delaySlotRel_lwr s t rs rt imm hvec
  case swl rs rt imm => exact delaySlotRel_swl s t rs rt imm hvec
  case swr rs rt imm => exact delaySlotRel_swr s t rs rt imm hvec
  case sw a b c => exact delaySlotRel_sw s t a b c hvec
  case sh a b c => exact delaySlotRel_sh s t a b c hvec
  case sb a b c => exact delaySlotRel_sb s t a b c hvec
  case sc a b c => exact delaySlotRel_sc s t a b c hvec
  case swc1 a b c => exact delaySlotRel_swc1 s t a b c hvec
  case swxc1 a b c => exact delaySlotRel_swxc1 s t a b c hvec
  case sdc1 a b c => exact delaySlotRel_sdc1 s t a b c hvec
  case sdxc1 a b c => exact delaySlotRel_sdxc1 s t a b c hvec
  all_goals (
    obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, pb, llBit, cp0Status, cp0Cause, cp0Epc, cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase, cp0ConfigK0, cp0ConfigK23, cp0ConfigKU,
    cp0Count, cp0Compare, cp0TimerInt, cp0HWREna⟩ := s
    unfold execInstr execBody
    dsimp only [isBranchLike]
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, mkNext, advance,
      takeException, takeAddressException, readReg, readFpReg, readMemWord, readMemHalf, readMemByte,
      translate, accessAllowed, kernelMode, erlSet, writeFpReg, readFpD, writeFpD, fpFinishS, fpFinishD,
      fpFinishCmp, takeCoprocessorUnusable, readFcc,
      writeReg_proj_pc, writeReg_proj_hi, writeReg_proj_lo,
      writeReg_proj_fpRegs, writeReg_proj_fcsr, writeReg_proj_mem,
      writeReg_proj_pendingBranch, writeReg_proj_llBit, writeReg_proj_cp0Status,
      writeReg_proj_cp0Cause, writeReg_proj_cp0Epc, writeReg_proj_cp0BadVAddr,
      writeReg_proj_cp0ErrorEpc, writeReg_proj_llAddr, writeReg_proj_cp0EBase, writeReg_proj_cp0ConfigK0, writeReg_proj_cp0ConfigK23, writeReg_proj_cp0ConfigKU,
      writeReg_proj_cp0Count, writeReg_proj_cp0Compare, writeReg_proj_cp0TimerInt,
      writeReg_proj_cp0HWREna, writeReg_proj_regs]
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
  unfold step execute at h0 ⊢
  rw [show readMemWord ({ s with pendingBranch := none } : State) ({ s with pendingBranch := none } : State).pc = some w from hfetch] at h0
  rw [show readMemWord ({ s with pendingBranch := some t } : State) ({ s with pendingBranch := some t } : State).pc = some w from hfetch]
  dsimp only at h0 ⊢
  rw [hdecode] at h0 ⊢
  dsimp only at h0 ⊢
  subst h0
  rw [execInstr_delay_slot s t instr _ hnb hvec rfl hnormal]
  rfl

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
    step s = timerTick (takeException s excCodeRI) := by
  have hbr' : isBranchLike instr = true := hbr
  unfold step execute
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  unfold execInstr
  simp only [hpb, hbr', Bool.and_self, ↓reduceIte]
