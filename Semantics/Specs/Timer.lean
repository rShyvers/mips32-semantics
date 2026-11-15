import Lean.Elab.Tactic
import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures
import Semantics.Specs.Exception
import Semantics.Specs.Cp0

/-!
# Timer — `Count`/`Compare`, `Cause.TI`, `HWREna` and `rdhwr`

Constructors: `rdhwr`.

Manual pages: MD00090 Vol III Rev 6.02 §9.27 Count (p.183), §9.30 Compare (p.187), §9.36 Cause
(`TI` p.209, `DC` p.210, `IP7..IP2` p.211), §9.23 HWREna (p.175-176), §6.1.1.1 Table 6.2 (p.73),
§9.33 IntCtl.IPTI (p.199); MD00086 Vol II-A Rev 6.06 RDHWR (p.332-334).

Reference: `docs/spec/INSTRUCTION-REF.md`, "rdhwr"; pins in `docs/spec/SPEC-NOTES.md` §9 item 28.

`step s = timerTick (stepCore s)` (`Step.lean`): the instruction (`execute`, or an interrupt entry or a standby step: `stepCore`) and then the timer
(`timerTick`: `Count` + 1 unless `Cause.DC = 1`, `Cause.TI` set when `Count = Compare`). What this
file proves:

* **Count advances once per step** (`step_count_advances`): unless `Cause.DC = 1` or the
  instruction itself writes `Count`, `Compare` or `Cause` (`fetchesTimerWrite`), `Count` goes up
  by exactly one, whatever the instruction does (exceptions included). `step_count_stopped`: with
  `Cause.DC = 1` it does not move. Both rest on `execute_timerKept`: no other instruction touches
  `Count`, `Compare`, `Cause.TI` or `Cause.DC`, proved structurally over every constructor.
* **The match sets `Cause.TI`** (`step_timer_match_sets_ti`, every state, no side condition), and
  `TI` stays set until `Compare` is written (`step_timerInt`).
* **A write to `Compare` clears the timer interrupt** (`mtc0_compare_clears_ti`): after `mtc0 $rt,
  $11`, `TI` is set only if the new `Count` equals the new `Compare`.
* `mtc0`/`mfc0` of `Count`, and `Cause` as read (`TI`, `IP7`): `mtc0_count_spec`,
  `causeValue_timer`.
* **`rdhwr`**: `rdhwr_spec_raw`; the access rule (`rdhwr_reserved_unimplemented`,
  `rdhwr_reserved_not_enabled`, `rdhwr_allowed`); the register values (`hwrValue_*`).

## Theorems in this file (50)

  `step_eq_timerTick_stepCore` `timerTick_count` `step_timer_match_sets_ti` `timerKept_advance`
  `countEnabled_exceptionEntry` `stepCore_timerKept` `writeMemWord_timerFields` `writeMemHalf_timerFields`
  `writeMemByte_timerFields` `execInstr_timerKept` `execute_timerKept` `step_count_advances`
  `step_count_stopped` `step_timerInt` `mtc0_count_spec` `mtc0_compare_clears_ti`
  `mtc0_compare_no_match_clears_ti` `causeValue_timer` `causeValue_no_timer` `rdhwr_spec_raw`
  `hwrValue_cpuNum` `hwrValue_synciStep` `hwrValue_cc` `hwrValue_ccRes` `hwrValue_unimplemented`
  `rdhwrAllowed_iff` `rdhwr_reserved_unimplemented` `rdhwr_reserved_not_enabled` `rdhwr_allowed`
  `rdhwr_cc_reads_count` `hwrena_write_masked` `resetException_timer` `advance_cp0Count`
  `advance_cp0Compare` `advance_cp0TimerInt` `advance_cp0Cause` `advance_hwInt` `mkNext_eq_advance`
  `exceptionEntry_cp0Count` `exceptionEntry_cp0Compare` `exceptionEntry_cp0TimerInt` `exceptionEntry_hwInt`
  `exceptionEntry_dc` `takeException_eq` `takeAddressException_eq` `takeCoprocessorUnusable_eq`
  `takeCop0Unusable_eq` `writeFpReg_timer` `writeFpD_timer` `writeMemByte_getD_timer`
-/

set_option maxRecDepth 4000

/-! ## The timer tick -/

/-- `step` is the processor's part (`stepCore`: an interrupt, a standby step, or the instruction)
followed by the timer (definition of `step`). -/
theorem step_eq_timerTick_stepCore (s : State) : step s = timerTick (stepCore s) := rfl

/-- **What one tick does to `Count`**: + 1 (modulo 2^32) when counting is enabled (`Cause.DC = 0`),
unchanged otherwise (MD00090 Vol III Rev 6.02 §9.27, p.183; Table 9.52 `DC`, p.210). -/
theorem timerTick_count (s : State) :
    (timerTick s).cp0Count = if countEnabled s then s.cp0Count + 1#32 else s.cp0Count := rfl

/-- **`Count = Compare` sets `Cause.TI`**, after every step, from every state: "When the value of
the Count register equals the value of the Compare register, an interrupt request is made" (MD00090
Vol III Rev 6.02 §9.30, p.187), visible in `Cause.TI` (Table 9.52, p.209). -/
theorem step_timer_match_sets_ti (s : State) (h : (step s).cp0Count = (step s).cp0Compare) :
    (step s).cp0TimerInt = true := by
  show ((stepCore s).cp0TimerInt ||
    (timerTick (stepCore s)).cp0Count == (stepCore s).cp0Compare) = true
  have h' : (timerTick (stepCore s)).cp0Count = (stepCore s).cp0Compare := h
  rw [h']
  simp

/-! ## No instruction but `mtc0 Count/Compare/Cause` touches the timer state

Proof device: `TimerKept s r` says that `r` has the `Count`, `Compare`, `Cause.TI` and `Cause.DC` of
`s`. Every result shape of `execInstr` keeps them (`writeReg`, `writeFp*`, `writeMem*`, record
updates of other fields, exception entry, which writes only `BD`, `CE`, `ExcCode` of `Cause`);
`execInstr_timerKept` checks this for every constructor, with the same structural tactic loop as
`execInstr_sizesKept` (`RegFileSize.lean`). -/

/-- Proof device: `r` has the timer state of `s` (and its hardware interrupt lines, which no
instruction writes either). -/
def TimerKept (s r : State) : Prop :=
  r.cp0Count = s.cp0Count ∧ r.cp0Compare = s.cp0Compare ∧ r.cp0TimerInt = s.cp0TimerInt ∧
    r.cp0Cause &&& causeDcMask = s.cp0Cause &&& causeDcMask ∧ r.hwInt = s.hwInt

theorem timerKept_advance (s o r : State) : TimerKept s (advance o r) ↔ TimerKept s r := by
  unfold advance; split <;> exact Iff.rfl

theorem advance_cp0Count (o r : State) : (advance o r).cp0Count = r.cp0Count := by
  unfold advance; split <;> rfl
theorem advance_cp0Compare (o r : State) : (advance o r).cp0Compare = r.cp0Compare := by
  unfold advance; split <;> rfl
theorem advance_cp0TimerInt (o r : State) : (advance o r).cp0TimerInt = r.cp0TimerInt := by
  unfold advance; split <;> rfl
theorem advance_cp0Cause (o r : State) : (advance o r).cp0Cause = r.cp0Cause := by
  unfold advance; split <;> rfl
theorem advance_hwInt (o r : State) : (advance o r).hwInt = r.hwInt := by
  unfold advance; split <;> rfl

theorem mkNext_eq_advance (o r : State) : mkNext o r = advance o r := rfl

theorem exceptionEntry_cp0Count (r : State) (c ce : W32) :
    (exceptionEntry r c ce).cp0Count = r.cp0Count := rfl
theorem exceptionEntry_cp0Compare (r : State) (c ce : W32) :
    (exceptionEntry r c ce).cp0Compare = r.cp0Compare := rfl
theorem exceptionEntry_cp0TimerInt (r : State) (c ce : W32) :
    (exceptionEntry r c ce).cp0TimerInt = r.cp0TimerInt := rfl
theorem exceptionEntry_hwInt (r : State) (c ce : W32) :
    (exceptionEntry r c ce).hwInt = r.hwInt := rfl

/-- Exception entry keeps `Cause.DC` (it writes only `BD`, `CE`, `ExcCode`). -/
theorem exceptionEntry_dc (r : State) (c ce : W32) :
    (exceptionEntry r c ce).cp0Cause &&& causeDcMask = r.cp0Cause &&& causeDcMask :=
  exceptionEntry_cause_other_bits r c ce causeDcMask (by decide) (by decide) (by decide)

/-- Exception entry keeps counting enabled or disabled. -/
theorem countEnabled_exceptionEntry (s : State) (c ce : W32) :
    countEnabled (exceptionEntry s c ce) = countEnabled s := by
  unfold countEnabled
  rw [exceptionEntry_dc]

theorem takeException_eq (r : State) (c : W32) : takeException r c = exceptionEntry r c := rfl
theorem takeAddressException_eq (r : State) (c a : W32) :
    takeAddressException r c a = exceptionEntry { r with cp0BadVAddr := a } c := rfl
theorem takeCoprocessorUnusable_eq (r : State) :
    takeCoprocessorUnusable r = exceptionEntry r excCodeCpU 1#32 := rfl
theorem takeCop0Unusable_eq (r : State) :
    takeCop0Unusable r = exceptionEntry r excCodeCpU 0#32 := rfl

theorem writeFpReg_timer (r : State) (i : Fin 32) (v : W32) :
    (writeFpReg r i v).cp0Count = r.cp0Count ∧ (writeFpReg r i v).cp0Compare = r.cp0Compare ∧
      (writeFpReg r i v).cp0TimerInt = r.cp0TimerInt ∧ (writeFpReg r i v).cp0Cause = r.cp0Cause ∧
      (writeFpReg r i v).hwInt = r.hwInt :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem writeFpD_timer (r : State) (f : W32) (v : BitVec 64) :
    (writeFpD r f v).cp0Count = r.cp0Count ∧ (writeFpD r f v).cp0Compare = r.cp0Compare ∧
      (writeFpD r f v).cp0TimerInt = r.cp0TimerInt ∧ (writeFpD r f v).cp0Cause = r.cp0Cause ∧
      (writeFpD r f v).hwInt = r.hwInt :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A word store changes only memory. -/
theorem writeMemWord_timerFields (s s' : State) (a v : W32) (h : writeMemWord s a v = some s') :
    s'.cp0Count = s.cp0Count ∧ s'.cp0Compare = s.cp0Compare ∧ s'.cp0TimerInt = s.cp0TimerInt ∧
      s'.cp0Cause = s.cp0Cause ∧ s'.hwInt = s.hwInt := by
  unfold writeMemWord at h
  split at h
  · cases h
  · split at h
    · cases h
    · injection h with h'
      rw [← h']
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A halfword store changes only memory. -/
theorem writeMemHalf_timerFields (s s' : State) (a v : W32) (h : writeMemHalf s a v = some s') :
    s'.cp0Count = s.cp0Count ∧ s'.cp0Compare = s.cp0Compare ∧ s'.cp0TimerInt = s.cp0TimerInt ∧
      s'.cp0Cause = s.cp0Cause ∧ s'.hwInt = s.hwInt := by
  unfold writeMemHalf at h
  split at h
  · cases h
  · split at h
    · cases h
    · injection h with h'
      rw [← h']
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A byte store changes only memory. -/
theorem writeMemByte_timerFields (s s' : State) (a : W32) (v : UInt8)
    (h : writeMemByte s a v = some s') :
    s'.cp0Count = s.cp0Count ∧ s'.cp0Compare = s.cp0Compare ∧ s'.cp0TimerInt = s.cp0TimerInt ∧
      s'.cp0Cause = s.cp0Cause ∧ s'.hwInt = s.hwInt := by
  unfold writeMemByte at h
  split at h
  · cases h
  · injection h with h'
    rw [← h']
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem writeMemByte_getD_timer (r : State) (a : W32) (v : UInt8) :
    ((writeMemByte r a v).getD r).cp0Count = r.cp0Count ∧
      ((writeMemByte r a v).getD r).cp0Compare = r.cp0Compare ∧
      ((writeMemByte r a v).getD r).cp0TimerInt = r.cp0TimerInt ∧
      ((writeMemByte r a v).getD r).cp0Cause = r.cp0Cause ∧
      ((writeMemByte r a v).getD r).hwInt = r.hwInt := by
  unfold writeMemByte; cases translate r a <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Forward step for the tactic loop below: for every hypothesis
`writeMem{Byte,Half,Word} s a v = some s'` in the context, add the four timer-field equations. -/
elab "tk_fwd" : tactic => Lean.Elab.Tactic.withMainContext do
  for d in (← Lean.getLCtx) do
    if d.isImplementationDetail then continue
    for lem in [``writeMemByte_timerFields, ``writeMemHalf_timerFields, ``writeMemWord_timerFields] do
      try
        let pf ← Lean.Meta.mkAppOptM lem #[none, none, none, none, some d.toExpr]
        let ty ← Lean.Meta.inferType pf
        Lean.Elab.Tactic.liftMetaTactic fun g => do
          let (_, g) ← (← g.assert `htk ty pf).intro1
          return [g]
      catch _ => pure ()

/-- Simp set for the tactic loop below: unfold `TimerKept` and push the four timer fields through
every state-update primitive (plus the equations `tk_fwd` put in the context). -/
macro "tk_simp" : tactic => `(tactic|
  simp only [TimerKept, mkNext_eq_advance, advance_cp0Count, advance_cp0Compare,
    advance_cp0TimerInt, advance_cp0Cause, advance_hwInt, takeException_eq, takeAddressException_eq,
    takeCoprocessorUnusable_eq, takeCop0Unusable_eq, exceptionEntry_cp0Count,
    exceptionEntry_cp0Compare, exceptionEntry_cp0TimerInt, exceptionEntry_dc, exceptionEntry_hwInt,
    writeReg_proj_cp0Count, writeReg_proj_cp0Compare, writeReg_proj_cp0TimerInt, writeReg_proj_hwInt,
    writeReg_proj_cp0Cause, writeFpReg_timer, writeFpD_timer, writeMemByte_getD_timer,
    fpFinishS, fpFinishD, fpFinishCmp, and_self, *])

-- ~190 constructors through one generic tactic loop
set_option maxHeartbeats 4000000 in
/-- **No instruction other than `mtc0` to `Count`, `Compare` or `Cause` changes `Count`, `Compare`,
`Cause.TI` or `Cause.DC`**, in any state (in or out of a delay slot, with or without an
exception). Proved structurally over every constructor. -/
theorem execInstr_timerKept (s : State) (instr : Instruction) (hw : writesTimer instr = false) :
    TimerKept s (execInstr s instr) := by
  unfold execInstr
  split
  · tk_simp
  · split
    · tk_simp
    · split
      · tk_simp
      · unfold execBody
        cases instr <;> simp only [writesTimer] at hw <;> dsimp only <;>
          repeat' (first | (tk_fwd; tk_simp; done) | split | (unfold fpFinishS; dsimp only) |
            (unfold fpThen; dsimp only) | (unfold fpStep; dsimp only) |
            (unfold fpFinishD; dsimp only) | (unfold fpFinishCmp; dsimp only) |
            (simp [*] at hw; done))

/-- **`execute` (fetch, decode, execute) keeps the timer state** unless the fetched instruction is
an `mtc0` to `Count`, `Compare` or `Cause`. -/
theorem execute_timerKept (s : State) (hw : fetchesTimerWrite s = false) :
    TimerKept s (execute s) := by
  unfold execute
  unfold fetchesTimerWrite at hw
  split
  · tk_simp
  · rename_i w hfetch
    simp only [hfetch] at hw
    split
    · split
      · tk_simp
      · split
        · tk_simp
        · split <;> tk_simp
    · rename_i instr hdec
      simp only [hdec] at hw
      exact execInstr_timerKept s instr hw

/-- **`stepCore` keeps the timer state** unless it executes an `mtc0` to `Count`, `Compare` or
`Cause`: the Interrupt exception is an exception entry (which writes only `BD`, `CE`, `ExcCode` of
`Cause`), a standby step changes only `standby`, and a nullified step only `pc`, `pendingBranch` and
`nullified`. -/
theorem stepCore_timerKept (s : State) (hw : fetchesTimerWrite s = false) :
    TimerKept s (stepCore s) := by
  unfold stepCore
  split
  · unfold takeInterrupt
    exact ⟨rfl, rfl, rfl, exceptionEntry_dc s _ _, rfl⟩
  split
  · unfold standbyStep; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact execute_timerKept s hw

/-! ## Count, TI and Compare at the level of `step` -/

/-- **`Count` advances by one on every step** (pin of the implementation-dependent rate, MD00090
Vol III Rev 6.02 §9.27, p.183: "incrementing at a constant rate, whether or not an instruction is
executed"), when counting is enabled (`Cause.DC = 0`, Table 9.52, p.210) and the instruction at
`pc` does not itself write `Count`, `Compare` or `Cause`. Whatever else the step does — an ordinary
instruction, a branch, any exception, a fetch that fails — `Count` goes from `c` to `c + 1`
(modulo 2^32). -/
theorem step_count_advances (s : State) (hdc : countEnabled s = true)
    (hw : fetchesTimerWrite s = false) :
    (step s).cp0Count = s.cp0Count + 1#32 := by
  obtain ⟨h1, -, -, h4, -⟩ := stepCore_timerKept s hw
  have hce : countEnabled (stepCore s) = true := by
    unfold countEnabled at hdc ⊢; rw [h4]; exact hdc
  show (if countEnabled (stepCore s) then (stepCore s).cp0Count + 1#32 else (stepCore s).cp0Count) = _
  rw [hce, h1]
  rfl

/-- **With `Cause.DC = 1`, `Count` does not move** ("Disable counting of Count register", MD00090
Vol III Rev 6.02 Table 9.52, p.210), unless the instruction writes `Count`, `Compare` or `Cause`. -/
theorem step_count_stopped (s : State) (hdc : countEnabled s = false)
    (hw : fetchesTimerWrite s = false) :
    (step s).cp0Count = s.cp0Count := by
  obtain ⟨h1, -, -, h4, -⟩ := stepCore_timerKept s hw
  have hce : countEnabled (stepCore s) = false := by
    unfold countEnabled at hdc ⊢; rw [h4]; exact hdc
  show (if countEnabled (stepCore s) then (stepCore s).cp0Count + 1#32 else (stepCore s).cp0Count) = _
  rw [hce, h1]
  rfl

/-- **`Cause.TI` after a step** that does not write `Count`, `Compare` or `Cause`: it stays set
if it was set, and becomes set exactly when the new `Count` equals `Compare`; `Compare` does not
change ("maintains a stable value and does not change on its own", MD00090 Vol III Rev 6.02 §9.30,
p.187). -/
theorem step_timerInt (s : State) (hw : fetchesTimerWrite s = false) :
    (step s).cp0TimerInt = (s.cp0TimerInt || (step s).cp0Count == s.cp0Compare) ∧
      (step s).cp0Compare = s.cp0Compare := by
  obtain ⟨-, h2, h3, -, -⟩ := stepCore_timerKept s hw
  refine ⟨?_, h2⟩
  show ((stepCore s).cp0TimerInt || (timerTick (stepCore s)).cp0Count == (stepCore s).cp0Compare) = _
  rw [h2, h3]
  rfl

/-- **`mtc0 $rt, $9` (`Count`)**: the written value is what the timer advances from ("The Count
register can be written for functional or diagnostic purposes", MD00090 Vol III Rev 6.02 §9.27,
p.183): after the step `Count` is `$rt + 1`, or `$rt` with `Cause.DC = 1`. -/
theorem mtc0_count_spec (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 9#32 0#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    (step s).cp0Count =
      if countEnabled s then readReg s (regIdxSpec rt) + 1#32 else readReg s (regIdxSpec rt) := by
  rw [mtc0_spec_raw s w rt 9#32 0#32 hfetch hdecode hpb hcp0 hexec]
  rfl

/-- **A write to `Compare` clears the timer interrupt** ("Writing a value to the Compare register,
as a side effect, clears the timer interrupt", MD00090 Vol III Rev 6.02 §9.30, p.187): after
`mtc0 $rt, $11`, `Compare` holds `$rt` and `Cause.TI` is set only if the new `Count` equals it
(a new match in the same step); a pending timer interrupt from before is gone. -/
theorem mtc0_compare_clears_ti (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 11#32 0#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    (step s).cp0Compare = readReg s (regIdxSpec rt) ∧
      (step s).cp0TimerInt = ((step s).cp0Count == readReg s (regIdxSpec rt)) ∧
      (step s).cp0Count = (if countEnabled s then s.cp0Count + 1#32 else s.cp0Count) := by
  rw [mtc0_spec_raw s w rt 11#32 0#32 hfetch hdecode hpb hcp0 hexec]
  exact ⟨rfl, Bool.false_or _, rfl⟩

/-- **Corollary: after writing `Compare` with a value the new `Count` does not reach, no timer
interrupt is pending.** -/
theorem mtc0_compare_no_match_clears_ti (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 11#32 0#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true)
    (hne : (if countEnabled s then s.cp0Count + 1#32 else s.cp0Count) ≠ readReg s (regIdxSpec rt)) (hexec : executesInstr s = true) :
    (step s).cp0TimerInt = false := by
  obtain ⟨-, hti, hc⟩ := mtc0_compare_clears_ti s w rt hfetch hdecode hpb hcp0 hexec
  rw [hti, hc]
  simpa using hne

/-- **`Cause` as `mfc0` reads it, with a timer interrupt pending**: `TI` (bit 30) and `IP7`
(bit 15) are set (MD00090 Vol III Rev 6.02 Table 9.52, p.209, 211; the timer request is merged into
`IP7`, Table 6.2, p.73, the `IntCtl.IPTI = 7` pin); every other bit is the stored `Cause`. -/
theorem causeValue_timer (s : State) (h : s.cp0TimerInt = true) :
    causeValue s = s.cp0Cause ||| hwIntBits s ||| causeTiMask ||| causeIp7Mask := by
  unfold causeValue; rw [h]; simp [BitVec.or_assoc]

/-- **… and without one, the stored `Cause` with the hardware interrupt lines** (the stored
`TI` and `IP7..IP2` bits are never set: `mtc0` cannot write them, exception entry writes only `BD`,
`CE`, `ExcCode`). -/
theorem causeValue_no_timer (s : State) (h : s.cp0TimerInt = false) :
    causeValue s = s.cp0Cause ||| hwIntBits s := by
  unfold causeValue; rw [h]; simp

/-! ## `rdhwr` -/

/-- **`rdhwr $rt, $rd`** (MD00086 Vol II-A Rev 6.06, RDHWR, p.332-334): if hardware register `rd`
is implemented (`hwrValue s rd = some v`) and access is allowed (`rdhwrAllowed`: Coprocessor 0
enabled, or bit `rd` of `HWREna`), `$rt ← v` and `pc` advances; otherwise Reserved Instruction
("If access is not allowed or the register is not implemented, a Reserved Instruction Exception is
signaled", p.333). -/
theorem rdhwr_spec_raw (s : State) (w rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdhwr rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      match hwrValue s rd with
      | some v =>
        if rdhwrAllowed s rd then
          { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }
        else takeException s excCodeRI
      | none => takeException s excCodeRI) := by
  step_spec

/-- `CPUNum` (`rdhwr` register 0) is `EBase.CPUNum`, which reads 0 (one processor). -/
theorem hwrValue_cpuNum (s : State) : hwrValue s 0#32 = some 0#32 := by
  show some (((s.cp0EBase &&& ebaseWriteMask) ||| ebaseFixedBits) &&& 0x3FF#32) = some 0#32
  congr 1
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc,
    show ebaseWriteMask &&& 0x3FF#32 = 0#32 by decide,
    show ebaseFixedBits &&& 0x3FF#32 = 0#32 by decide, BitVec.and_zero, BitVec.or_zero]

/-- `SYNCI_Step` (`rdhwr` register 1) is 0: no caches need be synchronized. -/
theorem hwrValue_synciStep (s : State) : hwrValue s 1#32 = some 0#32 := rfl

/-- `CC` (`rdhwr` register 2) is `Count`. -/
theorem hwrValue_cc (s : State) : hwrValue s 2#32 = some s.cp0Count := rfl

/-- `CCRes` (`rdhwr` register 3) is 1: `Count` advances once per step. -/
theorem hwrValue_ccRes (s : State) : hwrValue s 3#32 = some 1#32 := rfl

/-- Registers 4..31 are not implemented (`PerfCtr`, `XNP` are Release 6; 6..28 reserved; `ULR`
needs the optional UserLocal register; 30, 31 implementation-dependent, none). -/
theorem hwrValue_unimplemented (s : State) (rd : W32) (h : 4 ≤ rd.toNat) : hwrValue s rd = none := by
  unfold hwrValue
  split <;> first | rfl | omega

/-- The access rule as a formula: Coprocessor 0 enabled (Kernel Mode or `Status.CU0 = 1`), or bit
`rd` of `HWREna` set. -/
theorem rdhwrAllowed_iff (s : State) (rd : W32) :
    rdhwrAllowed s rd = true ↔ (cp0Usable s = true ∨ (s.cp0HWREna >>> rd) &&& 1#32 ≠ 0#32) := by
  unfold rdhwrAllowed; simp

/-- **`rdhwr` of an unimplemented register raises Reserved Instruction**, in every mode
(MD00086 Vol II-A Rev 6.06, RDHWR, Table 5.4 and Restrictions, p.333). -/
theorem rdhwr_reserved_unimplemented (s : State) (w rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdhwr rt rd))
    (hpb : s.pendingBranch = none) (hrd : 4 ≤ rd.toNat) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) := by
  rw [rdhwr_spec_raw s w rt rd hfetch hdecode hpb hexec, hwrValue_unimplemented s rd hrd]

/-- **`rdhwr` outside Kernel Mode with `Status.CU0 = 0` and the `HWREna` bit clear raises Reserved
Instruction** (not Coprocessor Unusable): "Access to the specified hardware register is enabled if
Coprocessor 0 is enabled, or if the corresponding bit is set in the HWREna register. If access is
not allowed ... a Reserved Instruction Exception is signaled" (MD00086 Vol II-A Rev 6.06, RDHWR,
p.333). -/
theorem rdhwr_reserved_not_enabled (s : State) (w rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdhwr rt rd))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = false)
    (hen : (s.cp0HWREna >>> rd) &&& 1#32 = 0#32) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) := by
  rw [rdhwr_spec_raw s w rt rd hfetch hdecode hpb hexec]
  have ha : rdhwrAllowed s rd = false := by
    unfold rdhwrAllowed; rw [hcp0, hen]; rfl
  split
  · rw [ha]; rfl
  · rfl

/-- **`rdhwr` of an implemented register with access allowed** writes the register's value to
`$rt` and advances `pc`. -/
theorem rdhwr_allowed (s : State) (w rt rd v : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdhwr rt rd))
    (hpb : s.pendingBranch = none) (hv : hwrValue s rd = some v)
    (hacc : cp0Usable s = true ∨ (s.cp0HWREna >>> rd) &&& 1#32 ≠ 0#32) (hexec : executesInstr s = true) :
    step s = timerTick
      { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 } := by
  rw [rdhwr_spec_raw s w rt rd hfetch hdecode hpb hexec, hv]
  have ha : rdhwrAllowed s rd = true := (rdhwrAllowed_iff s rd).2 hacc
  simp only [ha, ↓reduceIte]

/-- **`rdhwr $rt, $2` reads `Count`** — in User Mode too, when `HWREna` bit 2 is set — the value
the step started with (MD00086 Vol II-A Rev 6.06, RDHWR, Table 5.4, p.332: "CC ... provides read
access to the coprocessor 0 Count Register"). -/
theorem rdhwr_cc_reads_count (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rdhwr rt 2#32))
    (hpb : s.pendingBranch = none)
    (hacc : cp0Usable s = true ∨ (s.cp0HWREna >>> 2#32) &&& 1#32 ≠ 0#32)
    (hrt : regIdxSpec rt ≠ 0) (hsize : s.regs.size = 32) (hexec : executesInstr s = true) :
    readReg (step s) (regIdxSpec rt) = s.cp0Count := by
  rw [rdhwr_allowed s w rt 2#32 s.cp0Count hfetch hdecode hpb (hwrValue_cc s) hacc hexec]
  exact writeReg_reads_back s (regIdxSpec rt) s.cp0Count hrt hsize

/-- **`mtc0 $rt, $7` (`HWREna`) keeps bits 3..0 only**: the bits of the registers the model
implements; "If RDHWR register ‘n’ is not implemented, bit ‘n’ of this field returns a zero and is
ignored on a write" (MD00090 Vol III Rev 6.02 Table 9.39, p.175). -/
theorem hwrena_write_masked (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 7#32 0#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    (step s).cp0HWREna = readReg s (regIdxSpec rt) &&& 0x0000000F#32 := by
  rw [mtc0_spec_raw s w rt 7#32 0#32 hfetch hdecode hpb hcp0 hexec]
  rfl

/-- **The Reset exception clears `HWREna`** ("HWREna ← 0", MD00090 Vol III Rev 6.02 §6.2.5, p.89)
and leaves `Count`, `Compare` and `Cause.TI` (reset state "Undefined", Tables 9.44, 9.46, 9.52,
p.183, 187, 209) unchanged. -/
theorem resetException_timer (s : State) :
    (resetException s).cp0HWREna = 0#32 ∧ (resetException s).cp0Count = s.cp0Count ∧
      (resetException s).cp0Compare = s.cp0Compare ∧
      (resetException s).cp0TimerInt = s.cp0TimerInt :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Satisfiable examples -/

-- `step_count_advances`: an `addu` from the hosted start state moves `Count` from 0 to 1.
#guard (stepIn (prog1Spec (.addu 8#32 9#32 10#32)) (initialState textBase)).cp0Count == 1#32
-- `step_count_stopped`: with `Cause.DC = 1` it stays.
#guard (stepIn (prog1Spec (.addu 8#32 9#32 10#32))
          { initialState textBase with cp0Cause := causeDcMask }).cp0Count == 0#32
-- An exception step counts too (`break`).
#guard (stepIn (prog1Spec (.break 0#32)) { initialState textBase with cp0Count := 41#32 }).cp0Count
  == 42#32
-- `step_timer_match_sets_ti`: Count reaching Compare sets TI, and `mfc0 Cause` then shows TI and IP7.
#guard (let s := stepIn (prog1Spec (.sll 0#32 0#32 0#32))
          { initialState textBase with cp0Count := 99#32, cp0Compare := 100#32 }
        s.cp0TimerInt && causeValue s == 0x40008000#32)
-- `mtc0_compare_clears_ti`: writing Compare (with a value Count does not reach) clears TI.
#guard (let s := stepIn (prog1Spec (.mtc0 8#32 11#32 0#32))
          (setRegsSpec { initialState textBase with cp0TimerInt := true } [(8, 1000#32)])
        !s.cp0TimerInt && s.cp0Compare == 1000#32)
-- `rdhwr_allowed`: Kernel Mode reads CC = Count (the value before the step's tick).
#guard (let s := stepIn (prog1Spec (.rdhwr 8#32 2#32)) { initialState textBase with cp0Count := 77#32 }
        readReg s 8 == 77#32 && s.cp0Count == 78#32)
-- `rdhwr_reserved_not_enabled`: User Mode, HWREna = 0b0101: register 1 is Reserved Instruction.
#guard (let s := stepIn (prog1Spec (.rdhwr 8#32 1#32))
          { initialState textBase with cp0Status := statusUmMask, cp0HWREna := 5#32 }
        causeExcCode s == excCodeRI)
-- … and register 2 (bit 2 set) is readable there.
#guard (let s := stepIn (prog1Spec (.rdhwr 8#32 2#32))
          { initialState textBase with cp0Status := statusUmMask, cp0HWREna := 5#32, cp0Count := 5#32 }
        readReg s 8 == 5#32 && s.pc == textBase + 4#32)
-- `rdhwr_reserved_unimplemented`: register 29 (ULR) in Kernel Mode.
#guard causeExcCode (stepIn (prog1Spec (.rdhwr 8#32 29#32)) (initialState textBase)) == excCodeRI
