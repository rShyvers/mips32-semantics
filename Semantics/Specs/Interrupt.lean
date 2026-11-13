import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures
import Semantics.Specs.Exception
import Semantics.Specs.Cp0
import Semantics.Specs.Timer

/-!
# Interrupt — the Interrupt exception, standby (`wait`), `IntCtl` and `SRSCtl`

Constructors: none of its own (`wait`, `rdpgpr`, `wrpgpr` are in `Cp0.lean`).

Manual pages: MD00090 Vol III Rev 6.02 §6.1 (p.71-72: when an interrupt is taken), §6.1.1.1
(p.73: interrupt compatibility mode, Table 6.2), §6.1.2.1 (p.82: hazards, Table 6.5), §6.2.1
(p.83-84: Table 6.6 priority, Table 6.7), §6.2.2 (p.84-86: Tables 6.9, 6.10 vectors), §6.2.3
(p.86-88: general exception processing), §6.2.26 (p.102: Interrupt exception), §7 (p.103-104: GPR
shadow sets), §9.33 IntCtl (p.199-201), §9.34 SRSCtl (p.203-205), §9.35 SRSMap (p.207), §9.36 Cause
(p.209-212); MD00086 Vol II-A Rev 6.06, WAIT (p.442-443).

`step s = timerTick (stepCore s)` and `stepCore` first checks for an interrupt (`interruptTaken`),
then for standby, and only then fetches (`execute`). What this file proves:

* **When an interrupt is taken** (`step_interrupt`, `interruptTaken_iff`): exactly when `Status.IE
  = 1`, `EXL = ERL = 0` and some `Cause.IPi` is set with `Status.IMi = 1`; never with `IE = 0`,
  `EXL = 1` or `ERL = 1` (`no_interrupt_ie0`, `no_interrupt_exl`, `no_interrupt_erl`), never with
  every request masked (`no_interrupt_masked`). The instruction at `pc` is then not executed: the
  step is the exception entry (and the timer).
* **The entry** (`takeInterrupt_not_in_delay_slot`, `takeInterrupt_in_delay_slot`): `ExcCode = 0`,
  `EPC` = the address of the instruction that was not executed, or of the branch before it with
  `Cause.BD = 1`, `EXL ← 1`, the pending branch abandoned, no GPR changed.
* **The vector** (`interruptVector_iv0`, `interruptVector_iv1_bev0`, `interruptVector_iv1_bev1`):
  offset `0x180` with `Cause.IV = 0`, `0x200` with `Cause.IV = 1`.
* **The sources**: a software request written with `mtc0` to `Cause` (`mtc0_cause_requests_
  software_interrupt`), the timer (`timer_requests_interrupt`), a hardware line
  (`hwInt_requests_interrupt`); the lines are inputs `step` never writes (`step_hwInt`).
* **Standby** (`step_standby_stays`, `step_standby_restarts`, `step_standby_interrupt`).
* **`IntCtl` and `SRSCtl`**: their values (`intCtlValue_fields`, `srsCtlValue_fields`), the
  `mfc0` reads in every state and the ignored writes (`mfc0_intctl_spec`, `mfc0_srsctl_spec`,
  `mtc0_intctl_ignored`, `mtc0_srsctl_ignored`).

## Theorems in this file (29)

  `stepCore_interrupt` `step_interrupt` `interruptTaken_iff` `no_interrupt_ie0`
  `no_interrupt_exl` `no_interrupt_erl` `no_interrupt_masked` `executesInstr_iff`
  `takeInterrupt_not_in_delay_slot` `takeInterrupt_in_delay_slot` `takeInterrupt_keeps`
  `interruptVector_iv0` `interruptVector_iv1_bev0` `interruptVector_iv1_bev1`
  `ne_zero_of_getLsbD` `mtc0_cause_requests_software_interrupt` `timer_requests_interrupt`
  `hwInt_requests_interrupt` `execInstr_hwInt` `step_hwInt` `step_standby_stays` `step_standby_restarts`
  `step_standby_interrupt` `intCtlValue_fields` `srsCtlValue_fields` `mfc0_intctl_spec`
  `mfc0_srsctl_spec` `mtc0_intctl_ignored` `mtc0_srsctl_ignored`
-/

set_option maxRecDepth 4000

/-! ## When an interrupt is taken -/

/-- `stepCore` takes the Interrupt exception when one is taken. -/
theorem stepCore_interrupt (s : State) (h : interruptTaken s = true) :
    stepCore s = takeInterrupt s := by
  unfold stepCore; rw [h]; rfl

/-- **An interrupt preempts the instruction at `pc`**: if an interrupt is requested and enabled,
the step is the Interrupt exception followed by the timer; the instruction at `pc` is not fetched
or executed (an interrupt is "the highest priority relative to the next instruction", MD00090
Vol III Rev 6.02 Table 6.7, p.84, above every fetch and instruction exception in Table 6.6, p.83). -/
theorem step_interrupt (s : State) (h : interruptTaken s = true) :
    step s = timerTick (takeInterrupt s) := by
  show timerTick (stepCore s) = _
  rw [stepCore_interrupt s h]

/-- **The condition** (MD00090 Vol III Rev 6.02 §6.1, p.72: a request is made, "The IE bit in the
Status register is a one", "The EXL and ERL bits in the Status register are both zero"; Table 6.2,
p.73: request `i` is "CauseIPi and StatusIMi"). -/
theorem interruptTaken_iff (s : State) :
    interruptTaken s = true ↔
      s.cp0Status &&& statusIeMask ≠ 0#32 ∧ s.cp0Status &&& statusExlMask = 0#32 ∧
      s.cp0Status &&& statusErlMask = 0#32 ∧
      causeValue s &&& s.cp0Status &&& statusImMask ≠ 0#32 := by
  unfold interruptTaken interruptsEnabled interruptRequests
  simp [Bool.and_eq_true, and_assoc]

/-- **No interrupt with `Status.IE = 0`.** -/
theorem no_interrupt_ie0 (s : State) (h : s.cp0Status &&& statusIeMask = 0#32) :
    interruptTaken s = false := by
  unfold interruptTaken interruptsEnabled; simp [h]

/-- **No interrupt with `Status.EXL = 1`** (inside an exception handler). -/
theorem no_interrupt_exl (s : State) (h : s.cp0Status &&& statusExlMask ≠ 0#32) :
    interruptTaken s = false := by
  unfold interruptTaken interruptsEnabled; simp [h]

/-- **No interrupt with `Status.ERL = 1`** (after Reset, until software clears it). -/
theorem no_interrupt_erl (s : State) (h : s.cp0Status &&& statusErlMask ≠ 0#32) :
    interruptTaken s = false := by
  unfold interruptTaken interruptsEnabled; simp [h]

/-- **No interrupt when every request is masked** (`Cause.IP & Status.IM = 0`). -/
theorem no_interrupt_masked (s : State) (h : interruptRequests s = 0#32) :
    interruptTaken s = false := by
  unfold interruptTaken; simp [h]

/-- **The hypothesis of every per-instruction theorem**, unfolded: no interrupt is taken and the
processor is not in standby. -/
theorem executesInstr_iff (s : State) :
    executesInstr s = true ↔ interruptTaken s = false ∧ s.standby = false := by
  unfold executesInstr; cases interruptTaken s <;> cases s.standby <;> simp

/-! ## The entry -/

/-- **Interrupt entry, not in a delay slot** (MD00090 Vol III Rev 6.02 §6.2.3, p.86-88; §6.2.26,
p.102): `EPC ←` the address of the instruction that was not executed, `Cause.BD ← 0`, `ExcCode ←
Int` (0), `CE ← 0`, `Status.EXL ← 1`, `PC ←` the interrupt vector, and the processor leaves standby.
`EXL = 0` holds whenever an interrupt is taken. -/
theorem takeInterrupt_not_in_delay_slot (s : State) (hexl : s.cp0Status &&& statusExlMask = 0#32)
    (hpb : s.pendingBranch = none) :
    (takeInterrupt s).cp0Epc = s.pc ∧
      (takeInterrupt s).cp0Cause =
        (s.cp0Cause &&& ~~~causeBdMask) &&& ~~~(causeExcCodeMask ||| causeCeMask) ∧
      causeExcCode (takeInterrupt s) = excCodeInt ∧
      (takeInterrupt s).cp0Status = s.cp0Status ||| statusExlMask ∧
      (takeInterrupt s).pc = interruptVector s ∧
      (takeInterrupt s).standby = false := by
  have h := exceptionEntry_exl0_not_in_delay_slot s excCodeInt 0#32 hexl hpb
  refine ⟨h.1, ?_, ?_, rfl, rfl, rfl⟩
  · show (exceptionEntry s excCodeInt 0#32).cp0Cause = _
    rw [h.2]; simp [excCodeInt]
  · show causeExcCode (exceptionEntry s excCodeInt 0#32) = _
    rw [exceptionEntry_excCode]; rfl

/-- **Interrupt entry in a branch delay slot** (`pendingBranch = some t`): `EPC ←` the branch
(`pc - 4`), `Cause.BD ← 1` ("Address of the branch or jump instruction (PC-4)", MD00090 Vol III
Rev 6.02 Table 6.11, p.87); the pending branch is abandoned, so `eret` re-executes the branch. -/
theorem takeInterrupt_in_delay_slot (s : State) (t : W32)
    (hexl : s.cp0Status &&& statusExlMask = 0#32) (hpb : s.pendingBranch = some t) :
    (takeInterrupt s).cp0Epc = s.pc - 4#32 ∧
      (takeInterrupt s).cp0Cause =
        (s.cp0Cause ||| causeBdMask) &&& ~~~(causeExcCodeMask ||| causeCeMask) ∧
      causeExcCode (takeInterrupt s) = excCodeInt ∧
      (takeInterrupt s).pendingBranch = none ∧
      (takeInterrupt s).pc = interruptVector s := by
  have h := exceptionEntry_exl0_in_delay_slot s excCodeInt 0#32 t hexl hpb
  refine ⟨h.1, ?_, ?_, rfl, rfl⟩
  · show (exceptionEntry s excCodeInt 0#32).cp0Cause = _
    rw [h.2]; simp [excCodeInt]
  · show causeExcCode (exceptionEntry s excCodeInt 0#32) = _
    rw [exceptionEntry_excCode]; rfl

/-- **Interrupt entry touches nothing else**: no GPR, `HI`/`LO`, memory, FPR, `FCSR`, `BadVAddr`,
`ErrorEPC`, timer state or hardware line changes; `LLbit` is cleared. -/
theorem takeInterrupt_keeps (s : State) :
    (takeInterrupt s).regs = s.regs ∧ (takeInterrupt s).hi = s.hi ∧ (takeInterrupt s).lo = s.lo ∧
      (takeInterrupt s).physMem = s.physMem ∧ (takeInterrupt s).fpRegs = s.fpRegs ∧
      (takeInterrupt s).fcsr = s.fcsr ∧ (takeInterrupt s).cp0BadVAddr = s.cp0BadVAddr ∧
      (takeInterrupt s).cp0ErrorEpc = s.cp0ErrorEpc ∧ (takeInterrupt s).cp0Count = s.cp0Count ∧
      (takeInterrupt s).cp0Compare = s.cp0Compare ∧
      (takeInterrupt s).cp0TimerInt = s.cp0TimerInt ∧ (takeInterrupt s).hwInt = s.hwInt ∧
      (takeInterrupt s).llBit = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The vector -/

/-- **`Cause.IV = 0`: the general exception vector** (offset `0x180`; MD00090 Vol III Rev 6.02
§6.2.26, p.102: "General exception vector (offset 0x180) if the IV bit in the Cause register is
zero"). -/
theorem interruptVector_iv0 (s : State) (h : s.cp0Cause &&& causeIvMask = 0#32) :
    interruptVector s = exceptionVector s := by
  unfold interruptVector; simp [h]

/-- **`Cause.IV = 1`, `Status.BEV = 0`: `EBase` + `0x200`** ("Interrupt vector (offset 0x200) if the
IV bit in the Cause register is one", §6.2.26, p.102; `IntCtl.VS = 0`, so the vectored-interrupt
offsets of Table 6.4 do not apply, §6.2.3 Operation, p.88). `0x8000_0200` with `EBase` at its reset
value (Table 6.10, p.86). -/
theorem interruptVector_iv1_bev0 (s : State) (h : s.cp0Cause &&& causeIvMask ≠ 0#32)
    (hbev : s.cp0Status &&& statusBevMask = 0#32) :
    interruptVector s = ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32) ||| 0x200#32 := by
  unfold interruptVector; simp [h, hbev]; rfl

/-- **`Cause.IV = 1`, `Status.BEV = 1`: `0xBFC0_0400`** (Table 6.10, p.86: "Interrupt 1 0 1 ...
0xBFC0.0400"; base `0xBFC0_0200`, Table 6.8, p.85, plus `0x200`). -/
theorem interruptVector_iv1_bev1 (s : State) (h : s.cp0Cause &&& causeIvMask ≠ 0#32)
    (hbev : s.cp0Status &&& statusBevMask ≠ 0#32) :
    interruptVector s = 0xBFC00400#32 := by
  unfold interruptVector; simp [h, hbev]; rfl

/-! ## The sources of requests -/

/-- A word with some bit set is not zero (proof device). -/
theorem ne_zero_of_getLsbD (x : W32) (i : Nat) (h : x.getLsbD i = true) : x ≠ 0#32 := by
  intro hx; rw [hx] at h; simp at h

/-- **A software interrupt requested with `mtc0`** (MD00090 Vol III Rev 6.02 Table 9.52, p.212:
`IP1..IP0` "Controls the request for software interrupts", R/W; Table 6.2, p.73: SW0/SW1 are
"CauseIP0 and StatusIM0" / "CauseIP1 and StatusIM1"): if `mtc0 $rt, $13` writes a 1 into `IP0`
(bit 8) or `IP1` (bit 9) and `Status.IMi` is 1, a request is pending after the step; with `IE = 1`
and `EXL = ERL = 0` the next step takes the interrupt (`step_interrupt`), so its `EPC` is the
instruction after the `mtc0` (the hazard of Table 6.5, p.82, is cleared at once: pin). -/
theorem mtc0_cause_requests_software_interrupt (s : State) (w rt : W32) (i : Nat)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 13#32 0#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true)
    (hi : i = 8 ∨ i = 9) (hip : (readReg s (regIdxSpec rt)).getLsbD i = true)
    (him : s.cp0Status.getLsbD i = true) (hen : interruptsEnabled s = true) :
    interruptRequests (step s) ≠ 0#32 ∧ interruptTaken (step s) = true := by
  rw [mtc0_spec_raw s w rt 13#32 0#32 hfetch hdecode hpb hcp0 hexec]
  have hreq : interruptRequests (timerTick { s with
      cp0Cause := (s.cp0Cause &&& ~~~causeWriteMask) ||| (readReg s (regIdxSpec rt) &&& causeWriteMask)
      pc := s.pc + 4#32 }) ≠ 0#32 := by
    apply ne_zero_of_getLsbD _ i
    unfold interruptRequests causeValue hwIntBits
    rcases hi with rfl | rfl <;> simp [hip, him, causeWriteMask, statusImMask]
  refine ⟨hreq, ?_⟩
  unfold interruptTaken
  have hen' : interruptsEnabled (timerTick { s with
      cp0Cause := (s.cp0Cause &&& ~~~causeWriteMask) ||| (readReg s (regIdxSpec rt) &&& causeWriteMask)
      pc := s.pc + 4#32 }) = true := hen
  simp [hen', hreq]

/-- **The timer requests an interrupt on `IP7`** (MD00090 Vol III Rev 6.02 §9.30, p.187: "When the
value of the Count register equals the value of the Compare register, an interrupt request is
made"; Table 6.2, p.73: HW5, "CauseIP7 and StatusIM7"; `IntCtl.IPTI = 7`): with `Cause.TI` set and
`Status.IM7 = 1` a request is pending, so with `IE = 1`, `EXL = ERL = 0` the step takes the
interrupt. -/
theorem timer_requests_interrupt (s : State) (hti : s.cp0TimerInt = true)
    (him : s.cp0Status.getLsbD 15 = true) :
    interruptRequests s ≠ 0#32 := by
  apply ne_zero_of_getLsbD _ 15
  unfold interruptRequests causeValue
  simp [hti, him, causeTiMask, causeIp7Mask, statusImMask]

/-- **A hardware line requests an interrupt on its `IP` bit** (Table 9.52, p.211: `IP(i+2)` is
"Hardware interrupt i"; Table 6.2, p.73): with line `HWi` asserted and `Status.IM(i+2) = 1` a
request is pending. (The environment of this model never asserts a line, `Semantics/Env.lean`.) -/
theorem hwInt_requests_interrupt (s : State) (i : Nat) (hi : i < 6)
    (hline : s.hwInt.getLsbD i = true) (him : s.cp0Status.getLsbD (i + 10) = true) :
    interruptRequests s ≠ 0#32 := by
  apply ne_zero_of_getLsbD _ (i + 10)
  unfold interruptRequests causeValue hwIntBits
  have h1 : (s.hwInt.setWidth 32 <<< 10).getLsbD (i + 10) = true := by
    simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hline]; omega
  have h2 : (statusImMask).getLsbD (i + 10) = true := by
    unfold statusImMask
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp [h1, h2, him]

/-- No instruction writes the hardware interrupt lines (`execInstr_timerKept` for every instruction
but `mtc0` to `Count`/`Compare`/`Cause`; those `mtc0` arms by computation). -/
theorem execInstr_hwInt (s : State) (instr : Instruction) : (execInstr s instr).hwInt = s.hwInt := by
  cases hw : writesTimer instr
  · exact (execInstr_timerKept s instr hw).2.2.2.2
  · cases instr <;> simp only [writesTimer, reduceCtorEq] at hw
    unfold execInstr
    split
    · rfl
    split
    · rfl
    split
    · rfl
    unfold execBody
    dsimp only
    split <;> first | rfl | (unfold mkNext advance; split <;> rfl)

/-- **The hardware interrupt lines are inputs**: no step changes them (MD00090 Vol III Rev 6.02
Table 9.52, p.211: `IP7..IP2` are Read-only, "Hardware interrupt 5 ... 0"). Whatever drives them is
the system around the processor (`Semantics/Env.lean`). -/
theorem step_hwInt (s : State) : (step s).hwInt = s.hwInt := by
  show (stepCore s).hwInt = s.hwInt
  unfold stepCore
  split
  · rfl
  split
  · unfold standbyStep; split <;> rfl
  unfold execute
  split
  · rfl
  split
  · split
    · rfl
    split
    · rfl
    split <;> rfl
  · exact execInstr_hwInt _ _

/-! ## Standby (`wait`) -/

/-- **In standby with no request, the processor stays stopped**: only the timer advances (MD00086
Vol II-A Rev 6.06, WAIT, p.442: "stalling the pipeline ... The pipeline is restarted when an
external event, such as an interrupt or external request occurs"). -/
theorem step_standby_stays (s : State) (hsb : s.standby = true)
    (hreq : interruptRequests s = 0#32) :
    step s = timerTick s := by
  have hi : interruptTaken s = false := no_interrupt_masked s hreq
  show timerTick (stepCore s) = _
  unfold stepCore standbyStep
  rw [hi, hsb, hreq]
  rfl

/-- **A request that is not enabled restarts the pipeline** (pin: WAIT, p.442, "It is
implementation-dependent whether the pipeline restarts when a non-enabled interrupt is requested";
the model restarts, as Release 6 requires, p.443): the step leaves standby, and the next step
executes the instruction after the `wait` (`pc` already holds it). -/
theorem step_standby_restarts (s : State) (hsb : s.standby = true)
    (hreq : interruptRequests s ≠ 0#32) (hen : interruptsEnabled s = false) :
    step s = timerTick { s with standby := false } := by
  have hi : interruptTaken s = false := by unfold interruptTaken; simp [hen]
  show timerTick (stepCore s) = _
  unfold stepCore standbyStep
  rw [hi, hsb]
  simp [hreq]

/-- **An enabled interrupt in standby is taken with `EPC` = the instruction after the `wait`**
("If the pipeline restarts as the result of an enabled interrupt, that interrupt is taken between
the WAIT instruction and the following instruction (EPC for the interrupt points at the instruction
following the WAIT instruction)", MD00086 Vol II-A Rev 6.06, WAIT, p.442). After `wait`,
`pc` is that instruction (`wait_spec_raw`) and no branch is pending. -/
theorem step_standby_interrupt (s : State) (_hsb : s.standby = true) (h : interruptTaken s = true)
    (hpb : s.pendingBranch = none) :
    step s = timerTick (takeInterrupt s) ∧ (step s).cp0Epc = s.pc ∧ (step s).standby = false := by
  have hexl : s.cp0Status &&& statusExlMask = 0#32 := ((interruptTaken_iff s).mp h).2.1
  have he := takeInterrupt_not_in_delay_slot s hexl hpb
  refine ⟨step_interrupt s h, ?_, ?_⟩
  · rw [step_interrupt s h]; exact he.1
  · rw [step_interrupt s h]; exact he.2.2.2.2.2

/-! ## `IntCtl` and `SRSCtl` -/

/-- **`IntCtl` reads `IPTI = 7`, every other field 0** (MD00090 Vol III Rev 6.02 Table 9.48,
p.199-201): `IPTI` (31..29) = 7; `IPPCI` (28..26) = 0 ("If performance counters are not implemented
(Config1PC = 0), this field returns zero on read"); `IPFDC` (25..23) = 0; `VS` (9..5) = 0 ("If
neither EIC interrupt mode nor VI mode are implemented ... this field is ignored on write and reads
as zero"). -/
theorem intCtlValue_fields :
    intCtlValue >>> 29 = 7#32 ∧ (intCtlValue >>> 26) &&& 7#32 = 0#32 ∧
      (intCtlValue >>> 23) &&& 7#32 = 0#32 ∧ (intCtlValue >>> 5) &&& 31#32 = 0#32 := by
  decide

/-- **`SRSCtl` reads 0**: `HSS` (29..26) = 0, only the normal GPRs ("A value of zero in this field
indicates that only the normal GPRs are implemented", MD00090 Vol III Rev 6.02 Table 9.49, p.203),
and `ESS` (15..12), `PSS` (9..6), `CSS` (3..0) = 0 in every state, so the shadow-set update of
exception entry ("SRSCtlPSS ← SRSCtlCSS; SRSCtlCSS ← NewShadowSet", guarded by "SRSCtlHSS ≠ 0",
§6.2.3, p.88) and of `eret` ("SRSCtlCSS ← SRSCtlPSS", MD00086 Vol II-A Rev 6.06, ERET, p.177) never
applies, and would change nothing if it did. -/
theorem srsCtlValue_fields :
    (srsCtlValue >>> 26) &&& 15#32 = 0#32 ∧ (srsCtlValue >>> 12) &&& 15#32 = 0#32 ∧
      (srsCtlValue >>> 6) &&& 15#32 = 0#32 ∧ srsCtlValue &&& 15#32 = 0#32 := by
  decide

/-- **`mfc0 $rt, $12, 1` reads `IntCtl` = `0xE000_0000` in every state.** -/
theorem mfc0_intctl_spec (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc0 rt 12#32 1#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick
      { (writeReg s (regIdxSpec rt) 0xE0000000#32) with
          pc := (writeReg s (regIdxSpec rt) 0xE0000000#32).pc + 4#32 } := by
  rw [mfc0_spec_raw s w rt 12#32 1#32 hfetch hdecode hpb hcp0 hexec]; rfl

/-- **`mfc0 $rt, $12, 2` reads `SRSCtl` = 0 in every state** (`HSS = ESS = PSS = CSS = 0`): no
exception entry or `eret` ever makes `CSS` or `PSS` nonzero. -/
theorem mfc0_srsctl_spec (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc0 rt 12#32 2#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick
      { (writeReg s (regIdxSpec rt) 0#32) with pc := (writeReg s (regIdxSpec rt) 0#32).pc + 4#32 } := by
  rw [mfc0_spec_raw s w rt 12#32 2#32 hfetch hdecode hpb hcp0 hexec]; rfl

/-- **A write to `IntCtl` changes nothing** (no writable field: `VS` "is ignored on write" without
VI/EIC, Table 9.48, p.201). -/
theorem mtc0_intctl_ignored (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 12#32 1#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick { s with pc := s.pc + 4#32 } := by
  rw [mtc0_spec_raw s w rt 12#32 1#32 hfetch hdecode hpb hcp0 hexec]; rfl

/-- **A write to `SRSCtl` changes nothing** (pin: with `HSS = 0` writing anything but 0 to `ESS` or
`PSS` is UNDEFINED, Table 9.49, p.203-204, and 0 is what they hold). -/
theorem mtc0_srsctl_ignored (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt 12#32 2#32))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hexec : executesInstr s = true) :
    step s = timerTick { s with pc := s.pc + 4#32 } := by
  rw [mtc0_spec_raw s w rt 12#32 2#32 hfetch hdecode hpb hcp0 hexec]; rfl
