import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures
import Semantics.Specs.DelaySlot

/-!
# Cp0 — coprocessor 0: `mfc0`/`mtc0`, `di`/`ei`, `eret`, `wait`

Constructors: `mfc0` `mtc0` `di` `ei` `eret` `wait`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  MFC0 p.266; MTC0 p.290-291; DI p.164; EI p.176; ERET p.177-178; WAIT p.442-443.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Coprocessor 0 / traps and exceptions (real MIPS32 ISA)".

Every one of these instructions needs coprocessor 0: outside Kernel Mode with `Status.CU0 = 0`
it raises Coprocessor Unusable with `Cause.CE = 0` and does nothing else
(`cp0_instruction_user_mode_unusable`, one theorem for all six; MD00090 Vol III Rev 6.02
§6.2.22, p.100). The per-instruction `_spec_raw` theorems state the other case: they assume
`hcp0 : cp0Usable s = true` (Kernel Mode, or `Status.CU0 = 1`; §3.5.3, p.23).

## Theorems in this file (13)

  `mfc0_spec_raw` `mtc0_spec_raw` `causeWriteMask_eq` `statusWriteMask_eq` `di_spec_raw`
  `ei_spec_raw` `eret_spec_raw` `eret_clears_llBit` `eret_in_delay_slot_reserved_instruction`
  `wait_spec_raw` `wait_preserves_state` `cp0_instruction_user_mode_unusable`
  `usesCop1_of_usesCop0`
-/

set_option maxRecDepth 4000

/-! ## `mfc0`/`mtc0`, `di`/`ei`, `eret`, `wait`

(`pref` is in `Memory.lean`; the coprocessor-1 specifications are in the `Fpu*.lean` files.) -/

/-- **`mfc0` reads a modeled CP0 register `(rd, sel)` into GPR `$rt`**:
`(7,0)` HWREna, `(8,0)` BadVAddr, `(9,0)` Count, `(11,0)` Compare, `(12,0)` Status,
`(13,0)` Cause, `(14,0)` EPC, `(15,0)` PRId, `(15,1)` EBase, `(16,0)` Config, `(16,1)` Config1,
`(30,0)` ErrorEPC. `Cause` reads the stored bits plus the timer request: `TI` (bit 30) and, merged
into it (`IntCtl.IPTI = 7` pin), `IP7` (bit 15) while a timer interrupt is pending (MD00090 Vol III
Rev 6.02 Table 9.52, p.209, 211; Table 6.2, p.73). The read happens before the step's timer tick, so
`Count` reads the value the step started with.
`decode` produces `mfc0` only for these; for any other pair (reachable only
through a hand-built `Instruction`) the step raises Reserved Instruction,
which is also what the undecodable word does. Coprocessor 0 must be usable
(`hcp0`: Kernel Mode or `Status.CU0 = 1`); otherwise see
`cp0_instruction_user_mode_unusable`. -/
theorem mfc0_spec_raw (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc0 rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) :
    step s = timerTick (
      let read (v : W32) : State :=
        { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }
      match rd.toNat, sel.toNat with
      | 7, 0 => read s.cp0HWREna
      | 8, 0 => read s.cp0BadVAddr
      | 9, 0 => read s.cp0Count
      | 11, 0 => read s.cp0Compare
      | 12, 0 => read s.cp0Status
      | 13, 0 => read (s.cp0Cause ||| (if s.cp0TimerInt then causeTiMask ||| causeIp7Mask else 0#32))
      | 14, 0 => read s.cp0Epc
      | 15, 0 => read 0x00010000#32
      | 15, 1 => read ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32)
      | 16, 0 => read (0x80008580#32 ||| (s.cp0ConfigK23.setWidth 32 <<< 28) |||
          (s.cp0ConfigKU.setWidth 32 <<< 25) ||| s.cp0ConfigK0.setWidth 32)
      | 16, 1 => read 0x00000001#32
      | 30, 0 => read s.cp0ErrorEpc
      | _, _ => takeException s excCodeRI) := by
  cp0_step_spec

/-- **`mtc0` writes GPR `$rt` into a modeled CP0 register, through that
register's write mask.** `Status` (12,0) keeps only `statusWriteMask` (IE,
EXL, ERL, UM, IM7..0, BEV, CU0, CU1; every other bit reads as zero). `Cause` (13,0)
changes only `causeWriteMask` (DC, IV, IP1..0) and keeps `BD`, `CE`,
`ExcCode` and everything else. `EPC` (14,0) and `ErrorEPC` (30,0) are fully
writable, and so is `Count` (9,0) (MD00090 Vol III Rev 6.02 §9.27, p.183). A write to `Compare`
(11,0) stores the value and clears the timer interrupt (`Cause.TI`; §9.30, p.187). `HWREna` (7,0)
keeps bits 3..0 (`hwrenaWriteMask`; Table 9.39, p.175). `EBase` (15,1) takes bits 29..12 of the
written value under the fixed bits 31..30 = `10`. `Config` (16,0) takes only `K0` (bits 2..0, Read/Write: MD00090 Vol III Rev 6.02 Table 9.64, p.235);
`BadVAddr` (8,0), `PRId` (15,0) and `Config1` (16,1) are read-only: the write is ignored. Any other pair
raises Reserved Instruction, as for `mfc0_spec_raw`. Coprocessor 0 must be
usable (`hcp0`). -/
theorem mtc0_spec_raw (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt rd sel))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) :
    step s = timerTick (
      match rd.toNat, sel.toNat with
      | 7, 0 =>
        { s with cp0HWREna := readReg s (regIdxSpec rt) &&& hwrenaWriteMask, pc := s.pc + 4#32 }
      | 8, 0 => { s with pc := s.pc + 4#32 }
      | 9, 0 => { s with cp0Count := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 11, 0 =>
        { s with cp0Compare := readReg s (regIdxSpec rt), cp0TimerInt := false, pc := s.pc + 4#32 }
      | 12, 0 =>
        { s with cp0Status := readReg s (regIdxSpec rt) &&& statusWriteMask, pc := s.pc + 4#32 }
      | 13, 0 =>
        { s with
              cp0Cause := (s.cp0Cause &&& ~~~causeWriteMask) |||
                (readReg s (regIdxSpec rt) &&& causeWriteMask)
              pc := s.pc + 4#32 }
      | 14, 0 => { s with cp0Epc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 15, 0 => { s with pc := s.pc + 4#32 }
      | 15, 1 =>
        { s with
              cp0EBase := (readReg s (regIdxSpec rt) &&& 0x3ffff000#32) ||| 0x80000000#32
              pc := s.pc + 4#32 }
      | 16, 0 =>
        { s with
              cp0ConfigK0 := (readReg s (regIdxSpec rt)).setWidth 3
              cp0ConfigK23 := (readReg s (regIdxSpec rt) >>> 28).setWidth 3
              cp0ConfigKU := (readReg s (regIdxSpec rt) >>> 25).setWidth 3
              pc := s.pc + 4#32 }
      | 16, 1 => { s with pc := s.pc + 4#32 }
      | 30, 0 =>
        { s with cp0ErrorEpc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | _, _ => takeException s excCodeRI) := by
  cp0_step_spec

/-- The write mask of `Cause` is `DC` (27), `IV` (23), `IP1..IP0` (9..8)
(MD00090 Vol III Rev 6.02 §9.36, p.209-210). -/
theorem causeWriteMask_eq : causeWriteMask = 0x08800300#32 := rfl

/-- The write mask of `Status` is `CU1` (29), `CU0` (28), `BEV` (22), `IM7..IM0`
(15..8), `UM` (4), `ERL` (2), `EXL` (1), `IE` (0) (MD00090 Vol III Rev 6.02
§9.32, Table 9.47, p.190-196: the R/W fields of an implementation without
Supervisor Mode, coprocessors 2/3, `RP`, `FR`, `RE`, `MX`, `TS`, `SR`, `NMI`). -/
theorem statusWriteMask_eq : statusWriteMask = 0x3040ff17#32 := rfl

/-- **`di`: `$rt ← Status`, then `Status.IE ← 0`** (MD00086 Vol II-A
Rev 6.06, DI, p.164). The value written to `$rt` is the `Status` before the
change; no other `Status` bit changes. -/
theorem di_spec_raw (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.di rt))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) :
    step s = timerTick (
      { (writeReg { s with cp0Status := s.cp0Status &&& ~~~statusIeMask } (regIdxSpec rt)
            s.cp0Status) with
          pc := (writeReg { s with cp0Status := s.cp0Status &&& ~~~statusIeMask } (regIdxSpec rt)
            s.cp0Status).pc + 4#32 }) := by
  cp0_step_spec

/-- **`ei`: `$rt ← Status`, then `Status.IE ← 1`** (MD00086 Vol II-A
Rev 6.06, EI, p.176). -/
theorem ei_spec_raw (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ei rt))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) :
    step s = timerTick (
      { (writeReg { s with cp0Status := s.cp0Status ||| statusIeMask } (regIdxSpec rt)
            s.cp0Status) with
          pc := (writeReg { s with cp0Status := s.cp0Status ||| statusIeMask } (regIdxSpec rt)
            s.cp0Status).pc + 4#32 }) := by
  cp0_step_spec

/-- **`eret`** (MD00086 "ERET"), executed outside a delay slot:
`if Status.ERL = 1 then PC ← ErrorEPC, ERL ← 0 else PC ← EPC, EXL ← 0`,
and **always `LLbit ← 0`**. It has no delay slot of its own: `pc` is set in
this very step. -/
theorem eret_spec_raw (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) :
    step s = timerTick (
      if s.cp0Status &&& statusErlMask != 0#32 then
        { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask, llBit := false }
      else
        { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask, llBit := false }) := by
  cp0_step_spec

/-- **`eret` clears `LLbit`**, whichever return address it uses — so an
`sc` after an exception return fails (see `sc_spec_raw`). -/
theorem eret_clears_llBit (s s' : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) (hstep : step s = s') :
    s'.llBit = false := by
  rw [← hstep, eret_spec_raw s w hfetch hdecode hpb hcp0, timerTick_llBit]
  split <;> rfl

/-- **`eret` in a branch delay slot raises Reserved Instruction**, like a
branch or jump there (pin): "Pre-Release 6: The operation of the processor is
UNDEFINED if an ERET is executed in the delay slot of a branch or jump
instruction" (MD00086 Vol II-A Rev 6.06, ERET, p.177); Release 6 requires
Reserved Instruction (same page). See `branch_in_delay_slot_reserved_instruction`. -/
theorem eret_in_delay_slot_reserved_instruction (s : State) (w t : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = some t) :
    step s = timerTick (takeException s excCodeRI) :=
  branch_in_delay_slot_reserved_instruction s w .eret hfetch hdecode (by rw [hpb]; rfl) rfl

/-- **`wait` continues with the next instruction** (pin): the manual makes the low-power operation
implementation-dependent and says that when the pipeline restarts "execution continues with the
instruction following the WAIT instruction" (MD00086 Vol II-A Rev 6.06, WAIT, p.442; `PC ← PC + 4`
in the Operation, p.443). The model has no interrupts and treats the restart as immediate, so the
step changes only `pc` (`Step.lean`'s `wait` arm: `mkNext s s`). -/
theorem wait_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.wait code))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) :
    step s = timerTick ({ s with pc := s.pc + 4#32 }) := by
  cp0_step_spec

/-- Corollary of `wait_spec_raw`: every piece of state besides `pc` is
left untouched — the "no-op" claim made precise, not just "produces some
next state". -/
theorem wait_preserves_state (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.wait code))
    (hpb : s.pendingBranch = none) (hcp0 : cp0Usable s = true) :
    ∃ s', step s = s' ∧ s'.regs = s.regs ∧ s'.fpRegs = s.fpRegs ∧
      s'.hi = s.hi ∧ s'.lo = s.lo ∧ s'.physMem = s.physMem ∧
      s'.cp0Status = s.cp0Status ∧ s'.cp0Cause = s.cp0Cause ∧ s'.cp0Epc = s.cp0Epc ∧
      s'.pc = s.pc + 4#32 := by
  refine ⟨_, wait_spec_raw s w code hfetch hdecode hpb hcp0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Coprocessor Unusable outside Kernel Mode -/

/-- A coprocessor-0 instruction does not use coprocessor 1 (the two guards of `execInstr` are
about disjoint instruction sets). -/
theorem usesCop1_of_usesCop0 (instr : Instruction) (h : usesCop0 instr = true) :
    usesCop1 instr = false := by
  cases instr <;> first | rfl | exact absurd h Bool.false_ne_true

/-- **Every coprocessor-0 instruction executed outside Kernel Mode with `Status.CU0 = 0` raises
Coprocessor Unusable with `Cause.CE = 0`, and does nothing else.** The instructions are
`usesCop0`: `mfc0`, `mtc0`, `di`, `ei`, `eret`, `wait` (each page lists "Coprocessor Unusable"
among its exceptions: MD00086 Vol II-A Rev 6.06, MFC0 p.266, MTC0 p.291, DI p.164, EI p.176,
ERET p.178, WAIT p.443). The rule: "A COP0 or Cache instruction was executed while the processor
was running in a mode other than Debug Mode or Kernel Mode, and the CU0 bit in the Status register
was a zero"; `Cause.CE` = "unit number of the coprocessor being referenced" (MD00090 Vol III
Rev 6.02 §6.2.22, p.100). `cp0Usable s = false` is exactly "User Mode and `CU0 = 0`" (`kernelMode`,
§3.2, p.21; §3.5.3, p.23). The hypothesis `hnb` excludes `eret`/`wait` in a delay slot, which is
UNDEFINED and pinned to Reserved Instruction in every mode
(`branch_in_delay_slot_reserved_instruction`). Undecodable COP0 words and CACHE:
`step_reserved_cop0_unusable`. -/
theorem cp0_instruction_user_mode_unusable (s : State) (w : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some instr)
    (huses : usesCop0 instr = true)
    (hnb : isBranchLike instr = false ∨ s.pendingBranch = none)
    (hcu : cp0Usable s = false) :
    step s = timerTick (exceptionEntry s excCodeCpU 0#32) := by
  have h1 : (isBranchLike instr && s.pendingBranch.isSome) = false := by
    rcases hnb with h | h <;> simp [h]
  have h2 : usesCop1 instr = false := usesCop1_of_usesCop0 instr huses
  unfold step execute; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only
  unfold execInstr
  rw [h1, h2, huses, hcu]
  rfl

-- `mfc0` reads back Status/Cause/EPC, selected by `rd`;
-- an out-of-scope `rd` raises Reserved Instruction.
#guard (let s := stepIn (prog1Spec (.mfc0 8#32 12#32 0#32)) { (initialState textBase) with cp0Status := 0x2#32 }
        readReg s 8 == 0x2#32) = true

#guard (let s := stepIn (prog1Spec (.mfc0 8#32 13#32 0#32)) { (initialState textBase) with cp0Cause := 0x34#32 }
        readReg s 8 == 0x34#32) = true

#guard (let s := stepIn (prog1Spec (.mfc0 8#32 14#32 0#32)) { (initialState textBase) with cp0Epc := 0x3000#32 }
        readReg s 8 == 0x3000#32) = true

#guard (let s' := stepIn (prog1Spec (.mfc0 8#32 0#32 0#32)) (initialState textBase)
        causeExcCode s' == excCodeRI && s'.pc == exceptionVectorAddr) = true

-- `mtc0` writes Status/Cause (through its mask)/EPC from a GPR; an
-- out-of-scope `rd` raises Reserved Instruction.
#guard (let s := stepIn (prog1Spec (.mtc0 8#32 12#32 0#32)) (setRegsSpec (initialState textBase) [(8, 0x2#32)])
        s.cp0Status == 0x2#32) = true

#guard (let s := stepIn (prog1Spec (.mtc0 8#32 13#32 0#32)) (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)])
        s.cp0Cause == causeWriteMask) = true

#guard (let s := stepIn (prog1Spec (.mtc0 8#32 14#32 0#32)) (setRegsSpec (initialState textBase) [(8, 0x3000#32)])
        s.cp0Epc == 0x3000#32) = true

#guard (let s' := stepIn (prog1Spec (.mtc0 8#32 0#32 0#32)) (setRegsSpec (initialState textBase) [(8, 1#32)])
        causeExcCode s' == excCodeRI && s'.pc == exceptionVectorAddr) = true

-- `eret` restores `pc` from `cp0Epc` and clears `Status.EXL`.
#guard (let s := stepIn (prog1Spec .eret)
          { (initialState textBase) with cp0Epc := 0x3000#32, cp0Status := statusExlMask }
        s.pc == 0x3000#32 && s.cp0Status == 0#32) = true

-- `eret_clears_llBit`; `Status.ERL = 1` returns to `ErrorEPC` and clears `ERL`.
#guard (let s := stepIn (prog1Spec .eret)
          { (initialState textBase) with cp0Epc := 0x3000#32, cp0Status := statusExlMask, llBit := true }
        s.llBit == false) = true

-- (run from kseg0: with `ERL = 1` kuseg is the identity map and executing from it is UNDEFINED,
-- MD00090 Vol III Rev 6.02 §A.1.2, p.316)
#guard (let s := stepIn (buildProgSpec 0x80001000#32 [.eret])
          { (initialState 0x80001000#32) with
              cp0Epc := 0x3000#32, cp0ErrorEpc := 0x4000#32, cp0Status := statusErlMask ||| statusExlMask }
        s.pc == 0x4000#32 && s.cp0Status == statusExlMask) = true

-- `eret_in_delay_slot_reserved_instruction`: Reserved Instruction taken in the
-- delay slot (`EPC` = the branch at `pc - 4`, `Cause.BD = 1`).
#guard (let s := stepIn (prog1Spec .eret)
          { (initialState textBase) with
            cp0Epc := 0x3000#32, pendingBranch := some 0x99999999#32 }
        causeExcCode s == excCodeRI && s.cp0Epc == textBase - 4#32 &&
          s.cp0Cause &&& causeBdMask == causeBdMask && s.pc == exceptionVectorAddr) = true

-- `wait` falls through to `pc + 4`, touching no other state.
#guard (let s := stepIn (prog1Spec (.wait 0#32)) (initialState textBase)
        s.pc == textBase + 4#32 && s.cp0Status == (initialState textBase).cp0Status &&
            s.regs == (initialState textBase).regs) = true
