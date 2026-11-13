import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures
import Semantics.Specs.DelaySlot

/-!
# Cp0 — coprocessor 0: `mfc0`/`mtc0`, `di`/`ei`, `eret`, `wait`

Constructors: `mfc0` `mtc0` `di` `ei` `eret` `wait`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  MFC0 p.266; MTC0 p.290-291; DI p.164; EI p.176; ERET p.177-178; WAIT p.442-443.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Coprocessor 0 / traps and exceptions (real MIPS32 ISA)".

## Theorems in this file (10)

  `mfc0_spec_raw` `mtc0_spec_raw` `causeWriteMask_eq` `di_spec_raw` `ei_spec_raw` `eret_spec_raw`
  `eret_clears_llBit` `eret_in_delay_slot_reserved_instruction` `wait_spec_raw` `wait_preserves_state`
-/

set_option maxRecDepth 4000

/-! ## `mfc0`/`mtc0`, `di`/`ei`, `eret`, `wait`

(`pref` is in `Memory.lean`; the coprocessor-1 specifications are in the `Fpu*.lean` files.) -/

/-- **`mfc0` reads a modeled CP0 register `(rd, sel)` into GPR `$rt`**:
`(8,0)` BadVAddr, `(12,0)` Status, `(13,0)` Cause, `(14,0)` EPC, `(15,0)`
PRId, `(15,1)` EBase, `(16,0)` Config, `(16,1)` Config1, `(30,0)` ErrorEPC.
`decode` produces `mfc0` only for these; for any other pair (reachable only
through a hand-built `Instruction`) the step raises Reserved Instruction,
which is also what the undecodable word does. User mode is not modeled, so
Coprocessor Unusable is never raised. -/
theorem mfc0_spec_raw (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc0 rt rd sel))
    (hpb : s.pendingBranch = none) :
    step s =
      let read (v : W32) : State :=
        { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }
      match rd.toNat, sel.toNat with
      | 8, 0 => read s.cp0BadVAddr
      | 12, 0 => read s.cp0Status
      | 13, 0 => read s.cp0Cause
      | 14, 0 => read s.cp0Epc
      | 15, 0 => read 0x00010000#32
      | 15, 1 => read ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32)
      | 16, 0 => read (0x80008400#32 ||| s.cp0ConfigK0.setWidth 32)
      | 16, 1 => read 0x00000001#32
      | 30, 0 => read s.cp0ErrorEpc
      | _, _ => takeException s excCodeRI := by
  step_spec

/-- **`mtc0` writes GPR `$rt` into a modeled CP0 register, through that
register's write mask.** `Status` (12,0) keeps only `statusWriteMask` (IE,
EXL, ERL, IM7..0, BEV, CU1; every other bit reads as zero). `Cause` (13,0)
changes only `causeWriteMask` (DC, IV, IP1..0) and keeps `BD`, `CE`,
`ExcCode` and everything else. `EPC` (14,0) and `ErrorEPC` (30,0) are fully
writable. `EBase` (15,1) takes bits 29..12 of the written value under the
fixed bits 31..30 = `10`. `Config` (16,0) takes only `K0` (bits 2..0, Read/Write: MD00090 Vol III Rev 6.02 Table 9.64, p.235);
`BadVAddr` (8,0), `PRId` (15,0) and `Config1` (16,1) are read-only: the write is ignored. Any other pair
raises Reserved Instruction, as for `mfc0_spec_raw`. -/
theorem mtc0_spec_raw (s : State) (w rt rd sel : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc0 rt rd sel))
    (hpb : s.pendingBranch = none) :
    step s =
      match rd.toNat, sel.toNat with
      | 8, 0 => { s with pc := s.pc + 4#32 }
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
        { s with cp0ConfigK0 := (readReg s (regIdxSpec rt)).setWidth 3, pc := s.pc + 4#32 }
      | 16, 1 => { s with pc := s.pc + 4#32 }
      | 30, 0 =>
        { s with cp0ErrorEpc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | _, _ => takeException s excCodeRI := by
  step_spec

/-- The write mask of `Cause` is `DC` (27), `IV` (23), `IP1..IP0` (9..8)
(MD00090 Vol III Rev 6.02 §9.36, p.209-210). -/
theorem causeWriteMask_eq : causeWriteMask = 0x08800300#32 := rfl

/-- **`di`: `$rt ← Status`, then `Status.IE ← 0`** (MD00086 Vol II-A
Rev 6.06, DI, p.164). The value written to `$rt` is the `Status` before the
change; no other `Status` bit changes. -/
theorem di_spec_raw (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.di rt))
    (hpb : s.pendingBranch = none) :
    step s =
      { (writeReg { s with cp0Status := s.cp0Status &&& ~~~statusIeMask } (regIdxSpec rt)
            s.cp0Status) with
          pc := (writeReg { s with cp0Status := s.cp0Status &&& ~~~statusIeMask } (regIdxSpec rt)
            s.cp0Status).pc + 4#32 } := by
  step_spec

/-- **`ei`: `$rt ← Status`, then `Status.IE ← 1`** (MD00086 Vol II-A
Rev 6.06, EI, p.176). -/
theorem ei_spec_raw (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ei rt))
    (hpb : s.pendingBranch = none) :
    step s =
      { (writeReg { s with cp0Status := s.cp0Status ||| statusIeMask } (regIdxSpec rt)
            s.cp0Status) with
          pc := (writeReg { s with cp0Status := s.cp0Status ||| statusIeMask } (regIdxSpec rt)
            s.cp0Status).pc + 4#32 } := by
  step_spec

/-- **`eret`** (MD00086 "ERET"), executed outside a delay slot:
`if Status.ERL = 1 then PC ← ErrorEPC, ERL ← 0 else PC ← EPC, EXL ← 0`,
and **always `LLbit ← 0`**. It has no delay slot of its own: `pc` is set in
this very step. -/
theorem eret_spec_raw (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) :
    step s =
      if s.cp0Status &&& statusErlMask != 0#32 then
        { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask, llBit := false }
      else
        { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask, llBit := false } := by
  step_spec

/-- **`eret` clears `LLbit`**, whichever return address it uses — so an
`sc` after an exception return fails (see `sc_spec_raw`). -/
theorem eret_clears_llBit (s s' : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) (hstep : step s = s') :
    s'.llBit = false := by
  rw [eret_spec_raw s w hfetch hdecode hpb] at hstep
  split at hstep <;> (have h := hstep; rw [← h])

/-- **`eret` in a branch delay slot raises Reserved Instruction**, like a
branch or jump there (pin): "Pre-Release 6: The operation of the processor is
UNDEFINED if an ERET is executed in the delay slot of a branch or jump
instruction" (MD00086 Vol II-A Rev 6.06, ERET, p.177); Release 6 requires
Reserved Instruction (same page). See `branch_in_delay_slot_reserved_instruction`. -/
theorem eret_in_delay_slot_reserved_instruction (s : State) (w t : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = some t) :
    step s = takeException s excCodeRI :=
  branch_in_delay_slot_reserved_instruction s w .eret hfetch hdecode (by rw [hpb]; rfl) rfl

/-- **`wait` continues with the next instruction** (pin): the manual makes the low-power operation
implementation-dependent and says that when the pipeline restarts "execution continues with the
instruction following the WAIT instruction" (MD00086 Vol II-A Rev 6.06, WAIT, p.442; `PC ← PC + 4`
in the Operation, p.443). The model has no interrupts and treats the restart as immediate, so the
step changes only `pc` (`Step.lean`'s `wait` arm: `mkNext s s`). -/
theorem wait_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.wait code))
    (hpb : s.pendingBranch = none) :
    step s = { s with pc := s.pc + 4#32 } := by
  step_spec

/-- Corollary of `wait_spec_raw`: every piece of state besides `pc` is
left untouched — the "no-op" claim made precise, not just "produces some
next state". -/
theorem wait_preserves_state (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.wait code))
    (hpb : s.pendingBranch = none) :
    ∃ s', step s = s' ∧ s'.regs = s.regs ∧ s'.fpRegs = s.fpRegs ∧
      s'.hi = s.hi ∧ s'.lo = s.lo ∧ s'.mem = s.mem ∧
      s'.cp0Status = s.cp0Status ∧ s'.cp0Cause = s.cp0Cause ∧ s'.cp0Epc = s.cp0Epc ∧
      s'.pc = s.pc + 4#32 := by
  refine ⟨_, wait_spec_raw s w code hfetch hdecode hpb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

#guard (let s := stepIn (prog1Spec .eret)
          { (initialState textBase) with cp0Epc := 0x3000#32, cp0ErrorEpc := 0x4000#32,
                                         cp0Status := statusErlMask ||| statusExlMask }
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
