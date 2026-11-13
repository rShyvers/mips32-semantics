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
  `eret_clears_llBit` `eret_in_delay_slot_halts` `wait_spec_raw` `wait_preserves_state`
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
theorem mfc0_spec_raw (p : Program) (s : State) (w rt rd sel : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mfc0 rt rd sel))
    (hpb : s.pendingBranch = none) :
    step p s =
      let read (v : W32) : StepResult :=
        StepResult.next
          { (writeReg s (regIdxSpec rt) v) with pc := (writeReg s (regIdxSpec rt) v).pc + 4#32 }
      match rd.toNat, sel.toNat with
      | 8, 0 => read s.cp0BadVAddr
      | 12, 0 => read s.cp0Status
      | 13, 0 => read s.cp0Cause
      | 14, 0 => read s.cp0Epc
      | 15, 0 => read 0x00010000#32
      | 15, 1 => read ((s.cp0EBase &&& 0x3ffff000#32) ||| 0x80000000#32)
      | 16, 0 => read 0x80008402#32
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
fixed bits 31..30 = `10`. `BadVAddr` (8,0), `PRId` (15,0), `Config` (16,0)
and `Config1` (16,1) are read-only: the write is ignored. Any other pair
raises Reserved Instruction, as for `mfc0_spec_raw`. -/
theorem mtc0_spec_raw (p : Program) (s : State) (w rt rd sel : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.mtc0 rt rd sel))
    (hpb : s.pendingBranch = none) :
    step p s =
      match rd.toNat, sel.toNat with
      | 8, 0 => StepResult.next { s with pc := s.pc + 4#32 }
      | 12, 0 =>
        StepResult.next
          { s with cp0Status := readReg s (regIdxSpec rt) &&& statusWriteMask, pc := s.pc + 4#32 }
      | 13, 0 =>
        StepResult.next
          { s with
              cp0Cause := (s.cp0Cause &&& ~~~causeWriteMask) |||
                (readReg s (regIdxSpec rt) &&& causeWriteMask)
              pc := s.pc + 4#32 }
      | 14, 0 => StepResult.next { s with cp0Epc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | 15, 0 => StepResult.next { s with pc := s.pc + 4#32 }
      | 15, 1 =>
        StepResult.next
          { s with
              cp0EBase := (readReg s (regIdxSpec rt) &&& 0x3ffff000#32) ||| 0x80000000#32
              pc := s.pc + 4#32 }
      | 16, 0 => StepResult.next { s with pc := s.pc + 4#32 }
      | 16, 1 => StepResult.next { s with pc := s.pc + 4#32 }
      | 30, 0 =>
        StepResult.next { s with cp0ErrorEpc := readReg s (regIdxSpec rt), pc := s.pc + 4#32 }
      | _, _ => takeException s excCodeRI := by
  step_spec

/-- The write mask of `Cause` is `DC` (27), `IV` (23), `IP1..IP0` (9..8)
(MD00090 Vol III Rev 6.02 §9.36, p.209-210). -/
theorem causeWriteMask_eq : causeWriteMask = 0x08800300#32 := rfl

/-- **`di`: `$rt ← Status`, then `Status.IE ← 0`** (MD00086 Vol II-A
Rev 6.06, DI, p.164). The value written to `$rt` is the `Status` before the
change; no other `Status` bit changes. -/
theorem di_spec_raw (p : Program) (s : State) (w rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.di rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg { s with cp0Status := s.cp0Status &&& ~~~statusIeMask } (regIdxSpec rt)
            s.cp0Status) with
          pc := (writeReg { s with cp0Status := s.cp0Status &&& ~~~statusIeMask } (regIdxSpec rt)
            s.cp0Status).pc + 4#32 } := by
  step_spec

/-- **`ei`: `$rt ← Status`, then `Status.IE ← 1`** (MD00086 Vol II-A
Rev 6.06, EI, p.176). -/
theorem ei_spec_raw (p : Program) (s : State) (w rt : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.ei rt))
    (hpb : s.pendingBranch = none) :
    step p s =
      StepResult.next
        { (writeReg { s with cp0Status := s.cp0Status ||| statusIeMask } (regIdxSpec rt)
            s.cp0Status) with
          pc := (writeReg { s with cp0Status := s.cp0Status ||| statusIeMask } (regIdxSpec rt)
            s.cp0Status).pc + 4#32 } := by
  step_spec

/-- **`eret`** (MD00086 "ERET"), executed outside a delay slot:
`if Status.ERL = 1 then PC ← ErrorEPC, ERL ← 0 else PC ← EPC, EXL ← 0`,
and **always `LLbit ← 0`**. It has no delay slot of its own: `pc` is set in
this very step. -/
theorem eret_spec_raw (p : Program) (s : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) :
    step p s =
      if s.cp0Status &&& statusErlMask != 0#32 then
        StepResult.next
          { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask, llBit := false }
      else
        StepResult.next
          { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask, llBit := false } := by
  step_spec

/-- **`eret` clears `LLbit`**, whichever return address it uses — so an
`sc` after an exception return fails (see `sc_spec_raw`). -/
theorem eret_clears_llBit (p : Program) (s s' : State) (w : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = none) (hstep : step p s = StepResult.next s') :
    s'.llBit = false := by
  rw [eret_spec_raw p s w hfetch hdecode hpb] at hstep
  split at hstep <;> (injection hstep with h; rw [← h])

/-- **`eret` in a branch delay slot halts** (`branchInDelaySlot`), like a
branch or jump there: the architecture makes it UNPREDICTABLE. (This
replaces the former `eret_bypasses_delay_slot`, which stated that `eret`
ignored a pending branch and left it live — a behavior the architecture
does not define.) -/
theorem eret_in_delay_slot_halts (p : Program) (s : State) (w t : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some .eret)
    (hpb : s.pendingBranch = some t) :
    step p s = StepResult.halt .branchInDelaySlot :=
  branch_in_delay_slot_halts p s w .eret hfetch hdecode (by rw [hpb]; rfl) rfl

/-- **`wait` is a documented no-op**: this simulator has no
interrupt/timer model, so `wait` just falls through to `pc + 4` like any
ordinary non-control-flow instruction, touching no other state
(`Step.lean`'s `wait` docstring: `mkNext s s`). -/
theorem wait_spec_raw (p : Program) (s : State) (w code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.wait code))
    (hpb : s.pendingBranch = none) :
    step p s = StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

/-- Corollary of `wait_spec_raw`: every piece of state besides `pc` is
left untouched — the "no-op" claim made precise, not just "produces some
next state". -/
theorem wait_preserves_state (p : Program) (s : State) (w code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.wait code))
    (hpb : s.pendingBranch = none) :
    ∃ s', step p s = StepResult.next s' ∧ s'.regs = s.regs ∧ s'.fpRegs = s.fpRegs ∧
      s'.hi = s.hi ∧ s'.lo = s.lo ∧ s'.mem = s.mem ∧ s'.out = s.out ∧
      s'.cp0Status = s.cp0Status ∧ s'.cp0Cause = s.cp0Cause ∧ s'.cp0Epc = s.cp0Epc ∧
      s'.pc = s.pc + 4#32 := by
  refine ⟨_, wait_spec_raw p s w code hfetch hdecode hpb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- `mfc0` reads back Status/Cause/EPC, selected by `rd`;
-- an out-of-scope `rd` raises Reserved Instruction.
#guard (match step (prog1Spec (.mfc0 8#32 12#32 0#32)) { (initialState textBase) with cp0Status := 0x2#32 } with
        | .next s => readReg s 8 == 0x2#32
        | .halt _ => false) = true

#guard (match step (prog1Spec (.mfc0 8#32 13#32 0#32)) { (initialState textBase) with cp0Cause := 0x34#32 } with
        | .next s => readReg s 8 == 0x34#32
        | .halt _ => false) = true

#guard (match step (prog1Spec (.mfc0 8#32 14#32 0#32)) { (initialState textBase) with cp0Epc := 0x3000#32 } with
        | .next s => readReg s 8 == 0x3000#32
        | .halt _ => false) = true

#guard (match step (prog1Spec (.mfc0 8#32 0#32 0#32)) (initialState textBase) with
        | .next s' => causeExcCode s' == excCodeRI && s'.pc == exceptionVectorAddr
        | .halt _ => false) = true

-- `mtc0` writes Status/Cause (through its mask)/EPC from a GPR; an
-- out-of-scope `rd` raises Reserved Instruction.
#guard (match step (prog1Spec (.mtc0 8#32 12#32 0#32)) (setRegsSpec (initialState textBase) [(8, 0x2#32)]) with
        | .next s => s.cp0Status == 0x2#32
        | .halt _ => false) = true

#guard (match step (prog1Spec (.mtc0 8#32 13#32 0#32)) (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => s.cp0Cause == causeWriteMask
        | .halt _ => false) = true

#guard (match step (prog1Spec (.mtc0 8#32 14#32 0#32)) (setRegsSpec (initialState textBase) [(8, 0x3000#32)]) with
        | .next s => s.cp0Epc == 0x3000#32
        | .halt _ => false) = true

#guard (match step (prog1Spec (.mtc0 8#32 0#32 0#32)) (setRegsSpec (initialState textBase) [(8, 1#32)]) with
        | .next s' => causeExcCode s' == excCodeRI && s'.pc == exceptionVectorAddr
        | .halt _ => false) = true

-- `eret` restores `pc` from `cp0Epc` and clears `Status.EXL`.
#guard (match step (prog1Spec .eret)
          { (initialState textBase) with cp0Epc := 0x3000#32, cp0Status := statusExlMask } with
        | .next s => s.pc == 0x3000#32 && s.cp0Status == 0#32
        | .halt _ => false) = true

-- `eret_clears_llBit`; `Status.ERL = 1` returns to `ErrorEPC` and clears `ERL`.
#guard (match step (prog1Spec .eret)
          { (initialState textBase) with cp0Epc := 0x3000#32, cp0Status := statusExlMask, llBit := true } with
        | .next s => s.llBit == false
        | .halt _ => false) = true

#guard (match step (prog1Spec .eret)
          { (initialState textBase) with cp0Epc := 0x3000#32, cp0ErrorEpc := 0x4000#32,
                                         cp0Status := statusErlMask ||| statusExlMask } with
        | .next s => s.pc == 0x4000#32 && s.cp0Status == statusExlMask
        | .halt _ => false) = true

-- `eret_in_delay_slot_halts`.
#guard (match step (prog1Spec .eret)
          { (initialState textBase) with
            cp0Epc := 0x3000#32, cp0Status := statusExlMask,
            pendingBranch := some 0x99999999#32 } with
        | .halt .branchInDelaySlot => true
        | _ => false) = true

-- `wait` falls through to `pc + 4`, touching no other state.
#guard (match step (prog1Spec (.wait 0#32)) (initialState textBase) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == (initialState textBase).cp0Status &&
            s.regs == (initialState textBase).regs
        | .halt _ => false) = true
