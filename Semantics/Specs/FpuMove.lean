import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# FpuMove — FPU moves: `mfc1`/`mtc1`/`mfhc1`/`mthc1`, `mov.fmt`

Constructors: `mfc1` `mtc1` `mfhc1` `mthc1` `movS` `movD` (Release 6 removed the conditional moves
MOVF/MOVT/MOVN/MOVZ and their `.fmt` forms).

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  MFC1 p.267; MTC1 p.292; MFHC1 p.271; MTHC1 p.295; MOV.fmt p.275.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Floating point (coprocessor 1)".

## Theorems in this file (6)

  `mfc1_spec_raw` `mtc1_spec_raw` `mfhc1_spec_raw` `mthc1_spec_raw` `movS_spec_raw` `movD_spec_raw`
-/

-- W5: these statements describe the pre-Release 6 32-bit FPU register model (`Status.FR = 0`: a
-- double in an even/odd register pair, `mfhc1`/`mthc1` on the odd register); the Release 6 target
-- profile (CLAUDE.md) is `FR = 1` (64-bit FPRs), which W5 implements.

set_option maxRecDepth 4000

/-! ## Moves (non-arithmetic: FCSR untouched) -/

/-- **`mfc1`**: `$rt ← FPR[fs]`, raw bits -/
theorem mfc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdx rt) (readFpReg s (regIdx fs))) with pc := (writeReg s (regIdx rt) (readFpReg s (regIdx fs))).pc + 4#32 }) := by
  fp_step_spec

/-- **`mtc1`**: `FPR[fs] ← $rt`, raw bits -/
theorem mtc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpReg s (regIdx fs) (readReg s (regIdx rt))) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`mfhc1`**: `$rt ←` the high word of the double in `fs`, i.e. `FPR[fs+1]`
(MD00086 Vol II-A Rev 6.06, MFHC1, p.271) -/
theorem mfhc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfhc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdx rt) (readFpReg s (regIdx (fs + 1#32)))) with pc := (writeReg s (regIdx rt) (readFpReg s (regIdx (fs + 1#32)))).pc + 4#32 }) := by
  fp_step_spec

/-- **`mthc1`**: the high word of the double in `fs` (`FPR[fs+1]`) `← $rt`; `FPR[fs]` is kept
(MD00086 Vol II-A Rev 6.06, MTHC1, p.295) -/
theorem mthc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mthc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpReg s (regIdx (fs + 1#32)) (readReg s (regIdx rt))) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`mov.s`**: raw copy; an SNaN is copied without signaling -/
theorem movS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`mov.d`**: raw copy of the register pair -/
theorem movD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpD s fd (readFpD s fs)) with pc := s.pc + 4#32 }) := by
  fp_step_spec
