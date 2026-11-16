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

/-! Release 6 FPU register model (`Status.FR = 1`, read-only): 32 FPRs of 64 bits. `mfc1`/`mtc1`/`mov.s`
access the low 32 bits (`readFpReg`/`writeFpReg`; a 32-bit write keeps the upper half, the model's pin
of the UNPREDICTABLE value, MD00082 Vol I-A Rev 6.01 §6.6.2, p.98), `mfhc1`/`mthc1` the high 32 bits
and `mov.d` the whole register (`readFpD`/`writeFpD`). -/

set_option maxRecDepth 4000

/-! ## Moves (non-arithmetic: FCSR untouched) -/

/-- **`mfc1`**: `$rt ←` the low 32 bits of `FPR[fs]`, raw bits (MD00086 Vol II-A Rev 6.06, MFC1, p.267) -/
theorem mfc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdx rt) (readFpReg s (regIdx fs))) with pc := (writeReg s (regIdx rt) (readFpReg s (regIdx fs))).pc + 4#32 }) := by
  fp_step_spec

/-- **`mtc1`**: the low 32 bits of `FPR[fs]` `← $rt`, raw bits; the upper 32 bits are kept
(MD00086 Vol II-A Rev 6.06, MTC1, p.292) -/
theorem mtc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpReg s (regIdx fs) (readReg s (regIdx rt))) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`mfhc1`**: `$rt ←` bits 63..32 of the 64-bit `FPR[fs]`
(MD00086 Vol II-A Rev 6.06, MFHC1, p.271: `GPR[rt] ← ValueFPR(fs, UNINTERPRETED_DOUBLEWORD)63..32`) -/
theorem mfhc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfhc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdx rt) ((readFpD s fs).extractLsb' 32 32)) with pc := (writeReg s (regIdx rt) ((readFpD s fs).extractLsb' 32 32)).pc + 4#32 }) := by
  fp_step_spec

/-- **`mthc1`**: bits 63..32 of `FPR[fs]` `← $rt`; bits 31..0 are kept
(MD00086 Vol II-A Rev 6.06, MTHC1, p.295: `StoreFPR(fs, UNINTERPRETED_DOUBLEWORD, GPR[rt] ||
ValueFPR(fs, UNINTERPRETED_DOUBLEWORD)31..0)`) -/
theorem mthc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mthc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpD s fs (readReg s (regIdx rt) ++ (readFpD s fs).extractLsb' 0 32)) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`mov.s`**: raw copy of the low 32 bits (the upper half of `FPR[fd]` kept); an SNaN is copied
without signaling (MD00086 Vol II-A Rev 6.06, MOV.fmt, p.275) -/
theorem movS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`mov.d`**: raw copy of the whole 64-bit register (MD00086 Vol II-A Rev 6.06, MOV.fmt, p.275) -/
theorem movD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpD s fd (readFpD s fs)) with pc := s.pc + 4#32 }) := by
  fp_step_spec
