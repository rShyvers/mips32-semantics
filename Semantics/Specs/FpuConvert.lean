import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# FpuConvert — FPU conversions

Constructors: `roundWS` `truncWS` `ceilWS` `floorWS` `cvtWS` `cvtDS` `cvtSW` `cvtDW` `roundWD` `truncWD` `ceilWD` `floorWD` `cvtWD` `cvtSD`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  ROUND.W.fmt p.342; TRUNC.W.fmt p.441; CEIL.W.fmt p.128; FLOOR.W.fmt p.186; CVT.W.fmt p.160;
  CVT.D.fmt p.153; CVT.S.fmt p.159; CVT.D.fmt p.153; ROUND.W.fmt p.342; TRUNC.W.fmt p.441;
  CEIL.W.fmt p.128; FLOOR.W.fmt p.186; CVT.W.fmt p.160; CVT.S.fmt p.159.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Floating point (coprocessor 1)".

## Theorems in this file (14)

  `roundWS_spec_raw` `truncWS_spec_raw` `ceilWS_spec_raw` `floorWS_spec_raw` `cvtWS_spec_raw`
  `roundWD_spec_raw` `truncWD_spec_raw` `ceilWD_spec_raw` `floorWD_spec_raw` `cvtWD_spec_raw`
  `cvtSW_spec_raw` `cvtDW_spec_raw` `cvtDS_spec_raw` `cvtSD_spec_raw`
-/

-- W5: these statements describe the pre-Release 6 FPU (legacy NaN handling, `Status.FR = 0`
-- register pairs for doubles); the Release 6 target profile (CLAUDE.md: `FR = 1`,
-- `FCSR.NAN2008 = 1`) is implemented by W5.

set_option maxRecDepth 4000

/-! ## Conversions -/

/-- **`round.w.s`** converts to a 32-bit word rounding to nearest even, whatever FCSR.RM is:
`Mips.Fp.f32ToW32 .RN`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem roundWS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.roundWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32ToW32 .RN (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`trunc.w.s`** converts to a 32-bit word rounding toward zero, whatever FCSR.RM is:
`Mips.Fp.f32ToW32 .RZ`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem truncWS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.truncWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32ToW32 .RZ (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`ceil.w.s`** converts to a 32-bit word rounding toward +∞, whatever FCSR.RM is:
`Mips.Fp.f32ToW32 .RP`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem ceilWS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ceilWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32ToW32 .RP (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`floor.w.s`** converts to a 32-bit word rounding toward −∞, whatever FCSR.RM is:
`Mips.Fp.f32ToW32 .RM`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem floorWS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.floorWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32ToW32 .RM (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`cvt.w.s`** converts to a 32-bit word rounding **per FCSR.RM**
(MD00086 Vol II-A Rev 6.06, CVT.W.fmt, p.160): `Mips.Fp.f32ToW32 (getRM fcsr)` -/
theorem cvtWS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32ToW32 (Mips.Fp.getRM s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`round.w.d`** converts to a 32-bit word rounding to nearest even, whatever FCSR.RM is:
`Mips.Fp.f64ToW32 .RN`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem roundWD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.roundWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f64ToW32 .RN (readFpD s fs))) := by
  fp_step_spec

/-- **`trunc.w.d`** converts to a 32-bit word rounding toward zero, whatever FCSR.RM is:
`Mips.Fp.f64ToW32 .RZ`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem truncWD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.truncWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f64ToW32 .RZ (readFpD s fs))) := by
  fp_step_spec

/-- **`ceil.w.d`** converts to a 32-bit word rounding toward +∞, whatever FCSR.RM is:
`Mips.Fp.f64ToW32 .RP`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem ceilWD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ceilWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f64ToW32 .RP (readFpD s fs))) := by
  fp_step_spec

/-- **`floor.w.d`** converts to a 32-bit word rounding toward −∞, whatever FCSR.RM is:
`Mips.Fp.f64ToW32 .RM`. NaN, ±∞ and out-of-range values give `0x7FFFFFFF` with
Invalid Operation (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem floorWD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.floorWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f64ToW32 .RM (readFpD s fs))) := by
  fp_step_spec

/-- **`cvt.w.d`** converts to a 32-bit word rounding **per FCSR.RM**
(MD00086 Vol II-A Rev 6.06, CVT.W.fmt, p.160): `Mips.Fp.f64ToW32 (getRM fcsr)` -/
theorem cvtWD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f64ToW32 (Mips.Fp.getRM s.fcsr) (readFpD s fs))) := by
  fp_step_spec

/-- **`cvt.s.w`**: word → single, correctly rounded under FCSR (`Mips.Fp.w32ToF32`) -/
theorem cvtSW_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtSW fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.w32ToF32 (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`cvt.d.w`**: word → double, always exact (`Mips.Fp.w32ToF64`); raises nothing -/
theorem cvtDW_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtDW fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.w32ToF64 (readFpReg s (regIdx fs)), Mips.Fp.Flags.none)) := by
  fp_step_spec

/-- **`cvt.d.s`**: single → double (`Mips.Fp.f32ToF64`): exact; a quiet NaN keeps its sign and
payload, a signaling NaN signals Invalid -/
theorem cvtDS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtDS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f32ToF64 (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`cvt.s.d`**: double → single, correctly rounded under FCSR (`Mips.Fp.f64ToF32`) -/
theorem cvtSD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtSD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f64ToF32 (Mips.Fp.envOf s.fcsr) (readFpD s fs))) := by
  fp_step_spec
