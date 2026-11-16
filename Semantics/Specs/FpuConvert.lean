import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# FpuConvert — FPU conversions

Constructors: `roundWS` `truncWS` `ceilWS` `floorWS` `cvtWS` `cvtDS` `cvtSW` `cvtDW` `roundWD` `truncWD` `ceilWD` `floorWD` `cvtWD` `cvtSD`;
Release 2 longword conversions (required in Release 6): `roundLS` `truncLS` `ceilLS` `floorLS` `cvtLS`
`roundLD` `truncLD` `ceilLD` `floorLD` `cvtLD` `cvtSL` `cvtDL`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  ROUND.W.fmt p.342; TRUNC.W.fmt p.441; CEIL.W.fmt p.128; FLOOR.W.fmt p.186; CVT.W.fmt p.160;
  CVT.D.fmt p.153; CVT.S.fmt p.159; CVT.D.fmt p.153; ROUND.W.fmt p.342; TRUNC.W.fmt p.441;
  CEIL.W.fmt p.128; FLOOR.W.fmt p.186; CVT.W.fmt p.160; CVT.S.fmt p.159;
  ROUND.L.fmt p.341; TRUNC.L.fmt p.440; CEIL.L.fmt p.127; FLOOR.L.fmt p.185; CVT.L.fmt p.154.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Floating point (coprocessor 1)".

## Theorems in this file (26)

  `roundWS_spec_raw` `truncWS_spec_raw` `ceilWS_spec_raw` `floorWS_spec_raw` `cvtWS_spec_raw`
  `roundWD_spec_raw` `truncWD_spec_raw` `ceilWD_spec_raw` `floorWD_spec_raw` `cvtWD_spec_raw`
  `cvtSW_spec_raw` `cvtDW_spec_raw` `cvtDS_spec_raw` `cvtSD_spec_raw`
  `roundLS_spec_raw` `truncLS_spec_raw` `ceilLS_spec_raw` `floorLS_spec_raw` `cvtLS_spec_raw`
  `roundLD_spec_raw` `truncLD_spec_raw` `ceilLD_spec_raw` `floorLD_spec_raw` `cvtLD_spec_raw`
  `cvtSL_spec_raw` `cvtDL_spec_raw`
-/

/-! Release 6 FPU (`Status.FR = 1`, `FCSR.NAN2008 = 1`): a double or longword operand is the whole
64-bit `FPR[fs]` (`readFpD`), a single or word operand its low 32 bits (`readFpReg`); a 32-bit result
goes to the low half of `FPR[fd]` (`fpCompletesS`), a 64-bit result to the whole register
(`fpCompletesD`). Every conversion from a floating point operand flushes a subnormal operand to zero
when `FCSR.FS = 1` (the flush flag `Mips.Fp.getFS s.fcsr`). An invalid conversion to a fixed point
format gives the `FCSR.NAN2008 = 1` default result: 0 for a NaN, the largest integer for `+∞` or a
value too big, the smallest for `−∞` or a value too small, with Invalid Operation (MD00082 Vol I-A
Rev 6.01 §6.3.1.5, Table 6.3, p.82). -/

set_option maxRecDepth 4000

/-! ## Conversions -/

/-- **`round.w.s`** converts to a 32-bit word rounding to nearest even, whatever FCSR.RM is:
`Mips.Fp.f32ToW32 .RN`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF`, `−∞` or a value too small `0x80000000`, with Invalid Operation (MD00082 Vol I-A Rev
6.01 Table 6.3, p.82) -/
theorem roundWS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.roundWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32ToW32 .RN (Mips.Fp.getFS s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`trunc.w.s`** converts to a 32-bit word rounding toward zero, whatever FCSR.RM is:
`Mips.Fp.f32ToW32 .RZ`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF`, `−∞` or a value too small `0x80000000`, with Invalid Operation (MD00082 Vol I-A Rev
6.01 Table 6.3, p.82) -/
theorem truncWS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.truncWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32ToW32 .RZ (Mips.Fp.getFS s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`ceil.w.s`** converts to a 32-bit word rounding toward +∞, whatever FCSR.RM is:
`Mips.Fp.f32ToW32 .RP`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF`, `−∞` or a value too small `0x80000000`, with Invalid Operation (MD00082 Vol I-A Rev
6.01 Table 6.3, p.82) -/
theorem ceilWS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ceilWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32ToW32 .RP (Mips.Fp.getFS s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`floor.w.s`** converts to a 32-bit word rounding toward −∞, whatever FCSR.RM is:
`Mips.Fp.f32ToW32 .RM`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF`, `−∞` or a value too small `0x80000000`, with Invalid Operation (MD00082 Vol I-A Rev
6.01 Table 6.3, p.82) -/
theorem floorWS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.floorWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32ToW32 .RM (Mips.Fp.getFS s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`cvt.w.s`** converts to a 32-bit word rounding **per FCSR.RM**
(MD00086 Vol II-A Rev 6.06, CVT.W.fmt, p.160): `Mips.Fp.f32ToW32 (getRM fcsr)` -/
theorem cvtWS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtWS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32ToW32 (Mips.Fp.getRM s.fcsr) (Mips.Fp.getFS s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`round.w.d`** converts to a 32-bit word rounding to nearest even, whatever FCSR.RM is:
`Mips.Fp.f64ToW32 .RN`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF`, `−∞` or a value too small `0x80000000`, with Invalid Operation (MD00082 Vol I-A Rev
6.01 Table 6.3, p.82) -/
theorem roundWD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.roundWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f64ToW32 .RN (Mips.Fp.getFS s.fcsr) (readFpD s fs))) := by
  fp_step_spec

/-- **`trunc.w.d`** converts to a 32-bit word rounding toward zero, whatever FCSR.RM is:
`Mips.Fp.f64ToW32 .RZ`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF`, `−∞` or a value too small `0x80000000`, with Invalid Operation (MD00082 Vol I-A Rev
6.01 Table 6.3, p.82) -/
theorem truncWD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.truncWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f64ToW32 .RZ (Mips.Fp.getFS s.fcsr) (readFpD s fs))) := by
  fp_step_spec

/-- **`ceil.w.d`** converts to a 32-bit word rounding toward +∞, whatever FCSR.RM is:
`Mips.Fp.f64ToW32 .RP`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF`, `−∞` or a value too small `0x80000000`, with Invalid Operation (MD00082 Vol I-A Rev
6.01 Table 6.3, p.82) -/
theorem ceilWD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ceilWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f64ToW32 .RP (Mips.Fp.getFS s.fcsr) (readFpD s fs))) := by
  fp_step_spec

/-- **`floor.w.d`** converts to a 32-bit word rounding toward −∞, whatever FCSR.RM is:
`Mips.Fp.f64ToW32 .RM`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF`, `−∞` or a value too small `0x80000000`, with Invalid Operation (MD00082 Vol I-A Rev
6.01 Table 6.3, p.82) -/
theorem floorWD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.floorWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f64ToW32 .RM (Mips.Fp.getFS s.fcsr) (readFpD s fs))) := by
  fp_step_spec

/-- **`cvt.w.d`** converts to a 32-bit word rounding **per FCSR.RM**
(MD00086 Vol II-A Rev 6.06, CVT.W.fmt, p.160): `Mips.Fp.f64ToW32 (getRM fcsr)` -/
theorem cvtWD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtWD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f64ToW32 (Mips.Fp.getRM s.fcsr) (Mips.Fp.getFS s.fcsr) (readFpD s fs))) := by
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
payload, a signaling NaN signals Invalid; a subnormal operand is flushed to zero when `FCSR.FS = 1`
(MD00086 Vol II-A Rev 6.06, CVT.D.fmt, p.153) -/
theorem cvtDS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtDS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f32ToF64 (Mips.Fp.getFS s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`cvt.s.d`**: double → single, correctly rounded under FCSR (`Mips.Fp.f64ToF32`) -/
theorem cvtSD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtSD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f64ToF32 (Mips.Fp.envOf s.fcsr) (readFpD s fs))) := by
  fp_step_spec

-- BEGIN R6-5 (C)
/-! ## Conversions to and from the 64-bit longword format L

Release 6 requires L on a 64-bit FPU (MD00082 Vol I-A Rev 6.01 Table 6.4 note 3, p.85). A longword
operand or result is the whole 64-bit FPR (`Status.FR = 1`). -/

/-- **`round.l.s`** converts to a 64-bit longword rounding to nearest even, whatever FCSR.RM is:
`Mips.Fp.f32ToW64 .RN`, written to the whole 64-bit `FPR[fd]`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF_FFFFFFFF`, `−∞` or a value too small `0x80000000_00000000`, with Invalid Operation
(MD00086 Vol II-A Rev 6.06, ROUND.L.fmt, p.341; MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem roundLS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.roundLS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f32ToW64 .RN (Mips.Fp.getFS s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`trunc.l.s`** converts to a 64-bit longword rounding toward zero, whatever FCSR.RM is:
`Mips.Fp.f32ToW64 .RZ`, written to the whole 64-bit `FPR[fd]`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF_FFFFFFFF`, `−∞` or a value too small `0x80000000_00000000`, with Invalid Operation
(MD00086 Vol II-A Rev 6.06, TRUNC.L.fmt, p.440; MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem truncLS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.truncLS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f32ToW64 .RZ (Mips.Fp.getFS s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`ceil.l.s`** converts to a 64-bit longword rounding toward +∞, whatever FCSR.RM is:
`Mips.Fp.f32ToW64 .RP`, written to the whole 64-bit `FPR[fd]`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF_FFFFFFFF`, `−∞` or a value too small `0x80000000_00000000`, with Invalid Operation
(MD00086 Vol II-A Rev 6.06, CEIL.L.fmt, p.127; MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem ceilLS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ceilLS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f32ToW64 .RP (Mips.Fp.getFS s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`floor.l.s`** converts to a 64-bit longword rounding toward −∞, whatever FCSR.RM is:
`Mips.Fp.f32ToW64 .RM`, written to the whole 64-bit `FPR[fd]`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF_FFFFFFFF`, `−∞` or a value too small `0x80000000_00000000`, with Invalid Operation
(MD00086 Vol II-A Rev 6.06, FLOOR.L.fmt, p.185; MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem floorLS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.floorLS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f32ToW64 .RM (Mips.Fp.getFS s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`cvt.l.s`** converts to a 64-bit longword rounding **per FCSR.RM**:
`Mips.Fp.f32ToW64 (getRM fcsr)`, written to the whole 64-bit `FPR[fd]`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF_FFFFFFFF`, `−∞` or a value too small `0x80000000_00000000`, with Invalid Operation
(MD00086 Vol II-A Rev 6.06, CVT.L.fmt, p.154) -/
theorem cvtLS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtLS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f32ToW64 (Mips.Fp.getRM s.fcsr) (Mips.Fp.getFS s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`round.l.d`** converts to a 64-bit longword rounding to nearest even, whatever FCSR.RM is:
`Mips.Fp.f64ToW64 .RN`, written to the whole 64-bit `FPR[fd]`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF_FFFFFFFF`, `−∞` or a value too small `0x80000000_00000000`, with Invalid Operation
(MD00086 Vol II-A Rev 6.06, ROUND.L.fmt, p.341; MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem roundLD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.roundLD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64ToW64 .RN (Mips.Fp.getFS s.fcsr) (readFpD s fs))) := by
  fp_step_spec

/-- **`trunc.l.d`** converts to a 64-bit longword rounding toward zero, whatever FCSR.RM is:
`Mips.Fp.f64ToW64 .RZ`, written to the whole 64-bit `FPR[fd]`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF_FFFFFFFF`, `−∞` or a value too small `0x80000000_00000000`, with Invalid Operation
(MD00086 Vol II-A Rev 6.06, TRUNC.L.fmt, p.440; MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem truncLD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.truncLD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64ToW64 .RZ (Mips.Fp.getFS s.fcsr) (readFpD s fs))) := by
  fp_step_spec

/-- **`ceil.l.d`** converts to a 64-bit longword rounding toward +∞, whatever FCSR.RM is:
`Mips.Fp.f64ToW64 .RP`, written to the whole 64-bit `FPR[fd]`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF_FFFFFFFF`, `−∞` or a value too small `0x80000000_00000000`, with Invalid Operation
(MD00086 Vol II-A Rev 6.06, CEIL.L.fmt, p.127; MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem ceilLD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ceilLD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64ToW64 .RP (Mips.Fp.getFS s.fcsr) (readFpD s fs))) := by
  fp_step_spec

/-- **`floor.l.d`** converts to a 64-bit longword rounding toward −∞, whatever FCSR.RM is:
`Mips.Fp.f64ToW64 .RM`, written to the whole 64-bit `FPR[fd]`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF_FFFFFFFF`, `−∞` or a value too small `0x80000000_00000000`, with Invalid Operation
(MD00086 Vol II-A Rev 6.06, FLOOR.L.fmt, p.185; MD00082 Vol I-A Rev 6.01 Table 6.3, p.82) -/
theorem floorLD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.floorLD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64ToW64 .RM (Mips.Fp.getFS s.fcsr) (readFpD s fs))) := by
  fp_step_spec

/-- **`cvt.l.d`** converts to a 64-bit longword rounding **per FCSR.RM**:
`Mips.Fp.f64ToW64 (getRM fcsr)`, written to the whole 64-bit `FPR[fd]`. A NaN gives 0, `+∞` or a value too big
`0x7FFFFFFF_FFFFFFFF`, `−∞` or a value too small `0x80000000_00000000`, with Invalid Operation
(MD00086 Vol II-A Rev 6.06, CVT.L.fmt, p.154) -/
theorem cvtLD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtLD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64ToW64 (Mips.Fp.getRM s.fcsr) (Mips.Fp.getFS s.fcsr) (readFpD s fs))) := by
  fp_step_spec

/-- **`cvt.s.l`**: longword (the whole 64-bit `FPR[fs]`) → single, rounded per FCSR.RM
(`Mips.Fp.w64ToF32`; Inexact when the value needs rounding); the single goes to the low half of
`FPR[fd]` (MD00086 Vol II-A Rev 6.06, CVT.S.fmt, p.159) -/
theorem cvtSL_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtSL fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.w64ToF32 (Mips.Fp.envOf s.fcsr) (readFpD s fs))) := by
  fp_step_spec

/-- **`cvt.d.l`**: longword → double, rounded per FCSR.RM (`Mips.Fp.w64ToF64`; unlike `cvt.d.w` it
can be inexact) (MD00086 Vol II-A Rev 6.06, CVT.D.fmt, p.153) -/
theorem cvtDL_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cvtDL fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.w64ToF64 (Mips.Fp.envOf s.fcsr) (readFpD s fs))) := by
  fp_step_spec
-- END R6-5 (C)
