import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# FpuArith — FPU arithmetic (single and double)

Constructors: `addS` `subS` `mulS` `divS` `sqrtS` `absS` `negS` `recipS` `rsqrtS` `addD` `subD` `mulD` `divD` `sqrtD` `absD` `negD` `recipD` `rsqrtD` `maddS` `msubS` `nmaddS` `nmsubS` `maddD` `msubD` `nmaddD` `nmsubD`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  ADD.fmt p.34; SUB.fmt p.389; MUL.fmt p.302; DIV.fmt p.170; SQRT.fmt p.382; ABS.fmt p.32;
  NEG.fmt p.307; RECIP.fmt p.336; RSQRT.fmt p.343; ADD.fmt p.34; SUB.fmt p.389; MUL.fmt p.302;
  DIV.fmt p.170; SQRT.fmt p.382; ABS.fmt p.32; NEG.fmt p.307; RECIP.fmt p.336; RSQRT.fmt p.343;
  MADD.fmt p.256-258; MSUB.fmt p.287-288; NMADD.fmt p.308-309; NMSUB.fmt p.310-311;
  MADD.fmt p.256-258; MSUB.fmt p.287-288; NMADD.fmt p.308-309; NMSUB.fmt p.310-311.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Floating point (coprocessor 1)".

## Theorems in this file (26)

  `addS_spec_raw` `subS_spec_raw` `mulS_spec_raw` `divS_spec_raw` `sqrtS_spec_raw`
  `recipS_spec_raw` `rsqrtS_spec_raw` `absS_spec_raw` `negS_spec_raw` `maddS_spec_raw`
  `msubS_spec_raw` `nmaddS_spec_raw` `nmsubS_spec_raw` `addD_spec_raw` `subD_spec_raw`
  `mulD_spec_raw` `divD_spec_raw` `sqrtD_spec_raw` `recipD_spec_raw` `rsqrtD_spec_raw`
  `absD_spec_raw` `negD_spec_raw` `maddD_spec_raw` `msubD_spec_raw` `nmaddD_spec_raw`
  `nmsubD_spec_raw`
-/

set_option maxRecDepth 4000

/-! ## Arithmetic -/

/-- **`add.s`: `fd ← fs + ft`**, single precision: the result bits and exceptions are
`Mips.Fp.f32Add` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, ADD.fmt, p.34) -/
theorem addS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd
        (Mips.Fp.f32Add (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`sub.s`: `fd ← fs − ft`**, single precision: the result bits and exceptions are
`Mips.Fp.f32Sub` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, SUB.fmt, p.389) -/
theorem subS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.subS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd
        (Mips.Fp.f32Sub (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`mul.s`: `fd ← fs × ft`**, single precision: the result bits and exceptions are
`Mips.Fp.f32Mul` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, MUL.fmt, p.302) -/
theorem mulS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mulS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd
        (Mips.Fp.f32Mul (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`div.s`: `fd ← fs / ft`**, single precision: the result bits and exceptions are
`Mips.Fp.f32Div` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, DIV.fmt, p.170) -/
theorem divS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.divS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd
        (Mips.Fp.f32Div (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`sqrt.s`**: `Mips.Fp.f32Sqrt` of the operand, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, SQRT.fmt, p.382). -/
theorem sqrtS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sqrtS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32Sqrt (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`recip.s`**: `Mips.Fp.f32Recip` of the operand, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, RECIP.fmt, p.336). -/
theorem recipS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.recipS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32Recip (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`rsqrt.s`**: `Mips.Fp.f32Rsqrt` of the operand, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, RSQRT.fmt, p.343). -/
theorem rsqrtS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rsqrtS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32Rsqrt (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`abs.s`**: `Mips.Fp.f32Abs` of the operand, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, ABS.fmt, p.32). Arithmetic (`FIR.Has2008 = 0`): any NaN operand signals Invalid Operation. -/
theorem absS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.absS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32Abs (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`neg.s`**: `Mips.Fp.f32Neg` of the operand, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, NEG.fmt, p.307). Arithmetic (`FIR.Has2008 = 0`): any NaN operand signals Invalid Operation. -/
theorem negS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.negS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32Neg (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`madd.s`** (unfused: multiply, round, add/subtract, round):
`Mips.Fp.f32Madd` of `fr`, `fs`, `ft`, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem maddS_spec_raw (s : State) (w fd fr fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.maddS fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd
        (Mips.Fp.f32Madd (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fr)) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`msub.s`** (unfused: multiply, round, add/subtract, round):
`Mips.Fp.f32Msub` of `fr`, `fs`, `ft`, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem msubS_spec_raw (s : State) (w fd fr fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.msubS fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd
        (Mips.Fp.f32Msub (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fr)) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`nmadd.s`** (unfused: multiply, round, add/subtract, round, negate):
`Mips.Fp.f32Nmadd` of `fr`, `fs`, `ft`, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem nmaddS_spec_raw (s : State) (w fd fr fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.nmaddS fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd
        (Mips.Fp.f32Nmadd (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fr)) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`nmsub.s`** (unfused: multiply, round, add/subtract, round, negate):
`Mips.Fp.f32Nmsub` of `fr`, `fs`, `ft`, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem nmsubS_spec_raw (s : State) (w fd fr fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.nmsubS fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd
        (Mips.Fp.f32Nmsub (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fr)) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`add.d`: `fd ← fs + ft`**, double precision: the result bits and exceptions are
`Mips.Fp.f64Add` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, ADD.fmt, p.34) -/
theorem addD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd
        (Mips.Fp.f64Add (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec

/-- **`sub.d`: `fd ← fs − ft`**, double precision: the result bits and exceptions are
`Mips.Fp.f64Sub` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, SUB.fmt, p.389) -/
theorem subD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.subD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd
        (Mips.Fp.f64Sub (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec

/-- **`mul.d`: `fd ← fs × ft`**, double precision: the result bits and exceptions are
`Mips.Fp.f64Mul` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MUL.fmt, p.302) -/
theorem mulD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mulD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd
        (Mips.Fp.f64Mul (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec

/-- **`div.d`: `fd ← fs / ft`**, double precision: the result bits and exceptions are
`Mips.Fp.f64Div` of the operand bit patterns under the FCSR environment (rounding
mode, enables, FS); completion and FCSR update per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, DIV.fmt, p.170) -/
theorem divD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.divD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd
        (Mips.Fp.f64Div (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec

/-- **`sqrt.d`**: `Mips.Fp.f64Sqrt` of the operand, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, SQRT.fmt, p.382). -/
theorem sqrtD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sqrtD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64Sqrt (Mips.Fp.envOf s.fcsr) (readFpD s fs))) := by
  fp_step_spec

/-- **`recip.d`**: `Mips.Fp.f64Recip` of the operand, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, RECIP.fmt, p.336). -/
theorem recipD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.recipD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64Recip (Mips.Fp.envOf s.fcsr) (readFpD s fs))) := by
  fp_step_spec

/-- **`rsqrt.d`**: `Mips.Fp.f64Rsqrt` of the operand, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, RSQRT.fmt, p.343). -/
theorem rsqrtD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rsqrtD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64Rsqrt (Mips.Fp.envOf s.fcsr) (readFpD s fs))) := by
  fp_step_spec

/-- **`abs.d`**: `Mips.Fp.f64Abs` of the operand, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, ABS.fmt, p.32). Arithmetic (`FIR.Has2008 = 0`): any NaN operand signals Invalid Operation. -/
theorem absD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.absD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64Abs (readFpD s fs))) := by
  fp_step_spec

/-- **`neg.d`**: `Mips.Fp.f64Neg` of the operand, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, NEG.fmt, p.307). Arithmetic (`FIR.Has2008 = 0`): any NaN operand signals Invalid Operation. -/
theorem negD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.negD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64Neg (readFpD s fs))) := by
  fp_step_spec

/-- **`madd.d`** (unfused: multiply, round, add/subtract, round):
`Mips.Fp.f64Madd` of `fr`, `fs`, `ft`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem maddD_spec_raw (s : State) (w fd fr fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.maddD fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd
        (Mips.Fp.f64Madd (Mips.Fp.envOf s.fcsr) (readFpD s fr) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec

/-- **`msub.d`** (unfused: multiply, round, add/subtract, round):
`Mips.Fp.f64Msub` of `fr`, `fs`, `ft`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem msubD_spec_raw (s : State) (w fd fr fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.msubD fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd
        (Mips.Fp.f64Msub (Mips.Fp.envOf s.fcsr) (readFpD s fr) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec

/-- **`nmadd.d`** (unfused: multiply, round, add/subtract, round, negate):
`Mips.Fp.f64Nmadd` of `fr`, `fs`, `ft`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem nmaddD_spec_raw (s : State) (w fd fr fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.nmaddD fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd
        (Mips.Fp.f64Nmadd (Mips.Fp.envOf s.fcsr) (readFpD s fr) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec

/-- **`nmsub.d`** (unfused: multiply, round, add/subtract, round, negate):
`Mips.Fp.f64Nmsub` of `fr`, `fs`, `ft`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310) -/
theorem nmsubD_spec_raw (s : State) (w fd fr fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.nmsubD fd fr fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd
        (Mips.Fp.f64Nmsub (Mips.Fp.envOf s.fcsr) (readFpD s fr) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec
