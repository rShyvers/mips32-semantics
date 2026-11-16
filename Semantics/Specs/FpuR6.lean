import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# FpuR6 — the Release 6 FPU instructions

Constructors: `cmpS` `cmpD` `bc1eqz` `bc1nez` `selS` `selD` `seleqzS` `seleqzD` `selnezS` `selnezD`
`maddfS` `maddfD` `msubfS` `msubfD` `maxS` `maxD` `minS` `minD` `maxaS` `maxaD` `minaS` `minaD`
`classS` `classD` `rintS` `rintD`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page): CMP.condn.fmt p.136-140; BC1EQZ BC1NEZ
p.54-55; SEL.fmt p.368; SELEQZ.fmt SELNEQZ.fmt p.371-372; MADDF.fmt MSUBF.fmt p.259-260; MAX.fmt
MIN.fmt MAXA.fmt MINA.fmt p.262-265; CLASS.fmt p.132-133; RINT.fmt p.337-338.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Floating point (coprocessor 1)".

## Theorems in this file (26)

  `cmpS_spec_raw` `cmpD_spec_raw` `bc1eqz_spec_raw` `bc1nez_spec_raw` `selS_spec_raw` `selD_spec_raw`
  `seleqzS_spec_raw` `seleqzD_spec_raw` `selnezS_spec_raw` `selnezD_spec_raw` `maddfS_spec_raw`
  `maddfD_spec_raw` `msubfS_spec_raw` `msubfD_spec_raw` `maxS_spec_raw` `maxD_spec_raw`
  `minS_spec_raw` `minD_spec_raw` `maxaS_spec_raw` `maxaD_spec_raw` `minaS_spec_raw` `minaD_spec_raw`
  `classS_spec_raw` `classD_spec_raw` `rintS_spec_raw` `rintD_spec_raw`
-/

/-! Release 6 FPU (`Status.FR = 1`): a single result goes to the low 32 bits of the 64-bit `FPR[fd]`
(`fpCompletesS`, or `writeFpReg` for the non-arithmetic ones; the upper half kept), a double result to
the whole register (`fpCompletesD`, `writeFpD`). `SEL`/`SELEQZ`/`SELNEZ` and `CLASS` leave FCSR
untouched; the others complete per `fpCompletesS`/`fpCompletesD` (Cause, the trap, Flags). -/

set_option maxRecDepth 4000

/-- **`cmp.condn.s`**: the predicate `Mips.Fp.f32Cmp` selected by the `condn` field (bits 4..0) on the
operands (flushed per FCSR.FS, `cmpInS`, no Inexact: MD00082 Vol I-A Rev 6.01 §6.7.2.4, p.102),
as a mask of 32 ones or zeros (`cmpMaskS`) completing per `fpCompletesS`; Invalid Operation
for an SNaN, or a QNaN with `cond3` set (MD00086 Vol II-A Rev 6.06, CMP.condn.fmt, p.136-140) -/
theorem cmpS_spec_raw (s : State) (w cond fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cmpS cond fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (cmpMaskS (Mips.Fp.f32Cmp (cmpCondn cond)
        (cmpInS (Mips.Fp.getFS s.fcsr) (readFpReg s (regIdx fs)))
        (cmpInS (Mips.Fp.getFS s.fcsr) (readFpReg s (regIdx ft)))))) := by
  fp_step_spec

/-- **`cmp.condn.d`**: as `cmpS_spec_raw`, `Mips.Fp.f64Cmp` and a 64-bit mask (`cmpMaskD`)
(MD00086 Vol II-A Rev 6.06, CMP.condn.fmt, p.136-140) -/
theorem cmpD_spec_raw (s : State) (w cond fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cmpD cond fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (cmpMaskD (Mips.Fp.f64Cmp (cmpCondn cond)
        (cmpInD (Mips.Fp.getFS s.fcsr) (readFpD s fs)) (cmpInD (Mips.Fp.getFS s.fcsr) (readFpD s ft))))) := by
  fp_step_spec

/-- **`bc1eqz`**: a branch with a delay slot, taken when bit 0 of `FPR[ft]` is 0; target
`PC + 4 + sign_extend(offset << 2)` (MD00086 Vol II-A Rev 6.06, BC1EQZ BC1NEZ, p.54-55) -/
theorem bc1eqz_spec_raw (s : State) (w ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bc1eqz ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readFpReg s (regIdx ft) &&& 1#32 == 0#32 then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  fp_step_spec

/-- **`bc1nez`**: as `bc1eqz_spec_raw`, taken when bit 0 of `FPR[ft]` is 1
(MD00086 Vol II-A Rev 6.06, BC1EQZ BC1NEZ, p.54-55) -/
theorem bc1nez_spec_raw (s : State) (w ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bc1nez ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readFpReg s (regIdx ft) &&& 1#32 == 0#32 then
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }) := by
  fp_step_spec

/-- **`sel.s`**: `FPR[fd] ← FPR[fd].bit0 ? FPR[ft] : FPR[fs]` (low 32 bits; FCSR untouched)
(MD00086 Vol II-A Rev 6.06, SEL.fmt, p.368) -/
theorem selS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.selS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpReg s (regIdx fd) (if (readFpReg s (regIdx fd)).getLsbD 0 then (readFpReg s (regIdx ft)) else (readFpReg s (regIdx fs)))) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`sel.d`**: as `selS_spec_raw`, the whole 64-bit registers (MD00086 Vol II-A Rev 6.06, SEL.fmt, p.368) -/
theorem selD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.selD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpD s fd (if (readFpReg s (regIdx fd)).getLsbD 0 then readFpD s ft else readFpD s fs)) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`seleqz.s`**: `FPR[fd] ← FPR[ft].bit0 ? 0 : FPR[fs]` (FCSR untouched)
(MD00086 Vol II-A Rev 6.06, SELEQZ.fmt SELNEQZ.fmt, p.371) -/
theorem seleqzS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.seleqzS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpReg s (regIdx fd) (if (readFpReg s (regIdx ft)).getLsbD 0 then 0#32 else (readFpReg s (regIdx fs)))) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`seleqz.d`**: as `seleqzS_spec_raw`, 64 bits (MD00086 Vol II-A Rev 6.06, SELEQZ.fmt SELNEQZ.fmt, p.371) -/
theorem seleqzD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.seleqzD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpD s fd (if (readFpReg s (regIdx ft)).getLsbD 0 then 0#64 else readFpD s fs)) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`selnez.s`**: `FPR[fd] ← FPR[ft].bit0 ? FPR[fs] : 0` (FCSR untouched)
(MD00086 Vol II-A Rev 6.06, SELEQZ.fmt SELNEQZ.fmt, p.371) -/
theorem selnezS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.selnezS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpReg s (regIdx fd) (if (readFpReg s (regIdx ft)).getLsbD 0 then (readFpReg s (regIdx fs)) else 0#32)) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`selnez.d`**: as `selnezS_spec_raw`, 64 bits (MD00086 Vol II-A Rev 6.06, SELEQZ.fmt SELNEQZ.fmt, p.371) -/
theorem selnezD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.selnezD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpD s fd (if (readFpReg s (regIdx ft)).getLsbD 0 then readFpD s fs else 0#64)) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`maddf.s`**: `FPR[fd] + FPR[fs] × FPR[ft]` with one rounding, `Mips.Fp.f32Fma` (`sub = false`),
completing per `fpCompletesS` (MD00086 Vol II-A Rev 6.06, MADDF.fmt MSUBF.fmt, p.259-260) -/
theorem maddfS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.maddfS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32Fma (Mips.Fp.envOf s.fcsr) false (readFpReg s (regIdx fd)) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`maddf.d`**: as `maddfS_spec_raw`, `Mips.Fp.f64Fma`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MADDF.fmt MSUBF.fmt, p.259-260) -/
theorem maddfD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.maddfD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64Fma (Mips.Fp.envOf s.fcsr) false (readFpD s fd) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec

/-- **`msubf.s`**: `FPR[fd] − FPR[fs] × FPR[ft]` with one rounding, `Mips.Fp.f32Fma` (`sub = true`),
completing per `fpCompletesS` (MD00086 Vol II-A Rev 6.06, MADDF.fmt MSUBF.fmt, p.259-260) -/
theorem msubfS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.msubfS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32Fma (Mips.Fp.envOf s.fcsr) true (readFpReg s (regIdx fd)) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`msubf.d`**: as `msubfS_spec_raw`, `Mips.Fp.f64Fma`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MADDF.fmt MSUBF.fmt, p.259-260) -/
theorem msubfD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.msubfD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64Fma (Mips.Fp.envOf s.fcsr) true (readFpD s fd) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec

/-- **`max.s`**: `maxNum(FPR[fs], FPR[ft])`, `Mips.Fp.f32MinMax .max`, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt, p.262-265) -/
theorem maxS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.maxS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32MinMax .max (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`max.d`**: as `maxS_spec_raw`, `Mips.Fp.f64MinMax .max`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt, p.262-265) -/
theorem maxD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.maxD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64MinMax .max (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec

/-- **`min.s`**: `minNum(FPR[fs], FPR[ft])`, `Mips.Fp.f32MinMax .min`, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt, p.262-265) -/
theorem minS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.minS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32MinMax .min (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`min.d`**: as `minS_spec_raw`, `Mips.Fp.f64MinMax .min`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt, p.262-265) -/
theorem minD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.minD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64MinMax .min (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec

/-- **`maxa.s`**: `maxNumMag(FPR[fs], FPR[ft])`, `Mips.Fp.f32MinMax .maxa`, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt, p.262-265) -/
theorem maxaS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.maxaS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32MinMax .maxa (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`maxa.d`**: as `maxaS_spec_raw`, `Mips.Fp.f64MinMax .maxa`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt, p.262-265) -/
theorem maxaD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.maxaD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64MinMax .maxa (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec

/-- **`mina.s`**: `minNumMag(FPR[fs], FPR[ft])`, `Mips.Fp.f32MinMax .mina`, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt, p.262-265) -/
theorem minaS_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.minaS fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32MinMax .mina (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))) := by
  fp_step_spec

/-- **`mina.d`**: as `minaS_spec_raw`, `Mips.Fp.f64MinMax .mina`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, MAX.fmt MIN.fmt MAXA.fmt MINA.fmt, p.262-265) -/
theorem minaD_spec_raw (s : State) (w fd fs ft : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.minaD fd fs ft))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64MinMax .mina (Mips.Fp.envOf s.fcsr) (readFpD s fs) (readFpD s ft))) := by
  fp_step_spec

/-- **`class.s`**: the class mask `Mips.Fp.f32Class` of the operand written to `FPR[fd]`; FCSR untouched
(MD00086 Vol II-A Rev 6.06, CLASS.fmt, p.132) -/
theorem classS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.classS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpReg s (regIdx fd) (Mips.Fp.f32Class (readFpReg s (regIdx fs)))) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`class.d`**: as `classS_spec_raw`, `Mips.Fp.f64Class` (MD00086 Vol II-A Rev 6.06, CLASS.fmt, p.132) -/
theorem classD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.classD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeFpD s fd (Mips.Fp.f64Class (readFpD s fs))) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`rint.s`**: round to an integral value in FCSR.RM, `Mips.Fp.f32Rint`, completing per `fpCompletesS`
(MD00086 Vol II-A Rev 6.06, RINT.fmt, p.337) -/
theorem rintS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rintS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesS s fd (Mips.Fp.f32Rint (Mips.Fp.envOf s.fcsr) (readFpReg s (regIdx fs)))) := by
  fp_step_spec

/-- **`rint.d`**: as `rintS_spec_raw`, `Mips.Fp.f64Rint`, completing per `fpCompletesD`
(MD00086 Vol II-A Rev 6.06, RINT.fmt, p.337) -/
theorem rintD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rintD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      fpCompletesD s fd (Mips.Fp.f64Rint (Mips.Fp.envOf s.fcsr) (readFpD s fs))) := by
  fp_step_spec
