import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# FpuMove — FPU moves: `mfc1`/`mtc1`/`mfhc1`/`mthc1`, `mov.fmt`, conditional moves

Constructors: `mfc1` `mtc1` `mfhc1` `mthc1` `movS` `movD` `movfS` `movtS` `movfD` `movtD` `movnS` `movzS` `movnD` `movzD` `movf` `movt`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  MFC1 p.267; MTC1 p.292; MFHC1 p.271; MTHC1 p.295; MOV.fmt p.275; MOV.fmt p.275;
  MOVF.fmt p.277-278; MOVT.fmt p.282-283; MOVF.fmt p.277-278; MOVT.fmt p.282-283; MOVN.fmt p.280;
  MOVZ.fmt p.285; MOVN.fmt p.280; MOVZ.fmt p.285; MOVF p.276; MOVT p.281.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Floating point (coprocessor 1)".

## Theorems in this file (16)

  `mfc1_spec_raw` `mtc1_spec_raw` `mfhc1_spec_raw` `mthc1_spec_raw` `movS_spec_raw` `movD_spec_raw`
  `movfS_spec_raw` `movtS_spec_raw` `movnS_spec_raw` `movzS_spec_raw` `movfD_spec_raw`
  `movtD_spec_raw` `movnD_spec_raw` `movzD_spec_raw` `movf_spec_raw` `movt_spec_raw`
-/

set_option maxRecDepth 4000

/-! ## Moves (non-arithmetic: FCSR untouched) -/

/-- **`mfc1`**: `$rt ← FPR[fs]`, raw bits -/
theorem mfc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      { (writeReg s (regIdx rt) (readFpReg s (regIdx fs))) with pc := (writeReg s (regIdx rt) (readFpReg s (regIdx fs))).pc + 4#32 }) := by
  fp_step_spec

/-- **`mtc1`**: `FPR[fs] ← $rt`, raw bits -/
theorem mtc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mtc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      { (writeFpReg s (regIdx fs) (readReg s (regIdx rt))) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`mfhc1`**: `$rt ←` the high word of the double in `fs`, i.e. `FPR[fs+1]`
(MD00086 Vol II-A Rev 6.06, MFHC1, p.271) -/
theorem mfhc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mfhc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      { (writeReg s (regIdx rt) (readFpReg s (regIdx (fs + 1#32)))) with pc := (writeReg s (regIdx rt) (readFpReg s (regIdx (fs + 1#32)))).pc + 4#32 }) := by
  fp_step_spec

/-- **`mthc1`**: the high word of the double in `fs` (`FPR[fs+1]`) `← $rt`; `FPR[fs]` is kept
(MD00086 Vol II-A Rev 6.06, MTHC1, p.295) -/
theorem mthc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.mthc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      { (writeFpReg s (regIdx (fs + 1#32)) (readReg s (regIdx rt))) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`mov.s`**: raw copy; an SNaN is copied without signaling -/
theorem movS_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movS fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      { (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`mov.d`**: raw copy of the register pair -/
theorem movD_spec_raw (s : State) (w fd fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movD fd fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      { (writeFpD s fd (readFpD s fs)) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`movf.s`**: `if FCC[cc] = 0 then fd ← fs`; otherwise nothing changes but `pc`
(MD00086 Vol II-A Rev 6.06, MOVF.fmt, p.277) -/
theorem movfS_spec_raw (s : State) (w fd fs cc : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movfS fd fs cc))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      if readFcc s cc then { s with pc := s.pc + 4#32 }
      else { (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`movt.s`**: `if FCC[cc] = 1 then fd ← fs` -/
theorem movtS_spec_raw (s : State) (w fd fs cc : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movtS fd fs cc))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      if readFcc s cc then { (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) with pc := s.pc + 4#32 }
      else { s with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`movn.s`**: `if $rt ≠ 0 then fd ← fs` -/
theorem movnS_spec_raw (s : State) (w fd fs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movnS fd fs rt))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      if readReg s (regIdx rt) != 0#32 then { (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) with pc := s.pc + 4#32 }
      else { s with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`movz.s`**: `if $rt = 0 then fd ← fs` -/
theorem movzS_spec_raw (s : State) (w fd fs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movzS fd fs rt))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      if readReg s (regIdx rt) == 0#32 then { (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs))) with pc := s.pc + 4#32 }
      else { s with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`movf.d`**: `if FCC[cc] = 0 then fd ← fs`; otherwise nothing changes but `pc`
(MD00086 Vol II-A Rev 6.06, MOVF.fmt, p.277) -/
theorem movfD_spec_raw (s : State) (w fd fs cc : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movfD fd fs cc))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      if readFcc s cc then { s with pc := s.pc + 4#32 }
      else { (writeFpD s fd (readFpD s fs)) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`movt.d`**: `if FCC[cc] = 1 then fd ← fs` -/
theorem movtD_spec_raw (s : State) (w fd fs cc : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movtD fd fs cc))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      if readFcc s cc then { (writeFpD s fd (readFpD s fs)) with pc := s.pc + 4#32 }
      else { s with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`movn.d`**: `if $rt ≠ 0 then fd ← fs` -/
theorem movnD_spec_raw (s : State) (w fd fs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movnD fd fs rt))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      if readReg s (regIdx rt) != 0#32 then { (writeFpD s fd (readFpD s fs)) with pc := s.pc + 4#32 }
      else { s with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`movz.d`**: `if $rt = 0 then fd ← fs` -/
theorem movzD_spec_raw (s : State) (w fd fs rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movzD fd fs rt))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      if readReg s (regIdx rt) == 0#32 then { (writeFpD s fd (readFpD s fs)) with pc := s.pc + 4#32 }
      else { s with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`movf`** (GPR): `if FCC[cc] = 0 then $rd ← $rs` (MD00086 Vol II-A Rev 6.06, MOVF, p.276) -/
theorem movf_spec_raw (s : State) (w rs cc rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movf rs cc rd))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      if readFcc s cc then { s with pc := s.pc + 4#32 }
      else
        { (writeReg s (regIdx rd) (readReg s (regIdx rs))) with
            pc := (writeReg s (regIdx rd) (readReg s (regIdx rs))).pc + 4#32 }) := by
  fp_step_spec

/-- **`movt`** (GPR): `if FCC[cc] = 1 then $rd ← $rs` (MD00086 Vol II-A Rev 6.06, MOVT, p.281) -/
theorem movt_spec_raw (s : State) (w rs cc rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.movt rs cc rd))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s = timerTick (
      if readFcc s cc then
        { (writeReg s (regIdx rd) (readReg s (regIdx rs))) with
            pc := (writeReg s (regIdx rd) (readReg s (regIdx rs))).pc + 4#32 }
      else { s with pc := s.pc + 4#32 }) := by
  fp_step_spec
