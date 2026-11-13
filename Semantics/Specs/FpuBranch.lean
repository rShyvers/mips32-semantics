import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# FpuBranch — branches on an FPU condition code

Constructors: `bc1f` `bc1t` `bc1fl` `bc1tl`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  BC1F p.56-57; BC1T p.60-61; BC1FL p.58-59; BC1TL p.62-63.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Floating point (coprocessor 1)".

## Theorems in this file (4)

  `bc1f_spec_raw` `bc1t_spec_raw` `bc1fl_spec_raw` `bc1tl_spec_raw`
-/

set_option maxRecDepth 4000

/-! ## Branches on a condition code -/

/-- **`bc1f`**: branch if `FCC[cc] = 0`, with the ordinary delay slot (MD00086 Vol II-A Rev 6.06,
BC1F, p.56) -/
theorem bc1f_spec_raw (s : State) (w cc imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bc1f cc imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      if readFcc s cc then { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 imm <<< 2)) } := by
  fp_step_spec

/-- **`bc1t`**: branch if `FCC[cc] = 1`, with the ordinary delay slot (MD00086 Vol II-A Rev 6.06,
BC1T, p.60) -/
theorem bc1t_spec_raw (s : State) (w cc imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bc1t cc imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      if readFcc s cc then
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 imm <<< 2)) }
      else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  fp_step_spec

/-- **`bc1fl`**: branch-likely if `FCC[cc] = 0`; **when not taken the delay slot is nullified**
(`pc ← pc + 8`, nothing pending) (MD00086 Vol II-A Rev 6.06, BC1FL, p.58) -/
theorem bc1fl_spec_raw (s : State) (w cc imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bc1fl cc imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      if readFcc s cc then { s with pc := s.pc + 8#32 }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 imm <<< 2)) } := by
  fp_step_spec

/-- **`bc1tl`**: branch-likely if `FCC[cc] = 1`; when not taken the delay slot is nullified
(MD00086 Vol II-A Rev 6.06, BC1TL, p.62) -/
theorem bc1tl_spec_raw (s : State) (w cc imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bc1tl cc imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      if readFcc s cc then
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 imm <<< 2)) }
      else { s with pc := s.pc + 8#32 } := by
  fp_step_spec
