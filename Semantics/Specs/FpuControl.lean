import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# FpuControl — FPU control registers: `cfc1`/`ctc1`

Constructors: `cfc1` `ctc1`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  CFC1 p.129-130; CTC1 p.149-151.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Floating point (coprocessor 1)".

## Theorems in this file (5)

  `cfc1_spec_raw` `ctc1_spec_raw` `fcsr_ctc1_cfc1_roundtrip` `ctc1_fcsr_spec` `cfc1_fcsr_spec`
-/

set_option maxRecDepth 4000

/-! ## Control registers -/

/-- **`cfc1`**: `$rt ←` FP control register `fs` — `Mips.Fp.readControl`: FIR (0), FCCR (25),
FEXR (26), FENR (28), FCSR (31); any other number reads 0 (pin for UNPREDICTABLE)
(MD00086 Vol II-A Rev 6.06, CFC1, p.129-130) -/
theorem cfc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cfc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdx rt) ((Mips.Fp.readControl s.fcsr fs.toNat).getD 0#32)) with pc := (writeReg s (regIdx rt) ((Mips.Fp.readControl s.fcsr fs.toNat).getD 0#32)).pc + 4#32 }) := by
  fp_step_spec

/-- **`ctc1`**: FP control register `fs ← $rt` through `Mips.Fp.writeControl`, then
`CheckFPException`: if the new FCSR has a Cause bit whose Enable is set, or Cause.E, the
Floating Point exception is taken **with the register already written**. A register
number the manual leaves UNPREDICTABLE is not written (pin), and the `CheckFPException()` that
follows the UNPREDICTABLE arm still runs on the unchanged FCSR
(MD00086 Vol II-A Rev 6.06, CTC1, p.149-151) -/
theorem ctc1_spec_raw (s : State) (w rt fs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ctc1 rt fs))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      match Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt)) with
      | none =>
        if Mips.Fp.fcsrTrapPending s.fcsr then takeException s excCodeFPE
        else { s with pc := s.pc + 4#32 }
      | some f =>
        if Mips.Fp.fcsrTrapPending f then takeException { s with fcsr := f } excCodeFPE
        else { s with fcsr := f, pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **FCSR round trip through `ctc1 $rt, $31` / `cfc1 $rt, $31`.** Writing `v`
to control register 31 makes FCSR `v` with the reserved bits 22..18 cleared
(`Mips.Fp.fcsrWritableMask`), and reading register 31 of that FCSR returns
exactly that value. -/
theorem fcsr_ctc1_cfc1_roundtrip (fcsr v : W32) :
    ∃ f, Mips.Fp.writeControl fcsr 31 v = some f ∧ f = v &&& Mips.Fp.fcsrWritableMask ∧
      Mips.Fp.readControl f 31 = some (v &&& Mips.Fp.fcsrWritableMask) := by
  refine ⟨v &&& Mips.Fp.fcsrWritableMask, rfl, rfl, ?_⟩
  have h := Mips.Fp.readControl_writeControl_fcsr fcsr v
  simpa [Mips.Fp.writeControl, Mips.Fp.writeFCSR] using h

/-- The round trip at the level of `step`: after `ctc1 $rt, $31` completes
without a pending FP exception, the state's FCSR is `$rt` masked to the
writable bits. -/
theorem ctc1_fcsr_spec (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ctc1 rt 31#32))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hnt : Mips.Fp.fcsrTrapPending (readReg s (regIdx rt) &&& Mips.Fp.fcsrWritableMask) = false) (hexec : executesInstr s = true) :
    step s = timerTick (
      { s with fcsr := readReg s (regIdx rt) &&& Mips.Fp.fcsrWritableMask, pc := s.pc + 4#32 }) := by
  rw [ctc1_spec_raw s w rt 31#32 hfetch hdecode hpb hcu hexec]
  show timerTick (if Mips.Fp.fcsrTrapPending (readReg s (regIdx rt) &&& Mips.Fp.fcsrWritableMask) = true
    then _ else _) = _
  rw [ite_of_neg (by simp [hnt])]
  rfl

/-- … and `cfc1 $rt, $31` reads the FCSR back (its reserved bits as zero). -/
theorem cfc1_fcsr_spec (s : State) (w rt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.cfc1 rt 31#32))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdx rt) (s.fcsr &&& Mips.Fp.fcsrWritableMask)) with
          pc := (writeReg s (regIdx rt) (s.fcsr &&& Mips.Fp.fcsrWritableMask)).pc + 4#32 }) :=
  cfc1_spec_raw s w rt 31#32 hfetch hdecode hpb hcu hexec
