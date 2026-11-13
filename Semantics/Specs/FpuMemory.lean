import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# FpuMemory — FPU loads, stores and `prefx`

Constructors: `lwc1` `swc1` `ldc1` `sdc1` `lwxc1` `ldxc1` `swxc1` `sdxc1` `prefx`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  LWC1 p.236; SWC1 p.393; LDC1 p.215; SDC1 p.362; LWXC1 p.254; LDXC1 p.218; SWXC1 p.406;
  SDXC1 p.364; PREFX p.329.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Floating point (coprocessor 1)".

## Theorems in this file (13)

  `lwc1_spec_raw` `swc1_spec_raw` `ldc1_spec_raw` `sdc1_spec_raw` `lwxc1_spec_raw` `ldxc1_spec_raw`
  `swxc1_spec_raw` `sdxc1_spec_raw` `prefx_spec_raw` `lwc1_misaligned_spec` `swc1_misaligned_spec`
  `lwxc1_misaligned_spec` `swxc1_misaligned_spec`
-/

set_option maxRecDepth 4000

/-! ## Loads, stores, prefetch -/

/-- **`lwc1`**: `FPR[ft] ← MEM32[$rs + sext(imm)]`; Address Error (AdEL) if not word-aligned -/
theorem lwc1_spec_raw (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      let addr := readReg s (regIdx rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v => { (writeFpReg s (regIdx ft) v) with pc := s.pc + 4#32 } := by
  fp_step_spec

/-- **`swc1`**: `MEM32[$rs + sext(imm)] ← FPR[ft]`; Address Error (AdES) if not word-aligned;
clears `LLbit` like every store -/
theorem swc1_spec_raw (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.swc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      let addr := readReg s (regIdx rs) + signExt16 imm
      match writeMemWord s addr (readFpReg s (regIdx ft)) with
      | none => takeAddressException s excCodeAdES addr
      | some s' => { s' with llBit := false, pc := s'.pc + 4#32 } := by
  fp_step_spec

/-- **`ldc1`**: loads a big-endian doubleword into the pair (`FPR[ft+1]` ← the word at `addr`,
`FPR[ft]` ← the word at `addr + 4`). **Address Error if `addr` is not a multiple of 8**
(MD00086 Vol II-A Rev 6.06, LDC1, p.215) -/
theorem ldc1_spec_raw (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ldc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      let addr := readReg s (regIdx rs) + signExt16 imm
      if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdEL addr
      else
        match readMemWord s addr, readMemWord s (addr + 4#32) with
        | some hi, some lo =>
          { (writeFpReg (writeFpReg s (regIdx ft) lo) (regIdx (ft + 1#32)) hi) with pc := s.pc + 4#32 }
        | _, _ => takeAddressException s excCodeAdEL addr := by
  fp_step_spec

/-- **`sdc1`**: stores the pair as a big-endian doubleword. **Address Error if `addr` is not a
multiple of 8** (MD00086 Vol II-A Rev 6.06, SDC1, p.362) -/
theorem sdc1_spec_raw (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sdc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      let addr := readReg s (regIdx rs) + signExt16 imm
      if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdES addr
      else
        match writeMemWord s addr (readFpReg s (regIdx (ft + 1#32))) with
        | none => takeAddressException s excCodeAdES addr
        | some s' =>
          match writeMemWord s' (addr + 4#32) (readFpReg s (regIdx ft)) with
          | none => takeAddressException s excCodeAdES addr
          | some s'' => { s'' with llBit := false, pc := s''.pc + 4#32 } := by
  fp_step_spec

/-- **`lwxc1`**: as `lwc1` with the address `$base + $index` (MD00086 Vol II-A Rev 6.06, LWXC1, p.254) -/
theorem lwxc1_spec_raw (s : State) (w fd index base : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwxc1 fd index base))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      let addr := readReg s (regIdx base) + readReg s (regIdx index)
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v => { (writeFpReg s (regIdx fd) v) with pc := s.pc + 4#32 } := by
  fp_step_spec

/-- **`ldxc1`**: as `ldc1` with the address `$base + $index` (MD00086 Vol II-A Rev 6.06, LDXC1, p.218) -/
theorem ldxc1_spec_raw (s : State) (w fd index base : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ldxc1 fd index base))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      let addr := readReg s (regIdx base) + readReg s (regIdx index)
      if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdEL addr
      else
        match readMemWord s addr, readMemWord s (addr + 4#32) with
        | some hi, some lo =>
          { (writeFpReg (writeFpReg s (regIdx fd) lo) (regIdx (fd + 1#32)) hi) with pc := s.pc + 4#32 }
        | _, _ => takeAddressException s excCodeAdEL addr := by
  fp_step_spec

/-- **`swxc1`**: as `swc1` with the address `$base + $index` (MD00086 Vol II-A Rev 6.06, SWXC1, p.406) -/
theorem swxc1_spec_raw (s : State) (w fs index base : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.swxc1 fs index base))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      let addr := readReg s (regIdx base) + readReg s (regIdx index)
      match writeMemWord s addr (readFpReg s (regIdx fs)) with
      | none => takeAddressException s excCodeAdES addr
      | some s' => { s' with llBit := false, pc := s'.pc + 4#32 } := by
  fp_step_spec

/-- **`sdxc1`**: as `sdc1` with the address `$base + $index` (MD00086 Vol II-A Rev 6.06, SDXC1, p.364) -/
theorem sdxc1_spec_raw (s : State) (w fs index base : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sdxc1 fs index base))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      let addr := readReg s (regIdx base) + readReg s (regIdx index)
      if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdES addr
      else
        match writeMemWord s addr (readFpReg s (regIdx (fs + 1#32))) with
        | none => takeAddressException s excCodeAdES addr
        | some s' =>
          match writeMemWord s' (addr + 4#32) (readFpReg s (regIdx fs)) with
          | none => takeAddressException s excCodeAdES addr
          | some s'' => { s'' with llBit := false, pc := s''.pc + 4#32 } := by
  fp_step_spec

/-- **`prefx`** is a no-op (but, being a COP1X instruction, it needs `Status.CU1`)
(MD00086 Vol II-A Rev 6.06, PREFX, p.329) -/
theorem prefx_spec_raw (s : State) (w hint index base : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.prefx hint index base))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) :
    step s =
      { s with pc := s.pc + 4#32 } := by
  fp_step_spec

/-! ## Misaligned word accesses raise Address Error

Corollaries of the `_spec_raw` statements above and `readMemWord_misaligned` /
`writeMemWord_misaligned` (`Lemmas.lean`): the `none` arm is taken exactly when the effective
address is not a multiple of 4, and the exception names that address in `BadVAddr`. -/

/-- **A misaligned `lwc1` raises Address Error (AdEL) on the effective address**; no FP register
is written (`exceptionEntry_always`). Same shape as `lw_misaligned_spec`. -/
theorem lwc1_misaligned_spec (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hmisaligned : (readReg s (regIdx rs) + signExt16 imm).toNat % 4 ≠ 0) :
    step s = takeAddressException s excCodeAdEL (readReg s (regIdx rs) + signExt16 imm) := by
  rw [lwc1_spec_raw s w rs ft imm hfetch hdecode hpb hcu]
  dsimp only
  rw [readMemWord_misaligned s _ hmisaligned]

/-- **A misaligned `swc1` raises Address Error (AdES) on the effective address**; memory is not
written. -/
theorem swc1_misaligned_spec (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.swc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hmisaligned : (readReg s (regIdx rs) + signExt16 imm).toNat % 4 ≠ 0) :
    step s = takeAddressException s excCodeAdES (readReg s (regIdx rs) + signExt16 imm) := by
  rw [swc1_spec_raw s w rs ft imm hfetch hdecode hpb hcu]
  dsimp only
  rw [writeMemWord_misaligned s _ _ hmisaligned]

/-- **A misaligned `lwxc1` raises Address Error (AdEL) on `$base + $index`.** -/
theorem lwxc1_misaligned_spec (s : State) (w fd index base : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwxc1 fd index base))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hmisaligned : (readReg s (regIdx base) + readReg s (regIdx index)).toNat % 4 ≠ 0) :
    step s =
      takeAddressException s excCodeAdEL (readReg s (regIdx base) + readReg s (regIdx index)) := by
  rw [lwxc1_spec_raw s w fd index base hfetch hdecode hpb hcu]
  dsimp only
  rw [readMemWord_misaligned s _ hmisaligned]

/-- **A misaligned `swxc1` raises Address Error (AdES) on `$base + $index`.** -/
theorem swxc1_misaligned_spec (s : State) (w fs index base : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.swxc1 fs index base))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hmisaligned : (readReg s (regIdx base) + readReg s (regIdx index)).toNat % 4 ≠ 0) :
    step s =
      takeAddressException s excCodeAdES (readReg s (regIdx base) + readReg s (regIdx index)) := by
  rw [swxc1_spec_raw s w fs index base hfetch hdecode hpb hcu]
  dsimp only
  rw [writeMemWord_misaligned s _ _ hmisaligned]
