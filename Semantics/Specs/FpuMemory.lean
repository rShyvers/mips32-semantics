import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# FpuMemory — FPU loads and stores

Constructors: `lwc1` `swc1` `ldc1` `sdc1` (Release 6 removed the indexed COP1X forms
LWXC1/LDXC1/SWXC1/SDXC1 and PREFX).

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  LWC1 p.236; SWC1 p.393; LDC1 p.215; SDC1 p.362.

Reference: `docs/spec/INSTRUCTION-REF.md`, section "Floating point (coprocessor 1)".

## Theorems in this file (6)

  `lwc1_spec_raw` `swc1_spec_raw` `ldc1_spec_raw` `sdc1_spec_raw` `lwc1_misaligned_spec`
  `swc1_misaligned_spec`
-/

-- W5: `ldc1`/`sdc1` are stated for the pre-Release 6 32-bit FPU register model (`Status.FR = 0`,
-- an even/odd register pair, little-endian word order); W5 replaces them with the `FR = 1` 64-bit
-- FPR form of the Release 6 target profile.

set_option maxRecDepth 4000

/-! ## Loads and stores -/

/-- **`lwc1`**: `FPR[ft] ← MEM32[$rs + sext(imm)]`; Address Error (AdEL) if not word-aligned -/
theorem lwc1_spec_raw (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdx rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v => { (writeFpReg s (regIdx ft) v) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`swc1`**: `MEM32[$rs + sext(imm)] ← FPR[ft]`; Address Error (AdES) if not word-aligned;
clears `LLbit` like every store -/
theorem swc1_spec_raw (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.swc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdx rs) + signExt16 imm
      match writeMemWord s addr (readFpReg s (regIdx ft)) with
      | none => takeAddressException s excCodeAdES addr
      | some s' => { s' with llBit := false, pc := s'.pc + 4#32 }) := by
  fp_step_spec

/-- **`ldc1`**: loads a little-endian doubleword into the pair (`FPR[ft]`, the low half ← the word
at `addr`; `FPR[ft+1]`, the high half ← the word at `addr + 4`; LDC1 p.215: `memdoubleword ←
memmsw || memlsw` with the byte order of the little-endian profile). **Address Error if `addr` is not a multiple of 8**
(MD00086 Vol II-A Rev 6.06, LDC1, p.215) -/
theorem ldc1_spec_raw (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ldc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdx rs) + signExt16 imm
      if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdEL addr
      else
        match readMemWord s addr, readMemWord s (addr + 4#32) with
        | some lo, some hi =>
          { (writeFpReg (writeFpReg s (regIdx ft) lo) (regIdx (ft + 1#32)) hi) with pc := s.pc + 4#32 }
        | _, _ => takeAddressException s excCodeAdEL addr) := by
  fp_step_spec

/-- **`sdc1`**: stores the pair as a little-endian doubleword (`FPR[ft]`, the low half, at `addr`;
`FPR[ft+1]` at `addr + 4`). **Address Error if `addr` is not a
multiple of 8** (MD00086 Vol II-A Rev 6.06, SDC1, p.362) -/
theorem sdc1_spec_raw (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sdc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdx rs) + signExt16 imm
      if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdES addr
      else
        match writeMemWord s addr (readFpReg s (regIdx ft)) with
        | none => takeAddressException s excCodeAdES addr
        | some s' =>
          match writeMemWord s' (addr + 4#32) (readFpReg s (regIdx (ft + 1#32))) with
          | none => takeAddressException s excCodeAdES addr
          | some s'' => { s'' with llBit := false, pc := s''.pc + 4#32 }) := by
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
    (hmisaligned : (readReg s (regIdx rs) + signExt16 imm).toNat % 4 ≠ 0) (hexec : executesInstr s = true) :
    step s = timerTick (takeAddressException s excCodeAdEL (readReg s (regIdx rs) + signExt16 imm)) := by
  rw [lwc1_spec_raw s w rs ft imm hfetch hdecode hpb hcu hexec]
  dsimp only
  rw [readMemWord_misaligned s _ hmisaligned]

/-- **A misaligned `swc1` raises Address Error (AdES) on the effective address**; memory is not
written. -/
theorem swc1_misaligned_spec (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.swc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true)
    (hmisaligned : (readReg s (regIdx rs) + signExt16 imm).toNat % 4 ≠ 0) (hexec : executesInstr s = true) :
    step s = timerTick (takeAddressException s excCodeAdES (readReg s (regIdx rs) + signExt16 imm)) := by
  rw [swc1_spec_raw s w rs ft imm hfetch hdecode hpb hcu hexec]
  dsimp only
  rw [writeMemWord_misaligned s _ _ hmisaligned]
