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

/-! Release 6 FPU register model (`Status.FR = 1`): `lwc1`/`swc1` access the low 32 bits of the 64-bit
`FPR[ft]` (an `lwc1` keeps the upper half, the model's pin of the UNPREDICTABLE value, MD00082 Vol I-A
Rev 6.01 §6.6.2, p.98); `ldc1`/`sdc1` the whole register, one doubleword in the byte order of
`profile` (little-endian: the word at `addr` is bits 31..0). -/

set_option maxRecDepth 4000

/-! ## Loads and stores -/

/-- **`lwc1`**: the low 32 bits of `FPR[ft]` `← MEM32[$rs + sext(imm)]` (upper half kept); Address
Error (AdEL) if not word-aligned (MD00086 Vol II-A Rev 6.06, LWC1, p.236) -/
theorem lwc1_spec_raw (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.lwc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdx rs) + signExt16 imm
      match readMemWord s addr with
      | none => takeAddressException s excCodeAdEL addr
      | some v => { (writeFpReg s (regIdx ft) v) with pc := s.pc + 4#32 }) := by
  fp_step_spec

/-- **`swc1`**: `MEM32[$rs + sext(imm)] ←` the low 32 bits of `FPR[ft]`; Address Error (AdES) if not word-aligned;
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

/-- **`ldc1`**: loads the doubleword at `addr` into the whole 64-bit `FPR[ft]`. In the little-endian
`profile` the word at `addr` is the low half (bits 31..0) and the word at `addr + 4` the high half
(LDC1 p.215: `paddr xor ((BigEndianCPU xor ReverseEndian) || 0^2)`, `memdoubleword ← memmsw ||
memlsw`, `StoreFPR(ft, UNINTERPRETED_DOUBLEWORD, memdoubleword)`). **Address Error if `addr` is not
a multiple of 8** (the model pins the pre-Release 6 alignment rule; Release 6 "allows hardware to
provide address misalignment support in lieu of requiring natural alignment")
(MD00086 Vol II-A Rev 6.06, LDC1, p.215) -/
theorem ldc1_spec_raw (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.ldc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdx rs) + signExt16 imm
      if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdEL addr
      else
        match readMemWord s addr, readMemWord s (addr + 4#32) with
        | some lo, some hi => { (writeFpD s ft (hi ++ lo)) with pc := s.pc + 4#32 }
        | _, _ => takeAddressException s excCodeAdEL addr) := by
  fp_step_spec

/-- **`sdc1`**: stores the whole 64-bit `FPR[ft]` as a doubleword in the little-endian `profile`
(bits 31..0 at `addr`, bits 63..32 at `addr + 4`); clears `LLbit` like every store. **Address Error if
`addr` is not a multiple of 8** (MD00086 Vol II-A Rev 6.06, SDC1, p.362) -/
theorem sdc1_spec_raw (s : State) (w rs ft imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sdc1 rs ft imm))
    (hpb : s.pendingBranch = none) (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    step s = timerTick (
      let addr := readReg s (regIdx rs) + signExt16 imm
      if addr.toNat % 8 ≠ 0 then takeAddressException s excCodeAdES addr
      else
        match writeMemWord s addr ((readFpD s ft).extractLsb' 0 32) with
        | none => takeAddressException s excCodeAdES addr
        | some s' =>
          match writeMemWord s' (addr + 4#32) ((readFpD s ft).extractLsb' 32 32) with
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
