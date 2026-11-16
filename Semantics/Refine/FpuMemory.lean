import Semantics.Refine.BridgeFpuMove

/-!
# Refine.FpuMemory — FP loads and stores against `execInstr` (7C S4b)

`LWC1`, `SWC1`, `LDC1`, `SDC1` (Release 6 removed the indexed forms and `PREFX`). The alignment
check (word: `vAddr1..0`, doubleword: `vAddr2..0`; an Address Error with `BadVAddr = vAddr`), the
address check and Fixed Mapping translation (`Refine/Fetch.lean`), then the memory elements. The
doubleword pages access the word at `pAddr xor ((BigEndianCPU xor ReverseEndian) || 0^2)` first,
which is `pAddr` on this little-endian profile (`endian_xor`): the least-significant word
(`FPR[ft]` bits 31..0) is at the effective address, the most-significant one (bits 63..32) at `+ 4`, as in the
model (`profile.bigEndianMem = false`).
-/

namespace Refine

open Manual

-- The memory images are compared through `memOf_ins4_swap`/`storeWord_ins4`; keeping `ins4` and
-- `memOf` folded makes the final `rfl` of the store proofs cheap.
attribute [local irreducible] ins4 memOf

/-- The tail of `LWC1` after the effective address `va`. -/
macro "lw_fp_tail" s:ident va:ident hfsz:ident : tactic => `(tactic| (
  by_cases hal : ($va).toNat % 4 = 0
  · have hm : (bits $va 1 0 != 0#2) = false := by rw [misaligned_eq]; simp [hal]
    simp only [hm, Bool.false_eq_true, ↓reduceIte]
    rw [addrTrans_run $s $va .DATA .LOAD _ _ rfl, readMemWord_eq $s $va hal]
    unfold translate
    cases accessAllowed $s $va
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
      rw [gep_adel]
    · simp only [↓reduceIte, Option.map_some, loadMemory_model, StoreFPR32, Pseudo.modify, abs_Mem]
      rw [abs_mkNext_writeFpReg _ _ _ $hfsz]
      simp only [complete_plain, regIdx_eq_reg]
      rfl
  · have hm : (bits $va 1 0 != 0#2) = true := by rw [misaligned_eq]; simp [hal]
    have hr : readMemWord $s $va = none := by unfold readMemWord; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hr]
    rw [gep_adel]))

/-- The tail of `SWC1` after the effective address `va`. -/
macro "sw_fp_tail" s:ident va:ident : tactic => `(tactic| (
  by_cases hal : ($va).toNat % 4 = 0
  · have hm : (bits $va 1 0 != 0#2) = false := by rw [misaligned_eq]; simp [hal]
    simp only [hm, Bool.false_eq_true, ↓reduceIte]
    rw [addrTrans_run $s $va .DATA .STORE _ _ rfl, writeMemWord_eq $s $va _ hal]
    unfold translate
    cases accessAllowed $s $va
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
      rw [gep_ades]
    · have hst : modelCtx.oracle.storeClearsLL (abs $s) = true := rfl
      simp only [↓reduceIte, Option.map_some, ValueFPR32, StoreMemory, bind, Pseudo.oracle,
        Pseudo.modify, abs_Mem, hst, storeWord_ins4 _ _ _ (fixedMappingPA_aligned _ _ hal)]
      rw [complete_plain, mkNext, abs_advance _ _ (by rfl)]
      rfl
  · have hm : (bits $va 1 0 != 0#2) = true := by rw [misaligned_eq]; simp [hal]
    have hr : ∀ v, writeMemWord $s $va v = none := by intro v; unfold writeMemWord; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hr]
    rw [gep_ades]))

/-- The tail of `LDC1` after the effective address `va`. -/
macro "ld_fp_tail" s:ident va:ident hfsz:ident : tactic => `(tactic| (
  by_cases hal : ($va).toNat % 8 = 0
  · have hm : (bits $va 2 0 != 0#3) = false := by rw [misaligned8_eq]; simp [hal]
    have hpa := fixedMappingPA_aligned8 (erlSet $s) $va hal
    simp only [hm, Bool.false_eq_true, ↓reduceIte, hal, ne_eq, not_true_eq_false]
    rw [addrTrans_run $s $va .DATA .LOAD _ _ rfl, readMemWord_eq $s $va (aligned4_of_8 hal),
      readMemWord_eq $s ($va + 4#32) (aligned4_add4 hal), translate_add4 $s $va hal]
    unfold translate
    cases accessAllowed $s $va
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
      rw [gep_adel]
    · simp only [↓reduceIte, Option.map_some, Pseudo.get, endian_xor, BitVec.xor_zero,
        xor4_eq _ hpa, loadMemory_model, storeFPR64_model, abs_Mem]
      rw [abs_mkNext_writeFpD _ _ _ $hfsz]
      simp only [complete_plain]
      rfl
  · have hm : (bits $va 2 0 != 0#3) = true := by rw [misaligned8_eq]; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hal, ne_eq, not_false_eq_true]
    rw [gep_adel]))

/-- The tail of `SDC1` after the effective address `va`. -/
macro "sd_fp_tail" s:ident va:ident : tactic => `(tactic| (
  by_cases hal : ($va).toNat % 8 = 0
  · have hm : (bits $va 2 0 != 0#3) = false := by rw [misaligned8_eq]; simp [hal]
    have hpa := fixedMappingPA_aligned8 (erlSet $s) $va hal
    simp only [hm, Bool.false_eq_true, ↓reduceIte, hal, ne_eq, not_true_eq_false]
    rw [addrTrans_run $s $va .DATA .STORE _ _ rfl, writeMemWord_eq $s $va _ (aligned4_of_8 hal)]
    have hacc : ∀ m, accessAllowed { $s with physMem := m } $va = accessAllowed $s $va := fun _ => rfl
    have herl : ∀ m, erlSet { $s with physMem := m } = erlSet $s := fun _ => rfl
    unfold translate
    cases hA : accessAllowed $s $va
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
      rw [gep_ades]
    · simp only [↓reduceIte, Option.map_some]
      rw [writeMemWord_eq _ ($va + 4#32) _ (aligned4_add4 hal), translate_add4 _ $va hal]
      unfold translate
      simp only [hacc, herl, hA, ↓reduceIte, Option.map_some]
      have hst : ∀ a, modelCtx.oracle.storeClearsLL a = true := fun _ => rfl
      simp only [valueFPR64_model, Pseudo.get, endian_xor, BitVec.xor_zero, xor4_eq _ hpa,
        StoreMemory, bind, Pseudo.oracle, Pseudo.modify, abs_Mem, hst, bits,
        Nat.reduceAdd, Nat.reduceSub, append_lo, append_hi,
        storeWord_ins4 _ _ _ (aligned4_add4 hpa), storeWord_ins4 _ _ _ (aligned4_of_8 hpa)]
      rw [complete_plain, mkNext, abs_advance _ _ (by rfl), readFpD_abs]
      rfl
  · have hm : (bits $va 2 0 != 0#3) = true := by rw [misaligned8_eq]; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hal, ne_eq, not_false_eq_true]
    rw [gep_ades]))

/-- **LWC1 refines.** -/
theorem lwc1_refines (s : State) (hg : Good s) (base ft off w : W32)
    (hw : enc (.lwc1 base ft off) = some w) :
    Execute modelCtx w (.lwc1 base ft off) (abs s) = some (abs (execInstr s (.lwc1 base ft off))) := by
  obtain ⟨-, hfsz, h0⟩ := hg
  have hw' : w = iFormat 0x31#32 base ft off := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.LWC1 base ft off) rfl (by simp [InCop1Space, opcode_iFormat])
    (by simp [InCop0Space, opcode_iFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.lwc1 base ft off) =
      (match readMemWord s (readReg s (regIdx base) + signExt16 off) with
       | none => takeAddressException s excCodeAdEL (readReg s (regIdx base) + signExt16 off)
       | some v => mkNext s (writeFpReg s (regIdx ft) v)) := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.LWC1, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, offset16]
  rw [BitVec.add_comm (signExt16 off)]
  generalize readReg s (regIdx base) + signExt16 off = va
  lw_fp_tail s va hfsz

/-- **SWC1 refines.** -/
theorem swc1_refines (s : State) (hg : Good s) (base ft off w : W32)
    (hw : enc (.swc1 base ft off) = some w) :
    Execute modelCtx w (.swc1 base ft off) (abs s) = some (abs (execInstr s (.swc1 base ft off))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = iFormat 0x39#32 base ft off := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.SWC1 base ft off) rfl (by simp [InCop1Space, opcode_iFormat])
    (by simp [InCop0Space, opcode_iFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.swc1 base ft off) =
      (match writeMemWord s (readReg s (regIdx base) + signExt16 off) (readFpReg s (regIdx ft)) with
       | none => takeAddressException s excCodeAdES (readReg s (regIdx base) + signExt16 off)
       | some s' => mkNext s { s' with llBit := false }) := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.SWC1, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, offset16]
  rw [BitVec.add_comm (signExt16 off)]
  generalize readReg s (regIdx base) + signExt16 off = va
  sw_fp_tail s va

/-- **LDC1 refines** (one 64-bit FPR, `Status.FR = 1`). -/
theorem ldc1_refines (s : State) (hg : Good s) (base ft off w : W32)
    (hw : enc (.ldc1 base ft off) = some w) :
    Execute modelCtx w (.ldc1 base ft off) (abs s) = some (abs (execInstr s (.ldc1 base ft off))) := by
  obtain ⟨-, hfsz, h0⟩ := hg
  have hw' : w = iFormat 0x35#32 base ft off := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.LDC1 base ft off) rfl (by simp [InCop1Space, opcode_iFormat])
    (by simp [InCop0Space, opcode_iFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.ldc1 base ft off) =
      (if (readReg s (regIdx base) + signExt16 off).toNat % 8 ≠ 0 then
        takeAddressException s excCodeAdEL (readReg s (regIdx base) + signExt16 off)
      else
      match readMemWord s (readReg s (regIdx base) + signExt16 off),
          readMemWord s (readReg s (regIdx base) + signExt16 off + 4#32) with
      | some lo, some hi => mkNext s (writeFpD s ft (hi ++ lo))
      | _, _ => takeAddressException s excCodeAdEL (readReg s (regIdx base) + signExt16 off)) := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.LDC1, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, offset16]
  rw [BitVec.add_comm (signExt16 off)]
  generalize readReg s (regIdx base) + signExt16 off = va
  ld_fp_tail s va hfsz

/-- **SDC1 refines** (one 64-bit FPR, `Status.FR = 1`). -/
theorem sdc1_refines (s : State) (hg : Good s) (base ft off w : W32)
    (hw : enc (.sdc1 base ft off) = some w) :
    Execute modelCtx w (.sdc1 base ft off) (abs s) = some (abs (execInstr s (.sdc1 base ft off))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = iFormat 0x3D#32 base ft off := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.SDC1 base ft off) rfl (by simp [InCop1Space, opcode_iFormat])
    (by simp [InCop0Space, opcode_iFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.sdc1 base ft off) =
      (if (readReg s (regIdx base) + signExt16 off).toNat % 8 ≠ 0 then
        takeAddressException s excCodeAdES (readReg s (regIdx base) + signExt16 off)
      else
      match writeMemWord s (readReg s (regIdx base) + signExt16 off)
          ((readFpD s ft).extractLsb' 0 32) with
      | none => takeAddressException s excCodeAdES (readReg s (regIdx base) + signExt16 off)
      | some s' =>
        match writeMemWord s' (readReg s (regIdx base) + signExt16 off + 4#32)
            ((readFpD s ft).extractLsb' 32 32) with
        | none => takeAddressException s excCodeAdES (readReg s (regIdx base) + signExt16 off)
        | some s'' => mkNext s { s'' with llBit := false }) := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.SDC1, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, offset16]
  rw [BitVec.add_comm (signExt16 off)]
  generalize readReg s (regIdx base) + signExt16 off = va
  sd_fp_tail s va

end Refine
