import Semantics.Refine.BridgeFpuMove

/-!
# Refine.FpuMemory — FP loads and stores against `execInstr` (7C S4b)

`LWC1`, `SWC1`, `LDC1`, `SDC1`, `LWXC1`, `SWXC1`, `LDXC1`, `SDXC1`, `PREFX`. The pre-Release 6 alignment
check (word: `vAddr1..0`, doubleword: `vAddr2..0`; an Address Error with `BadVAddr = vAddr`), the
address check and Fixed Mapping translation (`Refine/Fetch.lean`), then the memory elements. The
doubleword pages access the word at `pAddr xor 0b100` first (`BigEndianCPU = 1`, `endian_xor`): for
a load that is the least-significant word (`FPR[ft]`), for a store the word stored first; the
model's two word stores are in the other order, and they commute (`memOf_ins4_swap`).
-/

namespace Refine

open Manual

-- The memory images are compared through `memOf_ins4_swap`/`storeWord_ins4`; keeping `ins4` and
-- `memOf` folded makes the final `rfl` of the store proofs cheap.
attribute [local irreducible] ins4 memOf

/-- The tail of `LWC1`/`LWXC1` after the effective address `va`. -/
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

/-- The tail of `SWC1`/`SWXC1` after the effective address `va`. -/
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

/-- The tail of `LDC1`/`LDXC1` after the effective address `va`. -/
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
    · simp only [↓reduceIte, Option.map_some, Pseudo.get, endian_xor, xor4_eq _ hpa,
        loadMemory_model, xor4_xor4 _ hpa, storeFPR64_model, abs_Mem]
      rw [writeFpReg2_eq, abs_mkNext_writeFpD _ _ _ $hfsz]
      simp only [complete_plain, append_lo, append_hi]
      rfl
  · have hm : (bits $va 2 0 != 0#3) = true := by rw [misaligned8_eq]; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hal, ne_eq, not_false_eq_true]
    rw [gep_adel]))

/-- The tail of `SDC1`/`SDXC1` after the effective address `va`. -/
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
      simp only [valueFPR64_model, Pseudo.get, endian_xor, xor4_eq _ hpa,
        StoreMemory, bind, Pseudo.oracle, Pseudo.modify, abs_Mem, hst, xor4_xor4 _ hpa, bits,
        Nat.reduceAdd, Nat.reduceSub, append_lo, append_hi,
        storeWord_ins4 _ _ _ (aligned4_add4 hpa), storeWord_ins4 _ _ _ (aligned4_of_8 hpa)]
      rw [memOf_ins4_swap, regIdx_succ, complete_plain, mkNext, abs_advance _ _ (by rfl)]
      simp only [regIdx_eq_reg, ite_true, abs_FPR]
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

/-- **LDC1 refines** (odd `ft`: `Oracle.fprOddWrite`, the model's pair `ft`, `ft + 1`). -/
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
      | some hi, some lo =>
        mkNext s (writeFpReg (writeFpReg s (regIdx ft) lo) (regIdx (ft + 1#32)) hi)
      | _, _ => takeAddressException s excCodeAdEL (readReg s (regIdx base) + signExt16 off)) := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.LDC1, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, offset16]
  rw [BitVec.add_comm (signExt16 off)]
  generalize readReg s (regIdx base) + signExt16 off = va
  ld_fp_tail s va hfsz

/-- **SDC1 refines** (odd `ft`: `Oracle.fprOddRead`). -/
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
          (readFpReg s (regIdx (ft + 1#32))) with
      | none => takeAddressException s excCodeAdES (readReg s (regIdx base) + signExt16 off)
      | some s' =>
        match writeMemWord s' (readReg s (regIdx base) + signExt16 off + 4#32)
            (readFpReg s (regIdx ft)) with
        | none => takeAddressException s excCodeAdES (readReg s (regIdx base) + signExt16 off)
        | some s'' => mkNext s { s'' with llBit := false }) := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.SDC1, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, offset16]
  rw [BitVec.add_comm (signExt16 off)]
  generalize readReg s (regIdx base) + signExt16 off = va
  sd_fp_tail s va

/-- **LWXC1 refines.** -/
theorem lwxc1_refines (s : State) (hg : Good s) (fd index base w : W32)
    (hw : enc (.lwxc1 fd index base) = some w) :
    Execute modelCtx w (.lwxc1 fd index base) (abs s) =
      some (abs (execInstr s (.lwxc1 fd index base))) := by
  obtain ⟨-, hfsz, h0⟩ := hg
  have hw' : w = rFormat 0x13#32 base index 0#32 fd 0x00#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.LWXC1 fd index base) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.lwxc1 fd index base) =
      (match readMemWord s (readReg s (regIdx base) + readReg s (regIdx index)) with
       | none => takeAddressException s excCodeAdEL (readReg s (regIdx base) + readReg s (regIdx index))
       | some v => mkNext s (writeFpReg s (regIdx fd) v)) := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.LWXC1, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg]
  generalize readReg s (regIdx base) + readReg s (regIdx index) = va
  lw_fp_tail s va hfsz

/-- **SWXC1 refines.** -/
theorem swxc1_refines (s : State) (hg : Good s) (fs index base w : W32)
    (hw : enc (.swxc1 fs index base) = some w) :
    Execute modelCtx w (.swxc1 fs index base) (abs s) =
      some (abs (execInstr s (.swxc1 fs index base))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = rFormat 0x13#32 base index fs 0#32 0x08#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.SWXC1 fs index base) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.swxc1 fs index base) =
      (match writeMemWord s (readReg s (regIdx base) + readReg s (regIdx index))
          (readFpReg s (regIdx fs)) with
       | none => takeAddressException s excCodeAdES (readReg s (regIdx base) + readReg s (regIdx index))
       | some s' => mkNext s { s' with llBit := false }) := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.SWXC1, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg]
  generalize readReg s (regIdx base) + readReg s (regIdx index) = va
  sw_fp_tail s va

/-- **LDXC1 refines** (odd `fd`: `Oracle.fprOddWrite`). -/
theorem ldxc1_refines (s : State) (hg : Good s) (fd index base w : W32)
    (hw : enc (.ldxc1 fd index base) = some w) :
    Execute modelCtx w (.ldxc1 fd index base) (abs s) =
      some (abs (execInstr s (.ldxc1 fd index base))) := by
  obtain ⟨-, hfsz, h0⟩ := hg
  have hw' : w = rFormat 0x13#32 base index 0#32 fd 0x01#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.LDXC1 fd index base) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.ldxc1 fd index base) =
      (if (readReg s (regIdx base) + readReg s (regIdx index)).toNat % 8 ≠ 0 then
        takeAddressException s excCodeAdEL (readReg s (regIdx base) + readReg s (regIdx index))
      else
      match readMemWord s (readReg s (regIdx base) + readReg s (regIdx index)),
          readMemWord s (readReg s (regIdx base) + readReg s (regIdx index) + 4#32) with
      | some hi, some lo =>
        mkNext s (writeFpReg (writeFpReg s (regIdx fd) lo) (regIdx (fd + 1#32)) hi)
      | _, _ =>
        takeAddressException s excCodeAdEL (readReg s (regIdx base) + readReg s (regIdx index))) := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.LDXC1, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg]
  generalize readReg s (regIdx base) + readReg s (regIdx index) = va
  ld_fp_tail s va hfsz

/-- **SDXC1 refines** (odd `fs`: `Oracle.fprOddRead`). -/
theorem sdxc1_refines (s : State) (hg : Good s) (fs index base w : W32)
    (hw : enc (.sdxc1 fs index base) = some w) :
    Execute modelCtx w (.sdxc1 fs index base) (abs s) =
      some (abs (execInstr s (.sdxc1 fs index base))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = rFormat 0x13#32 base index fs 0#32 0x09#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.SDXC1 fs index base) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.sdxc1 fs index base) =
      (if (readReg s (regIdx base) + readReg s (regIdx index)).toNat % 8 ≠ 0 then
        takeAddressException s excCodeAdES (readReg s (regIdx base) + readReg s (regIdx index))
      else
      match writeMemWord s (readReg s (regIdx base) + readReg s (regIdx index))
          (readFpReg s (regIdx (fs + 1#32))) with
      | none => takeAddressException s excCodeAdES (readReg s (regIdx base) + readReg s (regIdx index))
      | some s' =>
        match writeMemWord s' (readReg s (regIdx base) + readReg s (regIdx index) + 4#32)
            (readFpReg s (regIdx fs)) with
        | none =>
          takeAddressException s excCodeAdES (readReg s (regIdx base) + readReg s (regIdx index))
        | some s'' => mkNext s { s'' with llBit := false }) := rfl
  rw [hb]
  simp only [Pseudo.run, Ops.SDXC1, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg]
  generalize readReg s (regIdx base) + readReg s (regIdx index) = va
  sd_fp_tail s va

/-- **PREFX refines**: no architectural effect on either side (PREF p.321). -/
theorem prefx_refines (s : State) (_hg : Good s) (hint index base w : W32)
    (hw : enc (.prefx hint index base) = some w) :
    Execute modelCtx w (.prefx hint index base) (abs s) =
      some (abs (execInstr s (.prefx hint index base))) := by
  have hw' : w = rFormat 0x13#32 base index hint 0#32 0x0F#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.PREFX hint index base) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.prefx hint index base) = mkNext s s := rfl
  rw [hb, abs_mkNext_self]
  simp only [Pseudo.run, Ops.PREFX, bind, GPR, pure, complete_plain]

end Refine
