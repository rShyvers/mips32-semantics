import Semantics.Refine.BridgeMem

/-!
# Refine.Memory — aligned loads and stores against `execInstr`

The pilots `lw` and `sw`: the pre-Release-6 alignment check, the address check and
Fixed Mapping translation (`Refine/Fetch.lean`), and the memory element read or written.
-/

namespace Refine

open Manual

/-- **LW refines.** -/
theorem lw_refines (s : State) (hg : Good s) (base rt off w : W32)
    (hw : enc (.lw base rt off) = some w) :
    Execute modelCtx w (.lw base rt off) (abs s) = some (abs (execInstr s (.lw base rt off))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = iFormat 0x23#32 base rt off := by
    have : enc (.lw base rt off) = some (iFormat 0x23#32 base rt off) := rfl
    rw [this] at hw; exact (Option.some.inj hw).symm
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_iFormat]
  have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_iFormat]
  have hex : execInstr s (.lw base rt off) =
      (match readMemWord s (readReg s (regIdx base) + signExt16 off) with
       | none => takeAddressException s excCodeAdEL (readReg s (regIdx base) + signExt16 off)
       | some v => mkNext s (writeReg s (regIdx rt) v)) := by
    have h1 : isBranchLike (.lw base rt off) = false := rfl
    have h2 : usesCop1 (.lw base rt off) = false := rfl
    have h3 : usesCop0 (.lw base rt off) = false := rfl
    unfold execInstr; rw [h1, h2, h3]; rfl
  rw [hex, execute_run modelCtx w _ _ (Ops.LW base rt off) rfl hc1 hc0 rfl]
  simp only [Pseudo.run, Ops.LW, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, offset16]
  rw [BitVec.add_comm (signExt16 off)]
  generalize readReg s (regIdx base) + signExt16 off = va
  by_cases hal : va.toNat % 4 = 0
  · have hm : (bits va 1 0 != 0#2) = false := by rw [misaligned_eq]; simp [hal]
    simp only [hm, Bool.false_eq_true, ↓reduceIte]
    rw [addrTrans_run s va .DATA .LOAD _ _ rfl, readMemWord_eq s va hal]
    unfold translate
    cases accessAllowed s va
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
      rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_adel]
    · simp only [↓reduceIte, Option.map_some, loadMemory_model, setGPR, abs_Mem]
      rw [complete_plain, mkNext, abs_advance _ _ (by unfold writeReg; split <;> rfl),
        abs_writeReg _ _ _ hsz]
      have hpc : ∀ v, (writeReg s (regIdx rt) v).pc = s.pc := by
        intro v; unfold writeReg; split <;> rfl
      rw [hpc]; rfl
  · have hm : (bits va 1 0 != 0#2) = true := by rw [misaligned_eq]; simp [hal]
    have hr : readMemWord s va = none := by unfold readMemWord; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hr]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_adel]

theorem low2_of_aligned (pa : W32) (h : pa.toNat % 4 = 0) : (pa &&& 3#32).toNat = 0 := by
  rw [BitVec.toNat_and, show (3#32).toNat = 2 ^ 2 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact h

/-- **`StoreMemory` of a word against `writeMemWord`**: the four bytes at the aligned physical
address, in the profile's byte order (`byteOfValue`). -/
theorem storeWord_mem (m : Std.HashMap PAddr UInt8) (pa : PAddr) (v : W32) (h : pa.toNat % 4 = 0) :
    (storedLanes (pa &&& 3#32).toNat WORD).foldl
        (fun mm l => updMem mm ((pa &&& ~~~3#32) + BitVec.ofNat 32 l) (laneByte v l)) (memOf m) =
      memOf ((((m.insert pa (byteOfValue profile.bigEndianMem 4 v 0)).insert (pa + 1#32)
        (byteOfValue profile.bigEndianMem 4 v 1)).insert (pa + 2#32)
        (byteOfValue profile.bigEndianMem 4 v 2)).insert (pa + 3#32)
        (byteOfValue profile.bigEndianMem 4 v 3)) := by
  rw [base_of_aligned pa h, low2_of_aligned pa h]
  simp only [memOf_insert]
  rw [show storedLanes 0 WORD = [0, 1, 2, 3] by rfl]
  simp only [List.foldl, laneByte_eq v 0 (by omega), laneByte_eq v 1 (by omega),
    laneByte_eq v 2 (by omega), laneByte_eq v 3 (by omega)]
  simp only [BitVec.add_zero]

/-- **SW refines.** -/
theorem sw_refines (s : State) (hg : Good s) (base rt off w : W32)
    (hw : enc (.sw base rt off) = some w) :
    Execute modelCtx w (.sw base rt off) (abs s) = some (abs (execInstr s (.sw base rt off))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = iFormat 0x2B#32 base rt off := by
    have : enc (.sw base rt off) = some (iFormat 0x2B#32 base rt off) := rfl
    rw [this] at hw; exact (Option.some.inj hw).symm
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_iFormat]
  have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_iFormat]
  have hex : execInstr s (.sw base rt off) =
      (match writeMemWord s (readReg s (regIdx base) + signExt16 off) (readReg s (regIdx rt)) with
       | none => takeAddressException s excCodeAdES (readReg s (regIdx base) + signExt16 off)
       | some s' => mkNext s { s' with llBit := false }) := by
    have h1 : isBranchLike (.sw base rt off) = false := rfl
    have h2 : usesCop1 (.sw base rt off) = false := rfl
    have h3 : usesCop0 (.sw base rt off) = false := rfl
    unfold execInstr; rw [h1, h2, h3]; rfl
  rw [hex, execute_run modelCtx w _ _ (Ops.SW base rt off) rfl hc1 hc0 rfl]
  simp only [Pseudo.run, Ops.SW, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, offset16]
  rw [BitVec.add_comm (signExt16 off)]
  generalize readReg s (regIdx base) + signExt16 off = va
  by_cases hal : va.toNat % 4 = 0
  · have hm : (bits va 1 0 != 0#2) = false := by rw [misaligned_eq]; simp [hal]
    simp only [hm, Bool.false_eq_true, ↓reduceIte]
    rw [addrTrans_run s va .DATA .STORE _ _ rfl]
    unfold writeMemWord translate
    simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte]
    cases accessAllowed s va
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_ades]
    · simp only [↓reduceIte, StoreMemory, bind, Pseudo.oracle, Pseudo.modify, abs_Mem]
      have hst : modelCtx.oracle.storeClearsLL (abs s) = true := rfl
      simp only [hst, ↓reduceIte]
      rw [storeWord_mem _ _ _ (fixedMappingPA_aligned _ _ hal)]
      rw [readGPR_abs s h0, complete_plain, mkNext, abs_advance _ _ (by rfl)]
      rfl
  · have hm : (bits va 1 0 != 0#2) = true := by rw [misaligned_eq]; simp [hal]
    have hr : ∀ v, writeMemWord s va v = none := by intro v; unfold writeMemWord; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hr]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_ades]

/-! ## The byte and halfword loads and stores, PREF, SYNC, SYNCI -/

/-- **LB refines.** -/
theorem lb_refines (s : State) (hg : Good s) (base rt off w : W32)
    (hw : enc (.lb base rt off) = some w) :
    Execute modelCtx w (.lb base rt off) (abs s) = some (abs (execInstr s (.lb base rt off))) := by
  s2_open Ops.LB (Ops.LB base rt off)
  exec_unfold
  rw [BitVec.add_comm (signExt16 off)]
  generalize hva : readReg s (regIdx base) + signExt16 off = va
  rw [addrTrans_run s va .DATA .LOAD _ _ rfl, readMemByte_eq]
  unfold translate
  cases accessAllowed s va
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_adel]
  · simp only [↓reduceIte, Option.map_some, Pseudo.get, loadMemory_model, ReverseEndian, StatusRE,
      Bool.false_and, abs_Mem, setGPR, addr_recombine]
    rw [show BigEndianCPU (abs s) = false from rfl, byte_idx, ← fixedMappingPA_low (erlSet s) va,
      memElem_byte, complete_writeReg_eq s hg.1, signExtByte_eq]

/-- **LBU refines.** -/
theorem lbu_refines (s : State) (hg : Good s) (base rt off w : W32)
    (hw : enc (.lbu base rt off) = some w) :
    Execute modelCtx w (.lbu base rt off) (abs s) = some (abs (execInstr s (.lbu base rt off))) := by
  s2_open Ops.LBU (Ops.LBU base rt off)
  exec_unfold
  rw [BitVec.add_comm (signExt16 off)]
  generalize readReg s (regIdx base) + signExt16 off = va
  rw [addrTrans_run s va .DATA .LOAD _ _ rfl, readMemByte_eq]
  unfold translate
  cases accessAllowed s va
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_adel]
  · simp only [↓reduceIte, Option.map_some, Pseudo.get, loadMemory_model, ReverseEndian, StatusRE,
      Bool.false_and, abs_Mem, setGPR, addr_recombine]
    rw [show BigEndianCPU (abs s) = false from rfl, byte_idx, ← fixedMappingPA_low (erlSet s) va,
      memElem_byte, complete_writeReg_eq s hg.1, zeroExtByte_eq]

/-- **LH refines.** -/
theorem lh_refines (s : State) (hg : Good s) (base rt off w : W32)
    (hw : enc (.lh base rt off) = some w) :
    Execute modelCtx w (.lh base rt off) (abs s) = some (abs (execInstr s (.lh base rt off))) := by
  s2_open Ops.LH (Ops.LH base rt off)
  exec_unfold
  rw [BitVec.add_comm (signExt16 off)]
  generalize readReg s (regIdx base) + signExt16 off = va
  by_cases hal : va.toNat % 2 = 0
  · have hm : bit va 0 = false := by rw [misaligned2_eq]; simp [hal]
    simp only [hm, Bool.false_eq_true, ↓reduceIte]
    rw [addrTrans_run s va .DATA .LOAD _ _ rfl]
    unfold readMemHalf translate
    simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte]
    cases accessAllowed s va
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_adel]
    · simp only [↓reduceIte, Pseudo.get, loadMemory_model, ReverseEndian, StatusRE,
        Bool.false_and, abs_Mem, setGPR, addr_recombine_half]
      have hP := fixedMappingPA_low (erlSet s) va
      rw [show BigEndianCPU (abs s) = false from rfl, half_idx va, ← hP,
        memElem_half _ _ (by omega), complete_writeReg_eq s hg.1, signExt16_half]
      rfl
  · have hm : bit va 0 = true := by rw [misaligned2_eq]; simp [hal]
    have hr : readMemHalf s va = none := by unfold readMemHalf; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hr]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_adel]

/-- **LHU refines.** -/
theorem lhu_refines (s : State) (hg : Good s) (base rt off w : W32)
    (hw : enc (.lhu base rt off) = some w) :
    Execute modelCtx w (.lhu base rt off) (abs s) = some (abs (execInstr s (.lhu base rt off))) := by
  s2_open Ops.LHU (Ops.LHU base rt off)
  exec_unfold
  rw [BitVec.add_comm (signExt16 off)]
  generalize readReg s (regIdx base) + signExt16 off = va
  by_cases hal : va.toNat % 2 = 0
  · have hm : bit va 0 = false := by rw [misaligned2_eq]; simp [hal]
    simp only [hm, Bool.false_eq_true, ↓reduceIte]
    rw [addrTrans_run s va .DATA .LOAD _ _ rfl]
    unfold readMemHalf translate
    simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte]
    cases accessAllowed s va
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_adel]
    · simp only [↓reduceIte, Pseudo.get, loadMemory_model, ReverseEndian, StatusRE,
        Bool.false_and, abs_Mem, setGPR, addr_recombine_half]
      have hP := fixedMappingPA_low (erlSet s) va
      rw [show BigEndianCPU (abs s) = false from rfl, half_idx va, ← hP,
        memElem_half _ _ (by omega), complete_writeReg_eq s hg.1, half_bits]
      rfl
  · have hm : bit va 0 = true := by rw [misaligned2_eq]; simp [hal]
    have hr : readMemHalf s va = none := by unfold readMemHalf; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hr]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_adel]

/-- **PREF refines.** -/
theorem pref_refines (s : State) (hg : Good s) (base hint off w : W32)
    (hw : enc (.pref base hint off) = some w) :
    Execute modelCtx w (.pref base hint off) (abs s) = some (abs (execInstr s (.pref base hint off))) := by
  s2_open Ops.PREF (Ops.PREF base hint off)
  exec_unfold
  -- hints 24..31 raise Reserved Instruction (PREF, Table 5.2, p.322-323)
  have e : (low hint 5).toNat = (hint &&& 31#32).toNat := by
    rw [low5, BitVec.toNat_and, show (31#32).toNat = 2 ^ 5 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [e]
  by_cases hc : 24 ≤ (hint &&& 31#32).toNat
  · simp only [hc, ↓reduceIte, SignalException]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl,
      gep_take s .ReservedInstruction rfl excCodeRI (by decide)]
  · simp only [hc, ↓reduceIte, pure]
    exact congrArg some (complete_nop s)

/-- **SYNC refines.** -/
theorem sync_refines (s : State) (hg : Good s) (stype w : W32)
    (hw : enc (.sync stype) = some w) :
    Execute modelCtx w (.sync stype) (abs s) = some (abs (execInstr s (.sync stype))) := by
  s2_open Ops.SYNC (Ops.SYNC stype)
  exact congrArg some (complete_nop s)

/-- **SYNCI refines.** -/
theorem synci_refines (s : State) (hg : Good s) (base off w : W32)
    (hw : enc (.synci base off) = some w) :
    Execute modelCtx w (.synci base off) (abs s) = some (abs (execInstr s (.synci base off))) := by
  s2_open Ops.SYNCI (Ops.SYNCI base off)
  simp only [Pseudo.impl, Pseudo.get, show modelCtx.impl.SynciAddressError = false from rfl,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  exact congrArg some (complete_nop s)


/-- **SB refines.** -/
theorem sb_refines (s : State) (hg : Good s) (base rt off w : W32)
    (hw : enc (.sb base rt off) = some w) :
    Execute modelCtx w (.sb base rt off) (abs s) = some (abs (execInstr s (.sb base rt off))) := by
  s2_open Ops.SB (Ops.SB base rt off)
  exec_unfold
  have hcomm : signExt16 off + readReg s (regIdx base) = readReg s (regIdx base) + signExt16 off :=
    BitVec.add_comm _ _
  rw [hcomm]
  generalize hva : readReg s (regIdx base) + signExt16 off = va
  rw [addrTrans_run s va .DATA .STORE _ _ rfl]
  unfold writeMemByte translate
  cases accessAllowed s va
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_ades]
  · simp only [↓reduceIte, Pseudo.get, ReverseEndian, StatusRE, StoreMemory, bind, Pseudo.oracle,
      Pseudo.modify, Bool.false_and, abs_Mem, addr_recombine, readGPR_abs s h0,
      show modelCtx.oracle.storeClearsLL (abs s) = true from rfl, store_byte_fold]
    generalize hB : (bits (sign_extend (imm16 off) + readReg s (regIdx base)) 1 0 ^^^
      BitVec.fill 2 (BigEndianCPU (abs s))).toNat = byte
    rw [offset16, hcomm, hva, show BigEndianCPU (abs s) = false from rfl, byte_idx,
      ← fixedMappingPA_low (erlSet s) va] at hB
    subst hB
    rw [lane_sb _ _ (Nat.mod_lt _ (by omega)), complete_plain, mkNext, abs_advance _ _ (by rfl)]
    simp only [abs, memOf_insert]
    rfl


/-- **SH refines.** -/
theorem sh_refines (s : State) (hg : Good s) (base rt off w : W32)
    (hw : enc (.sh base rt off) = some w) :
    Execute modelCtx w (.sh base rt off) (abs s) = some (abs (execInstr s (.sh base rt off))) := by
  s2_open Ops.SH (Ops.SH base rt off)
  exec_unfold
  have hcomm : signExt16 off + readReg s (regIdx base) = readReg s (regIdx base) + signExt16 off :=
    BitVec.add_comm _ _
  rw [hcomm]
  generalize hva : readReg s (regIdx base) + signExt16 off = va
  by_cases hal : va.toNat % 2 = 0
  · have hm : bit va 0 = false := by rw [misaligned2_eq]; simp [hal]
    simp only [hm, Bool.false_eq_true, ↓reduceIte]
    rw [addrTrans_run s va .DATA .STORE _ _ rfl]
    unfold writeMemHalf translate
    simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte]
    cases accessAllowed s va
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_ades]
    · have hP := fixedMappingPA_low (erlSet s) va
      simp only [↓reduceIte, Pseudo.get, ReverseEndian, StatusRE, StoreMemory, bind, Pseudo.oracle,
        Pseudo.modify, Bool.false_and, abs_Mem, addr_recombine_half, readGPR_abs s h0,
        show modelCtx.oracle.storeClearsLL (abs s) = true from rfl, store_half_fold _ _ _ (by omega : (fixedMappingPA (erlSet s) va).toNat % 2 = 0)]
      generalize hB : (bits (sign_extend (imm16 off) + readReg s (regIdx base)) 1 0 ^^^
        (BitVec.ofBool (BigEndianCPU (abs s)) ++ 0#1)).toNat = byte
      rw [offset16, hcomm, hva, show BigEndianCPU (abs s) = false from rfl, half_idx va, ← hP] at hB
      subst hB
      have hl := lane_sh (readReg s (regIdx rt)) _ (by omega : (fixedMappingPA (erlSet s) va).toNat % 4 = 0 ∨ (fixedMappingPA (erlSet s) va).toNat % 4 = 2)
      rw [hl.1, hl.2, complete_plain, mkNext, abs_advance _ _ (by rfl)]
      simp only [abs, memOf_insert]
      rfl
  · have hm : bit va 0 = true := by rw [misaligned2_eq]; simp [hal]
    have hr : ∀ v, writeMemHalf s va v = none := by intro v; unfold writeMemHalf; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hr]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_ades]

end Refine
