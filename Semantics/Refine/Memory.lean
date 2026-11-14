import Semantics.Refine.Fetch

/-!
# Refine.Memory — aligned loads and stores against `execInstr`

Sub-wave 7A proves the pilots `lw` and `sw`: the pre-Release-6 alignment check, the address check and
Fixed Mapping translation (`Refine/Fetch.lean`), and the memory element read or written.
-/

namespace Refine

open Manual

theorem gep_adel (s : State) (va : W32) :
    GeneralExceptionProcessing modelOracle (.AddressErrorLoad va) (abs s) =
      abs (takeAddressException s excCodeAdEL va) := by
  rw [gep_eq s _ (by intro h; cases h) (by intro u h; cases h)]; rfl

theorem gep_ades (s : State) (va : W32) :
    GeneralExceptionProcessing modelOracle (.AddressErrorStore va) (abs s) =
      abs (takeAddressException s excCodeAdES va) := by
  rw [gep_eq s _ (by intro h; cases h) (by intro u h; cases h)]; rfl

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
      rw [show modelCtx.oracle = modelOracle from rfl, gep_adel]
    · simp only [↓reduceIte, Option.map_some, LoadMemory, bind, Pseudo.get, pure, setGPR, abs_Mem]
      rw [complete_plain, mkNext, abs_advance _ _ (by unfold writeReg; split <;> rfl),
        abs_writeReg _ _ _ hsz]
      have hpc : ∀ v, (writeReg s (regIdx rt) v).pc = s.pc := by
        intro v; unfold writeReg; split <;> rfl
      rw [hpc]; rfl
  · have hm : (bits va 1 0 != 0#2) = true := by rw [misaligned_eq]; simp [hal]
    have hr : readMemWord s va = none := by unfold readMemWord; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hr]
    rw [show modelCtx.oracle = modelOracle from rfl, gep_adel]

theorem low2_of_aligned (pa : W32) (h : pa.toNat % 4 = 0) : (pa &&& 3#32).toNat = 0 := by
  rw [BitVec.toNat_and, show (3#32).toNat = 2 ^ 2 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact h

/-- **`StoreMemory` of a word against `writeMemWord`**: the four bytes at the aligned physical
address, most significant first. -/
theorem storeWord_mem (m : Std.HashMap PAddr UInt8) (pa : PAddr) (v : W32) (h : pa.toNat % 4 = 0) :
    (List.range (WORD + 1)).foldl
        (fun mm j => updMem mm ((pa &&& ~~~3#32) + BitVec.ofNat 32 ((pa &&& 3#32).toNat + j))
          (laneByte v ((pa &&& 3#32).toNat + j))) (memOf m) =
      memOf ((((m.insert pa ((v >>> 24) &&& 0xff#32).toNat.toUInt8).insert (pa + 1#32)
        ((v >>> 16) &&& 0xff#32).toNat.toUInt8).insert (pa + 2#32) ((v >>> 8) &&& 0xff#32).toNat.toUInt8).insert
        (pa + 3#32) (v &&& 0xff#32).toNat.toUInt8) := by
  rw [base_of_aligned pa h, low2_of_aligned pa h]
  simp only [memOf_insert]
  rw [show List.range (WORD + 1) = [0, 1, 2, 3] by rfl]
  simp only [List.foldl, Nat.zero_add, laneByte_eq v 0 (by omega), laneByte_eq v 1 (by omega),
    laneByte_eq v 2 (by omega), laneByte_eq v 3 (by omega)]
  simp only [Nat.reduceMul, Nat.reduceSub, BitVec.add_zero, BitVec.ushiftRight_zero]

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
      rw [show modelCtx.oracle = modelOracle from rfl, gep_ades]
    · simp only [↓reduceIte, StoreMemory, bind, Pseudo.oracle, Pseudo.modify, abs_Mem]
      have hst : modelCtx.oracle.storeClearsLL (abs s) = true := rfl
      simp only [hst, ↓reduceIte]
      rw [storeWord_mem _ _ _ (fixedMappingPA_aligned _ _ hal)]
      rw [readGPR_abs s h0, complete_plain, mkNext, abs_advance _ _ (by rfl)]
      rfl
  · have hm : (bits va 1 0 != 0#2) = true := by rw [misaligned_eq]; simp [hal]
    have hr : ∀ v, writeMemWord s va v = none := by intro v; unfold writeMemWord; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hr]
    rw [show modelCtx.oracle = modelOracle from rfl, gep_ades]

end Refine
