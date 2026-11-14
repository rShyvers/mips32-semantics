import Semantics.Refine.Memory

/-!
# Refine.Atomic — LL and SC against `execInstr` (7C S2)

`LL` (MD00086 Vol II-A Rev 6.06, LL, p.223-224) loads like `LW` and starts the RMW sequence
(`LLbit ← 1`, `LLAddr ← vAddr`); the model's `ll` the same. Under the model's oracle a load does not
clear `LLbit` (`Oracle.loadClearsLL`, `loadMemory_model`) and a store does (`Oracle.storeClearsLL`).

`SC` (SC, p.347-349) stores if `atomic_update`, which the transcription reads as `LLbit` and the
aligned addresses `vAddr31..2 = LLAddr31..2` (p.347: "An SC will fail if the aligned address of the
SC does not match that of the preceding LL"); since 7D part 1 the model compares the same bits,
`s.llAddr >>> 2 == addr >>> 2`, so `sc_refines` holds for every state (7C S2 had a hypothesis
`s.llAddr.toNat % 4 = 0` while the model compared the whole addresses; dropped in 7D part 2).
-/

namespace Refine

open Manual

theorem abs_ll (s : State) (hsz : s.regs.size = 32) (i : Fin 32) (v va : W32) :
    abs { writeReg s i v with llBit := true, llAddr := va } =
      { writeGPR (abs s) i v with LLbit := true, LLAddr := va } := by
  rw [← abs_writeReg _ _ _ hsz]; rfl

/-- **LL refines.** -/
theorem ll_refines (s : State) (hg : Good s) (base rt off w : W32)
    (hw : enc (.ll base rt off) = some w) :
    Execute modelCtx w (.ll base rt off) (abs s) = some (abs (execInstr s (.ll base rt off))) := by
  s2_open Ops.LL (Ops.LL base rt off)
  simp only [execBody]
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
    · simp only [↓reduceIte, Option.map_some, loadMemory_model, setGPR, abs_Mem, Pseudo.modify]
      rw [complete_plain, mkNext,
        abs_advance s { writeReg s (regIdx rt) _ with llBit := true, llAddr := va } (writeReg_pb _ _ _),
        abs_ll s hg.1]
      simp only [writeReg_pc]
      rfl
  · have hm : (bits va 1 0 != 0#2) = true := by rw [misaligned_eq]; simp [hal]
    have hr : readMemWord s va = none := by unfold readMemWord; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hr]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_adel]

theorem abs_sc (r : State) (hsz : r.regs.size = 32) (i : Fin 32) (v : W32) :
    abs { writeReg r i v with llBit := false } = { writeGPR (abs r) i v with LLbit := false } := by
  rw [← abs_writeReg _ _ _ hsz]; rfl

theorem abs_mkNext_sc (s r : State) (hsz : r.regs.size = 32) (hpc : r.pc = s.pc)
    (hpb : r.pendingBranch = s.pendingBranch) (i : Fin 32) (v : W32) :
    abs (mkNext s { writeReg r i v with llBit := false }) =
      { ({ writeGPR (abs r) i v with LLbit := false } : Arch) with
        PC := s.pendingBranch.getD (s.pc + 4#32), BranchDelay := none } := by
  rw [mkNext, abs_advance s _ (by rw [← hpb]; exact writeReg_pb _ _ _), abs_sc _ hsz]
  simp only [writeReg_pc, hpc]

/-- The manual's aligned-address test (bits 31..2) is the model's comparison of the words
`>>> 2`. -/
theorem aligned_word_eq (x y : W32) : (bits x 31 2 == bits y 31 2) = (y >>> 2 == x >>> 2) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  have hx := x.isLt; have hy := y.isLt
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    simp only [bits, BitVec.extractLsb'_toNat] at h'
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  · intro h
    have h' := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h'
    apply BitVec.eq_of_toNat_eq
    simp only [bits, BitVec.extractLsb'_toNat]; omega

/-- **SC refines.** -/
theorem sc_refines (s : State) (hg : Good s) (base rt off w : W32)
    (hw : enc (.sc base rt off) = some w) :
    Execute modelCtx w (.sc base rt off) (abs s) = some (abs (execInstr s (.sc base rt off))) := by
  s2_open Ops.SC (Ops.SC base rt off)
  simp only [execBody]
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
    · simp only [↓reduceIte, Pseudo.get, show (abs s).LLbit = s.llBit from rfl,
        show (abs s).LLAddr = s.llAddr from rfl, aligned_word_eq va s.llAddr]
      cases hc : (s.llBit && s.llAddr >>> 2 == va >>> 2)
      · simp only [Bool.false_eq_true, ↓reduceIte, setGPR, Pseudo.modify]
        rw [show (BitVec.setWidth 32 (0#31 ++ BitVec.ofBool false)) = 0#32 from rfl, complete_plain,
          mkNext, abs_advance s { writeReg s (regIdx rt) 0#32 with llBit := false } (writeReg_pb _ _ _),
          abs_sc s hg.1]
        simp only [writeReg_pc]
        rfl
      · simp only [↓reduceIte, StoreMemory, bind, Pseudo.oracle, Pseudo.modify, setGPR, abs_Mem,
          readGPR_abs s h0, show modelCtx.oracle.storeClearsLL (abs s) = true from rfl,
          storeWord_mem _ _ _ (fixedMappingPA_aligned _ _ hal)]
        rw [show (BitVec.setWidth 32 (0#31 ++ BitVec.ofBool true)) = 1#32 from rfl, complete_plain,
          abs_mkNext_sc s _ (by exact hg.1) (by rfl) (by rfl)]
        unfold writeGPR; split <;> rfl
  · have hm : (bits va 1 0 != 0#2) = true := by rw [misaligned_eq]; simp [hal]
    have hr : ∀ v, writeMemWord s va v = none := by intro v; unfold writeMemWord; simp [hal]
    simp only [hm, ↓reduceIte, SignalException, hr]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_ades]

end Refine
