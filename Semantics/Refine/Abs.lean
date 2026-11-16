import Semantics.Refine.Defs

/-!
# Refine.Abs — the model's state seen as the manual's state

`abs : State → Manual.Arch` (defined in `Refine/Defs.lean`) is a field-by-field projection: nothing is computed but the reading of
the register arrays (`readReg`, `readFpReg`) and of the physical-memory map (`HashMap.get?`, unwritten
bytes are 0). It is the bridge of the refinement theorems (`docs/MANUAL-SPEC.md`); it is not part of
the independent spec.

The projection lemmas `abs_*` rewrite the model's state primitives (`writeReg`, the memory writes,
record updates) into the manual's (`Manual.writeGPR`, `Manual.update`, functional memory), once, so
that the per-instruction refinement theorems never destructure `State`.
-/

namespace Refine

open Manual

/-! Projections of `abs` (by definition). -/

@[simp] theorem abs_PC (s : State) : (abs s).PC = s.pc := rfl
@[simp] theorem abs_GPR (s : State) (i : Fin 32) : (abs s).GPR i = readReg s i := rfl
@[simp] theorem abs_FPR (s : State) (i : Fin 32) : (abs s).FPR i = readFpReg64 s i := rfl
@[simp] theorem abs_FCSR (s : State) : (abs s).FCSR = s.fcsr := rfl
@[simp] theorem abs_Mem (s : State) : (abs s).Mem = memOf s.physMem := rfl
@[simp] theorem abs_Status (s : State) : (abs s).Status = s.cp0Status := rfl
@[simp] theorem abs_BranchDelay (s : State) : (abs s).BranchDelay = s.pendingBranch := rfl

/-! ## Register files -/

theorem readGPR_abs (s : State) (h0 : readReg s 0 = 0#32) (i : Fin 32) :
    readGPR (abs s) i = readReg s i := by
  unfold readGPR; split
  · subst_vars; exact h0.symm
  · rfl

theorem regIdx_eq_reg (w : W32) : regIdx w = reg w := by
  unfold regIdx reg; ext; simp [Fin.ofNat]

theorem readReg_writeReg (s : State) (i j : Fin 32) (v : W32) (hsz : s.regs.size = 32) :
    readReg (writeReg s i v) j = if j = i ∧ i ≠ 0 then v else readReg s j := by
  unfold writeReg readReg
  by_cases hi : i = 0
  · simp [hi]
  · simp only [hi, beq_iff_eq, ite_false, ne_eq, not_false_eq_true, and_true]
    by_cases hj : j = i
    · subst hj; simp [Array.getD, Array.setIfInBounds, hsz, j.isLt]
    · have : i.val ≠ j.val := fun h => hj (Fin.ext h).symm
      simp [Array.getD, Array.setIfInBounds, hj]
      split <;> simp_all

theorem abs_writeReg (s : State) (i : Fin 32) (v : W32) (hsz : s.regs.size = 32) :
    abs (writeReg s i v) = writeGPR (abs s) i v := by
  unfold writeGPR
  by_cases hi : i = 0
  · subst hi; simp [writeReg]
  · simp only [hi, ite_false]
    have hw : writeReg s i v = { s with regs := s.regs.set! i.val v } := by
      simp [writeReg, hi]
    have hg : (fun j => readReg (writeReg s i v) j) = update (fun j => readReg s j) i v := by
      funext j; rw [readReg_writeReg s i j v hsz]; unfold update
      by_cases hj : j = i <;> simp [hj, hi]
    rw [abs]; rw [hg]; rw [hw]; rfl

theorem writeReg_regs_size (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).regs.size = s.regs.size := by
  unfold writeReg; split <;> simp [Array.size_setIfInBounds]

-- BEGIN R6-5
theorem readFpReg64_writeFpReg64 (s : State) (i j : Fin 32) (v : BitVec 64)
    (hsz : s.fpRegs.size = 32) :
    readFpReg64 (writeFpReg64 s i v) j = if j = i then v else readFpReg64 s j := by
  unfold writeFpReg64 readFpReg64
  by_cases hj : j = i
  · subst hj; simp [Array.getD_eq_getD_getElem?, hsz, j.isLt]
  · have : i.val ≠ j.val := fun h => hj (Fin.ext h).symm
    simp [Array.getD_eq_getD_getElem?, hj, this]

theorem writeFpReg64_fpRegs_size' (s : State) (i : Fin 32) (v : BitVec 64) :
    (writeFpReg64 s i v).fpRegs.size = s.fpRegs.size := by
  simp [writeFpReg64]

theorem lo_append (hi lo : W32) : (hi ++ lo).extractLsb' 0 32 = lo :=
  BitVec.extractLsb'_append_eq_right

theorem hi_append (hi lo : W32) : (hi ++ lo).extractLsb' 32 32 = hi :=
  BitVec.extractLsb'_append_eq_left

theorem halves_append (x : BitVec 64) : x.extractLsb' 32 32 ++ x.extractLsb' 0 32 = x :=
  BitVec.extractLsb'_append_extractLsb' (w := 32) (len := 32)

theorem readFpReg_writeFpReg (s : State) (i j : Fin 32) (v : W32) (hsz : s.fpRegs.size = 32) :
    readFpReg (writeFpReg s i v) j = if j = i then v else readFpReg s j := by
  unfold writeFpReg readFpReg
  rw [readFpReg64_writeFpReg64 _ _ _ _ hsz]
  split
  · exact lo_append _ _
  · rfl

theorem abs_writeFpReg64 (s : State) (i : Fin 32) (v : BitVec 64) (hsz : s.fpRegs.size = 32) :
    abs (writeFpReg64 s i v) = { abs s with FPR := update (abs s).FPR i v } := by
  have hg : (fun j => readFpReg64 (writeFpReg64 s i v) j) = update (fun j => readFpReg64 s j) i v := by
    funext j; rw [readFpReg64_writeFpReg64 s i j v hsz]; unfold update; rfl
  rw [abs]; rw [hg]; rfl

/-- A 32-bit write keeps the upper half (`StoreFPR32` with the model oracle's `fprUpper`). -/
theorem abs_writeFpReg (s : State) (i : Fin 32) (v : W32) (hsz : s.fpRegs.size = 32) :
    abs (writeFpReg s i v) =
      { abs s with FPR := update (abs s).FPR i ((readFpReg64 s i).extractLsb' 32 32 ++ v) } :=
  abs_writeFpReg64 s i _ hsz
-- END R6-5

end Refine
