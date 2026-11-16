import Semantics.Refine.Step

/-!
# Refine.ChoiceFp — facts about the FP core and `FPResult` used by the choice-point proofs (wave 9)

* `FPResult_eq`: one FP operation's FCSR side as an `if` on the trap condition `trapC` (`fpc` writes
  `Cause`, `fpf` also the `Flags`; MD00082 Vol I-A Rev 6.01 §6.7.1, p.99).
* `trapC_inv`, `trapC_fpf`, `fpf_fpf`: FCSR algebra of two consecutive FP operations (written for the
  pre-Release 6 `MADD.D`/`MSUB.D` rows, which Release 6 removed; kept as general facts).
* Two quiet NaNs (`QA64`/`QB64`, `QA32`/`QB32`) for the QNaN fields of the witness oracles.
(R6-5: the NaN branch of the binary `D` operations and the concrete facts of the witness values
`SN64`, `One64`, `Four64` served the odd-register rows of the 32-bit FPU, which the 64-bit FPU of
Release 6 removed; they were removed with them.)
-/

set_option linter.unusedSimpArgs false

namespace Refine

open Manual Mips.Fp

/-! ## Constants -/

/-- A quiet NaN (`FCSR.NAN2008 = 1`: the fraction MSB is 1; MD00082 Vol I-A Rev 6.01 §6.3.1.4,
Table 6.2, p.81), different from the default QNaN. -/
def QA64 : BitVec 64 := 0x7FF8000000000001#64
/-- A second quiet NaN. -/
def QB64 : BitVec 64 := 0x7FF8000000000002#64
/-- Two single quiet NaNs. -/
def QA32 : W32 := 0x7FC00001#32
def QB32 : W32 := 0x7FC00002#32

theorem QA64_ne_QB64 : QA64 ≠ QB64 := by decide

theorem QA64_q : isQNaN64 QA64 = true := by decide
theorem QB64_q : isQNaN64 QB64 = true := by decide
theorem QA32_q : isQNaN32 QA32 = true := by decide
theorem QB32_q : isQNaN32 QB32 = true := by decide

/-! ## `FPResult` -/

theorem ite_app2' {α β γ : Type} (c : Prop) [Decidable c] (f g : α → β → γ) (x : α) (y : β) :
    (if c then f else g) x y = if c then f x y else g x y := by split <;> rfl

def fpc (F : W32) (fl : Mips.Fp.Flags) : W32 := F &&& ~~~(63#32 <<< 12) ||| BitVec.setWidth 32 fl.toBits <<< 12
def fpf (F : W32) (fl : Mips.Fp.Flags) : W32 := fpc F fl ||| BitVec.setWidth 32 fl.toBits <<< 2
def trapC (F : W32) (fl : Mips.Fp.Flags) : Bool :=
  bit (fpc F fl) 17 || ((fpc F fl).extractLsb' 12 5 &&& (fpc F fl).extractLsb' 7 5) != 0#5

theorem FPResult_eq {α} (r : α × Mips.Fp.Flags) (c : Ctx) (f : Frame) :
    FPResult r c f = if trapC f.arch.FCSR r.2 then
      (.signal .FloatingPoint, { f with arch := { f.arch with FCSR := fpc f.arch.FCSR r.2 } })
    else (.ok r.1, { f with arch := { f.arch with FCSR := fpf f.arch.FCSR r.2 } }) := by
  unfold FPResult CheckFPException
  simp only [bind, Pseudo.modify, Pseudo.get, SignalException, pure, ite_app2']
  unfold trapC fpc fpf
  by_cases hc : (bit (f.arch.FCSR &&& ~~~(63#32 <<< 12) ||| BitVec.setWidth 32 r.2.toBits <<< 12) 17 ||
      (BitVec.extractLsb' 12 5 (f.arch.FCSR &&& ~~~(63#32 <<< 12) ||| BitVec.setWidth 32 r.2.toBits <<< 12) &&&
        BitVec.extractLsb' 7 5 (f.arch.FCSR &&& ~~~(63#32 <<< 12) ||| BitVec.setWidth 32 r.2.toBits <<< 12)) != 0#5) = true
  · simp only [hc, ↓reduceIte]
  · simp only [hc, ↓reduceIte, Bool.false_eq_true]; rfl

theorem inv_toBits (s : Bool) : (({ invalid := s } : Mips.Fp.Flags).toBits) = if s then 16#5 else 0#5 := by
  cases s <;> rfl

theorem toBits_b4 (fl : Mips.Fp.Flags) : fl.toBits.getLsbD 4 = fl.invalid := by
  obtain ⟨a, b, c, d, e⟩ := fl; cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem trapC_inv (F : W32) (s : Bool) (h : bit F 11 = false) : trapC F { invalid := s } = false := by
  simp only [bit] at h
  simp only [trapC, fpc, inv_toBits, bit, Bool.or_eq_false_iff, bne_eq_false_iff_eq]
  constructor
  · cases s <;> simp
  · apply BitVec.eq_of_getLsbD_eq; intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> cases s <;> simp_all

theorem fpc_ext12 (G : W32) (fl : Mips.Fp.Flags) : (fpc G fl).extractLsb' 12 5 = fl.toBits := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [fpc]
theorem fpc_ext7 (G : W32) (fl : Mips.Fp.Flags) : (fpc G fl).extractLsb' 7 5 = G.extractLsb' 7 5 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [fpc]
theorem fpc_17 (G : W32) (fl : Mips.Fp.Flags) : bit (fpc G fl) 17 = false := by
  simp [fpc, bit]
theorem fpf_ext7 (G : W32) (fl : Mips.Fp.Flags) : (fpf G fl).extractLsb' 7 5 = G.extractLsb' 7 5 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [fpf, fpc]

theorem trapC_eq (G : W32) (fl : Mips.Fp.Flags) :
    trapC G fl = (fl.toBits &&& G.extractLsb' 7 5 != 0#5) := by
  simp only [trapC, fpc_17, fpc_ext12, fpc_ext7, Bool.false_or]

theorem trapC_fpf (F : W32) (m fl : Mips.Fp.Flags) : trapC (fpf F m) fl = trapC F fl := by
  simp only [trapC_eq, fpf_ext7]

theorem fpf_fpf (F : W32) (s : Bool) (fl : Mips.Fp.Flags) (h : (bit F 6 || fl.invalid) = true) :
    fpf (fpf F { invalid := s }) fl = fpf (fpf F { invalid := false }) fl := by
  have hb := toBits_b4 fl
  simp only [bit] at h
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  by_cases h6 : j = 6
  · subst h6; cases s <;> simp_all [fpf, fpc, inv_toBits]
  · cases s
    · rfl
    · simp only [fpf, fpc, inv_toBits, ↓reduceIte, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_setWidth]
      generalize BitVec.getLsbD F j = b1
      generalize fl.toBits.getLsbD (j - 12) = b2
      generalize fl.toBits.getLsbD (j - 2) = b3
      revert b1 b2 b3; revert h6; revert hj; revert j; decide

end Refine
