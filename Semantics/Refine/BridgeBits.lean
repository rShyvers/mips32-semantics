import Semantics.Refine.Abs

/-!
# Refine.BridgeBits — the smallest bridge facts

Single-bit tests, the sign bit, the operating mode and the model's context: what `Refine/Fetch.lean`
needs, split out of `Refine/Bridge.lean` so that the general exception processing there can use the
instruction-fetch facts (`BadInstr`).
-/

namespace Refine

open Manual

/-! ## Single bits -/

theorem and_twoPow_ne (x : W32) (i : Nat) (h : i < 32) :
    (x &&& BitVec.twoPow 32 i != 0#32) = x.getLsbD i := by
  rw [BitVec.and_twoPow]
  have hne : BitVec.twoPow 32 i ≠ 0#32 := by
    intro h'; have := congrArg (·.getLsbD i) h'; simp [h] at this
  split <;> simp_all

theorem and_twoPow_eq (x : W32) (i : Nat) (h : i < 32) :
    (x &&& BitVec.twoPow 32 i == 0#32) = !x.getLsbD i := by
  rw [← and_twoPow_ne x i h]; simp [bne]

/-! ## The sign bit -/

theorem bit31_iff (x : W32) : bit x 31 = decide (2^31 ≤ x.toNat) := by
  simp only [bit, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  have := x.isLt
  by_cases h : 2^31 ≤ x.toNat
  · have : x.toNat / 2^31 = 1 := by omega
    simp [this, h]
  · have : x.toNat / 2^31 = 0 := by omega
    simp [this, h]

/-! ## The operating mode -/

theorem kernel_abs (s : State) : KernelMode (abs s) = kernelMode s := by
  simp only [KernelMode, kernelMode, StatusUM, StatusEXL, StatusERL, abs, bit,
    show statusUmMask = BitVec.twoPow 32 4 by decide, show statusExlMask = BitVec.twoPow 32 1 by decide,
    show statusErlMask = BitVec.twoPow 32 2 by decide, and_twoPow_ne _ 1 (by omega),
    and_twoPow_ne _ 2 (by omega), and_twoPow_eq _ 4 (by omega)]

/-! ## The model's context -/

/-- The context of the model's choices. -/
def modelCtx : Ctx := { impl := modelImpl, oracle := modelOracle }

end Refine
