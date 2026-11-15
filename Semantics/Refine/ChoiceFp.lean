import Semantics.Refine.Step

/-!
# Refine.ChoiceFp — facts about the FP core and `FPResult` used by the choice-point proofs (wave 9)

* `FPResult_eq`: one FP operation's FCSR side as an `if` on the trap condition `trapC` (`fpc` writes
  `Cause`, `fpf` also the `Flags`; MD00082 Vol I-A Rev 6.01 §6.7.1, p.99).
* `trapC_inv`, `trapC_fpf`, `fpf_fpf`: the FCSR algebra of the `MADD.D`/`MSUB.D` corner
  `Manual.MaddAbsorbs` (soundness of the refined row, `Refine.cf_maddD`).
* The NaN branch of the binary operations (`add_nan` ...: the first quiet NaN operand, Invalid iff some
  operand is a signaling NaN; `Mips.Fp.Format.nanResult`), and `Dist`: a signaling NaN and a quiet NaN
  in one operand position give results that differ in the value or in Invalid Operation
  (`dist_left`, `dist_right`, `dist_both`).
-/

set_option linter.unusedSimpArgs false

namespace Refine

open Manual Mips.Fp

/-! ## Constants -/

/-- A quiet NaN (legacy NaN encoding, `FIR.Has2008 = 0`: the fraction MSB is 0; MD00082 Vol I-A Rev
6.01 §6.3.1.4, Table 6.2, p.81), different from the default QNaN. -/
def QA64 : BitVec 64 := 0x7FF0000000000001#64
/-- A second quiet NaN. -/
def QB64 : BitVec 64 := 0x7FF0000000000002#64
/-- A signaling NaN (fraction MSB 1). -/
def SN64 : BitVec 64 := 0x7FF8000000000000#64
/-- `+1.0`. -/
def One64 : BitVec 64 := 0x3FF0000000000000#64
/-- `+4.0`. -/
def Four64 : BitVec 64 := 0x4010000000000000#64
/-- Two single quiet NaNs. -/
def QA32 : W32 := 0x7F800001#32
def QB32 : W32 := 0x7F800002#32

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

/-- `FPCheck` (one operation of a multiply-add: Cause and the trap check, no Flags) as an `if` on
`trapC`. -/
theorem FPCheck_eq {α} (r : α × Mips.Fp.Flags) (c : Ctx) (f : Frame) :
    FPCheck r c f = if trapC f.arch.FCSR r.2 then
      (.signal .FloatingPoint, { f with arch := { f.arch with FCSR := fpc f.arch.FCSR r.2 } })
    else (.ok r.1, { f with arch := { f.arch with FCSR := fpc f.arch.FCSR r.2 } }) := by
  unfold FPCheck CheckFPException
  simp only [bind, Pseudo.modify, Pseudo.get, SignalException, pure, ite_app2']
  unfold trapC fpc
  by_cases hc : (bit (f.arch.FCSR &&& ~~~(63#32 <<< 12) ||| BitVec.setWidth 32 r.2.toBits <<< 12) 17 ||
      (BitVec.extractLsb' 12 5 (f.arch.FCSR &&& ~~~(63#32 <<< 12) ||| BitVec.setWidth 32 r.2.toBits <<< 12) &&&
        BitVec.extractLsb' 7 5 (f.arch.FCSR &&& ~~~(63#32 <<< 12) ||| BitVec.setWidth 32 r.2.toBits <<< 12)) != 0#5) = true
  · simp only [hc, ↓reduceIte]
  · simp only [hc, ↓reduceIte, Bool.false_eq_true]

theorem m63_bit (k : Nat) : (63#32).getLsbD k = decide (k < 6) := by
  by_cases h : k < 6
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with h|h|h|h|h|h <;> subst h <;> decide
  · simp only [h, decide_false, BitVec.getLsbD_ofNat]
    have : 63 < 2 ^ k := Nat.lt_of_lt_of_le (by decide : 63 < 2 ^ 6) (Nat.pow_le_pow_right (by decide) (by omega))
    simp [Nat.testBit_lt_two_pow this]

/-- A second Cause write replaces the first. -/
theorem fpc_fpc (F : W32) (m fl : Mips.Fp.Flags) : fpc (fpc F m) fl = fpc F fl := by
  unfold fpc
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, m63_bit]
  by_cases h : i < 12
  · simp [h]
  · by_cases h2 : i < 18
    · simp [h, show i - 12 < 6 by omega]
    · simp [h, show ¬ (i - 12 < 6) by omega, BitVec.getLsbD_of_ge m.toBits (i - 12) (by omega),
        BitVec.getLsbD_of_ge fl.toBits (i - 12) (by omega)]

theorem fpf_fpc (F : W32) (m fl : Mips.Fp.Flags) : fpf (fpc F m) fl = fpf F fl := by
  unfold fpf; rw [fpc_fpc]

/-- The exceptions of the multiply joined with an Invalid add. -/
theorem inv_or_true (s : Bool) :
    (({ invalid := s } : Mips.Fp.Flags).or { invalid := true }) = { invalid := true } := by
  cases s <;> rfl

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

theorem trapC_fpc (F : W32) (m fl : Mips.Fp.Flags) : trapC (fpc F m) fl = trapC F fl := by
  simp only [trapC_eq, fpc_ext7]

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

/-! ## The NaN branch of the binary operations -/

def NR (x y : BitVec 64) : BitVec 64 × Flags :=
  (BitVec.ofNat 64 (binary64.nanResult [x.toNat, y.toNat]), binary64.nanFlags [x.toNat, y.toNat])

theorem add_nan (e : Env) (x y : BitVec 64) (h : (isNaN64 x || isNaN64 y) = true) : f64Add e x y = NR x y := by
  simp only [isNaN64] at h; simp only [f64Add, Format.add, h, ↓reduceIte, NR]
theorem sub_nan (e : Env) (x y : BitVec 64) (h : (isNaN64 x || isNaN64 y) = true) : f64Sub e x y = NR x y := by
  simp only [isNaN64] at h; simp only [f64Sub, Format.sub, h, ↓reduceIte, NR]
theorem mul_nan (e : Env) (x y : BitVec 64) (h : (isNaN64 x || isNaN64 y) = true) : f64Mul e x y = NR x y := by
  simp only [isNaN64] at h; simp only [f64Mul, Format.mul, h, ↓reduceIte, NR]
theorem div_nan (e : Env) (x y : BitVec 64) (h : (isNaN64 x || isNaN64 y) = true) : f64Div e x y = NR x y := by
  simp only [isNaN64] at h; simp only [f64Div, Format.div, h, ↓reduceIte, NR]

def Dist (r₁ r₂ : BitVec 64 × Flags) : Prop := r₁.1 ≠ r₂.1 ∨ r₁.2.invalid ≠ r₂.2.invalid

theorem qnan_not_snan64 (y : BitVec 64) (h : isQNaN64 y = true) : isSNaN64 y = false := by
  revert h; simp only [isQNaN64, isSNaN64, Format.isQNaN, Format.isSNaN]
  generalize binary64.isNaN _ = b; generalize binary64.fracField _ / _ = n; cases b <;> simp; omega

theorem bq_S : binary64.isQNaN SN64.toNat = false := by decide
theorem bq_Q : binary64.isQNaN QA64.toNat = true := by decide
theorem bq_QB : binary64.isQNaN QB64.toNat = true := by decide
theorem bs_S : binary64.isSNaN SN64.toNat = true := by decide
theorem bs_Q : binary64.isSNaN QA64.toNat = false := by decide
theorem bs_QB : binary64.isSNaN QB64.toNat = false := by decide
theorem dq_ne_Q : BitVec.ofNat 64 binary64.defaultQNaN ≠ QA64 := by decide
theorem dq_ne_QB : BitVec.ofNat 64 binary64.defaultQNaN ≠ QB64 := by decide

theorem nr_cons (n : Nat) (l : List Nat) :
    binary64.nanResult (n :: l) = if binary64.isQNaN n then n else binary64.nanResult l := by
  simp only [Format.nanResult, List.find?_cons]; cases binary64.isQNaN n <;> rfl
theorem nr_nil : binary64.nanResult [] = binary64.defaultQNaN := rfl
theorem nf_inv (l : List Nat) : (binary64.nanFlags l).invalid = l.any (fun x => binary64.isSNaN x) := rfl

theorem qnan_not_snan (n : Nat) (h : binary64.isQNaN n = true) : binary64.isSNaN n = false := by
  revert h; simp only [Format.isQNaN, Format.isSNaN]
  generalize binary64.isNaN _ = b; generalize binary64.fracField _ / _ = n; cases b <;> simp; omega


theorem dist_left (y : BitVec 64) : Dist (NR SN64 y) (NR QA64 y) := by
  unfold Dist NR
  simp only [nr_cons, nr_nil, bq_S, bq_Q, nf_inv, List.any_cons, List.any_nil, bs_S, bs_Q,
    Bool.true_or, Bool.false_or, Bool.or_false, ↓reduceIte, Bool.false_eq_true, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  cases hq : binary64.isQNaN y.toNat
  · left; simpa using dq_ne_Q
  · right; simp [qnan_not_snan _ hq]
theorem dist_right (x : BitVec 64) : Dist (NR x SN64) (NR x QA64) := by
  unfold Dist NR
  simp only [nr_cons, nr_nil, bq_S, bq_Q, nf_inv, List.any_cons, List.any_nil, bs_S, bs_Q,
    Bool.or_true, Bool.false_or, Bool.or_false, ↓reduceIte, Bool.false_eq_true, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  cases hq : binary64.isQNaN x.toNat
  · left; simpa using dq_ne_Q
  · right; simp [qnan_not_snan _ hq]
theorem dist_both : Dist (NR SN64 SN64) (NR QA64 QA64) := by
  right; decide

theorem qnan64_not_snan (x : BitVec 64) (h : isQNaN64 x = true) : isSNaN64 x = false :=
  qnan_not_snan x.toNat h
theorem qnan64_nan (x : BitVec 64) (h : isQNaN64 x = true) : isNaN64 x = true := by
  revert h; simp only [isQNaN64, isNaN64, Format.isQNaN, Bool.and_eq_true]; exact fun h => h.1

/-- A quiet NaN first operand is delivered unchanged; Invalid iff the other is a signaling NaN. -/
theorem nr_qnan_left (x y : BitVec 64) (h : isQNaN64 x = true) :
    NR x y = (x, { invalid := isSNaN64 y }) := by
  have hs := qnan64_not_snan x h
  simp only [isQNaN64, isSNaN64] at h hs
  simp only [NR, nr_cons, h, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq, Format.nanFlags,
    List.any_cons, List.any_nil, hs, Bool.false_or, Bool.or_false, isSNaN64]
theorem mul_qnan_left (e : Env) (x y : BitVec 64) (h : isQNaN64 x = true) :
    f64Mul e x y = (x, { invalid := isSNaN64 y }) := by
  rw [mul_nan e x y (by simp [qnan64_nan x h]), nr_qnan_left x y h]
theorem add_qnan_left (e : Env) (x y : BitVec 64) (h : isQNaN64 x = true) :
    f64Add e x y = (x, { invalid := isSNaN64 y }) := by
  rw [add_nan e x y (by simp [qnan64_nan x h]), nr_qnan_left x y h]
theorem sub_qnan_left (e : Env) (x y : BitVec 64) (h : isQNaN64 x = true) :
    f64Sub e x y = (x, { invalid := isSNaN64 y }) := by
  rw [sub_nan e x y (by simp [qnan64_nan x h]), nr_qnan_left x y h]

/-! ## Concrete facts for the witness values -/

theorem QA64_s : isSNaN64 QA64 = false := by decide
theorem QB64_s : isSNaN64 QB64 = false := by decide
theorem QA64_n : isNaN64 QA64 = true := by decide
theorem SN64_s : isSNaN64 SN64 = true := by decide
theorem SN64_q : isQNaN64 SN64 = false := by decide
theorem SN64_n : isNaN64 SN64 = true := by decide
theorem One64_s : isSNaN64 One64 = false := by decide
theorem One64_q : isQNaN64 One64 = false := by decide
theorem QA64_ne_QB64 : QA64 ≠ QB64 := by decide
theorem QA32_ne_QB32 : QA32 ≠ QB32 := by decide

theorem sqrt_SN (e : Env) : (f64Sqrt e SN64).2.invalid = true := rfl
theorem sqrt_QA (e : Env) : (f64Sqrt e QA64).2.invalid = false := rfl
theorem sqrt_QA1 (e : Env) : (f64Sqrt e QA64).1 = QA64 := rfl
theorem div1_SN (e : Env) : (f64Div e 0x3FF0000000000000#64 SN64).2.invalid = true := rfl
theorem div1_QA (e : Env) : (f64Div e 0x3FF0000000000000#64 QA64).2.invalid = false := rfl
theorem sqrt_SN1 (e : Env) : (f64Sqrt e SN64).1 = 0x7FF7FFFFFFFFFFFF#64 := rfl
theorem div1_dq (e : Env) : (f64Div e 0x3FF0000000000000#64 (f64Sqrt e SN64).1).2.invalid = false := by
  rw [sqrt_SN1]; rfl
theorem cvtSD_SN (e : Env) : (f64ToF32 e SN64).2.invalid = true := rfl
theorem toW_one (rm : RoundingMode) : f64ToW32 rm One64 = (1#32, Flags.none) := by cases rm <;> rfl
theorem toW_four (rm : RoundingMode) : f64ToW32 rm Four64 = (4#32, Flags.none) := by cases rm <;> rfl

/-- The NaN branch always delivers a quiet NaN (the first quiet NaN operand, or the default QNaN). -/
theorem NR_q (x y : BitVec 64) : isQNaN64 (NR x y).1 = true := by
  simp only [NR, nr_cons, nr_nil, isQNaN64]
  cases hx : binary64.isQNaN x.toNat
  · cases hy : binary64.isQNaN y.toNat
    · simp only [Bool.false_eq_true, ↓reduceIte]; decide
    · simp [hy]
  · simp [hx]
theorem add_q (e : Env) (x y : BitVec 64) (h : (isNaN64 x || isNaN64 y) = true) : isQNaN64 (f64Add e x y).1 = true := by
  rw [add_nan e x y h]; exact NR_q x y
theorem sub_q (e : Env) (x y : BitVec 64) (h : (isNaN64 x || isNaN64 y) = true) : isQNaN64 (f64Sub e x y).1 = true := by
  rw [sub_nan e x y h]; exact NR_q x y
theorem mul_q (e : Env) (x y : BitVec 64) (h : (isNaN64 x || isNaN64 y) = true) : isQNaN64 (f64Mul e x y).1 = true := by
  rw [mul_nan e x y h]; exact NR_q x y

/-- A multiply that signals Invalid Operation delivers a quiet NaN (a NaN operand's `nanResult`, or the
default QNaN of `∞ × 0`; a rounded product never signals Invalid). -/
theorem mul_inv_q (e : Env) (x y : BitVec 64) (h : (f64Mul e x y).2.invalid = true) :
    isQNaN64 (f64Mul e x y).1 = true := by
  by_cases hn : (isNaN64 x || isNaN64 y) = true
  · exact mul_q e x y hn
  · simp only [isNaN64] at hn
    revert h
    simp only [f64Mul, Format.mul, hn, Bool.false_eq_true, ↓reduceIte]
    split
    · intro _; decide
    · split
      · simp [Flags.none]
      · simp [Format.roundEnv, Format.Rounded.flags]

/-- The union with an Invalid set of conditions absorbs a later Invalid. -/
theorem or_inv_absorb (m : Flags) (hm : m.invalid = true) (s : Bool) : m.or { invalid := s } = m := by
  obtain ⟨a, b, c, d, f⟩ := m
  simp only at hm; subst hm
  simp [Flags.or]

theorem trapC_en (F : W32) (h : bit F 11 = true) : trapC F { invalid := true } = true := by
  rw [trapC_eq, inv_toBits]
  simp only [↓reduceIte, bne_iff_ne, ne_eq]
  intro he
  simp only [bit] at h
  have h4 : (16#5 &&& BitVec.extractLsb' 7 5 F).getLsbD 4 = true := by
    simp [BitVec.getLsbD_and, BitVec.getLsbD_extractLsb', h]
  rw [he] at h4; simp at h4

theorem toBits_b4e (f : Flags) : f.toBits[4] = f.invalid := by
  obtain ⟨a, b, c, d, e⟩ := f; cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem bit6_fpf (G : W32) (fl : Flags) : bit (fpf G fl) 6 = (bit G 6 || fl.invalid) := by
  have hb := toBits_b4e fl
  simp only [fpf, fpc, bit]
  simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, hb]

theorem bit16_fpf (G : W32) (fl : Flags) : bit (fpf G fl) 16 = fl.invalid := by
  have hb := toBits_b4e fl
  simp only [fpf, fpc, bit]
  simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, hb]

/-- A non-quiet first operand and a quiet NaN second operand: the second is delivered. -/
theorem nr_right_q (x y : BitVec 64) (hx : isQNaN64 x = false) (hy : isQNaN64 y = true) : (NR x y).1 = y := by
  simp only [isQNaN64] at hx hy
  simp only [NR, nr_cons, hx, hy, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem mul_right_q (e : Env) (x y : BitVec 64) (hx : isQNaN64 x = false) (hy : isQNaN64 y = true) :
    (f64Mul e x y).1 = y := by
  rw [mul_nan e x y (by simp [qnan64_nan y hy])]; exact nr_right_q x y hx hy

end Refine
