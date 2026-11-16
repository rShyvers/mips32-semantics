import Semantics.FpOpsCorrectOps

/-!
# FpOpsCorrectApi — the headline correctness theorems

For binary32 and binary64 (`Mips.Fp.binary32`, `binary64`):

* `roundCore_correct_binary32/64`: rounding a nonzero exact value meets `Format.RoundSpec`;
* `roundCore_zero`: an exact zero gives the zero of its sign, no flag;
* `roundCore_flush_*`: with FCSR.FS = 1, a value tiny before rounding becomes zero (tiny, inexact),
  any other value is rounded as with FS = 0;
* `roundSpec_representable`: without overflow the delivered value is correctly rounded to the
  format's finite values (`Format.Representable`);
* `f32Add_correct` … `f64Sqrt_correct`: the operations are correctly rounded.
-/

namespace Mips.Fp

/-- The finite values are values of the format with the exponent range unbounded above. -/
theorem representable_unbounded (f : Format) {x : Rat} (h : f.Representable x) : f.Unbounded x := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨-, -, ht⟩ := f.value_fields hn
  rw [← ht, Exact.toRat_eq]
  refine ⟨_, _, ?_, ?_, rfl⟩
  · have habs : ∀ (s : Bool) (k : Nat), (if s then -(k : Int) else (k : Int)).natAbs = k := by
      intro s k; cases s <;> simp
    rw [habs]
    have hF : f.fracField n < 2 ^ f.fracBits := Nat.mod_lt n (Nat.two_pow_pos f.fracBits)
    have : 2 ^ (f.fracBits + 1) = 2 * 2 ^ f.fracBits := Nat.pow_succ'
    simp only [Format.prec, Format.toExact]
    split <;> simp only <;> omega
  · show f.ulpMin ≤ _
    rw [f.ulpMin_eq]
    simp only [Format.toExact]
    split
    · exact Int.le_refl _
    · rename_i h; simp only [Format.qMin]; omega

/-- **Without overflow, the delivered value is correctly rounded to the finite values.** -/
theorem roundSpec_representable (f : Format) {rm : RoundingMode} {c : Cut} {R : Format.Rounded}
    (h : f.RoundSpec rm c R) (hov : R.overflow = false) :
    ∃ r, f.value R.bits = some r ∧ CorrectlyRounded f.Representable f.UnboundedEven rm c r := by
  obtain ⟨r, hcr, -, hv, -⟩ := h
  exact ⟨r, hv hov, correctlyRounded_mono hcr ⟨_, hv hov⟩ (fun y hy => representable_unbounded f hy)⟩

/-- An exact zero rounds to the zero of its sign, without any exception. -/
theorem roundCore_zero (f : Format) (rm : RoundingMode) (flush : Bool) (w : Exact) (hw : w.sig = 0) :
    f.roundCore rm flush w = ⟨f.zero w.sign, false, false, false⟩ := by
  simp [Format.roundCore, hw]

/-- **The rounding core is correct for binary32** (no flushing). -/
theorem roundCore_correct_binary32 (rm : RoundingMode) (w : Exact) (hw : w.sig ≠ 0) :
    binary32.RoundSpec rm (Cut.ofRat w.toRat) (binary32.roundCore rm false w) :=
  roundCore_correct binary32 binary32_wf rm w hw _ (Cut.ofRat_valid _) (CutAgree.ofRat _ _)

/-- **The rounding core is correct for binary64** (no flushing). -/
theorem roundCore_correct_binary64 (rm : RoundingMode) (w : Exact) (hw : w.sig ≠ 0) :
    binary64.RoundSpec rm (Cut.ofRat w.toRat) (binary64.roundCore rm false w) :=
  roundCore_correct binary64 binary64_wf rm w hw _ (Cut.ofRat_valid _) (CutAgree.ofRat _ _)

/-! ## The operations on `BitVec` -/

/-- With FCSR.FS = 0 an operand is not flushed (`Format.flushIn`). -/
@[simp] theorem Format.flushIn_false (f : Format) (n : Nat) : f.flushIn false n = n := by
  simp [Format.flushIn]

section bv

variable (e : Env) (he : e.flush = false)
include he

/-- `ADD.S` is correctly rounded. -/
theorem f32Add_correct {a b : BitVec 32} {x y : Rat} (ha : binary32.value a.toNat = some x)
    (hb : binary32.value b.toNat = some y) (hxy : x + y ≠ 0) :
    ∃ R : Format.Rounded, binary32.RoundSpec e.rm (Cut.ofRat (x + y)) R ∧
      f32Add e a b = (BitVec.ofNat 32 R.bits, R.flags e.enables) := by
  obtain ⟨R, h1, h2⟩ := binary32.add_correct binary32_wf e he ha hb hxy
  exact ⟨R, h1, by simp [f32Add, he, h2]⟩

/-- `SUB.S` is correctly rounded. -/
theorem f32Sub_correct {a b : BitVec 32} {x y : Rat} (ha : binary32.value a.toNat = some x)
    (hb : binary32.value b.toNat = some y) (hxy : x - y ≠ 0) :
    ∃ R : Format.Rounded, binary32.RoundSpec e.rm (Cut.ofRat (x - y)) R ∧
      f32Sub e a b = (BitVec.ofNat 32 R.bits, R.flags e.enables) := by
  obtain ⟨R, h1, h2⟩ := binary32.sub_correct binary32_wf e he ha hb hxy
  exact ⟨R, h1, by simp [f32Sub, he, h2]⟩

/-- `MUL.S` is correctly rounded. -/
theorem f32Mul_correct {a b : BitVec 32} {x y : Rat} (ha : binary32.value a.toNat = some x)
    (hb : binary32.value b.toNat = some y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ R : Format.Rounded, binary32.RoundSpec e.rm (Cut.ofRat (x * y)) R ∧
      f32Mul e a b = (BitVec.ofNat 32 R.bits, R.flags e.enables) := by
  obtain ⟨R, h1, h2⟩ := binary32.mul_correct binary32_wf e he ha hb hx hy
  exact ⟨R, h1, by simp [f32Mul, he, h2]⟩

/-- `DIV.S` is correctly rounded. -/
theorem f32Div_correct {a b : BitVec 32} {x y : Rat} (ha : binary32.value a.toNat = some x)
    (hb : binary32.value b.toNat = some y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ R : Format.Rounded, binary32.RoundSpec e.rm (Cut.ofRat (x / y)) R ∧
      f32Div e a b = (BitVec.ofNat 32 R.bits, R.flags e.enables) := by
  obtain ⟨R, h1, h2⟩ := binary32.div_correct binary32_wf e he ha hb hx hy
  exact ⟨R, h1, by simp [f32Div, he, h2]⟩

/-- `SQRT.S` is correctly rounded (positive operand). -/
theorem f32Sqrt_correct {a : BitVec 32} {x : Rat} (ha : binary32.value a.toNat = some x) (hx : 0 < x) :
    ∃ R : Format.Rounded, binary32.RoundSpec e.rm (Cut.sqrt x) R ∧
      f32Sqrt e a = (BitVec.ofNat 32 R.bits, R.flags e.enables) := by
  obtain ⟨R, h1, h2⟩ := binary32.sqrt_correct binary32_wf e he ha hx
  exact ⟨R, h1, by simp [f32Sqrt, he, h2]⟩

/-- `ADD.D` is correctly rounded. -/
theorem f64Add_correct {a b : BitVec 64} {x y : Rat} (ha : binary64.value a.toNat = some x)
    (hb : binary64.value b.toNat = some y) (hxy : x + y ≠ 0) :
    ∃ R : Format.Rounded, binary64.RoundSpec e.rm (Cut.ofRat (x + y)) R ∧
      f64Add e a b = (BitVec.ofNat 64 R.bits, R.flags e.enables) := by
  obtain ⟨R, h1, h2⟩ := binary64.add_correct binary64_wf e he ha hb hxy
  exact ⟨R, h1, by simp [f64Add, he, h2]⟩

/-- `SUB.D` is correctly rounded. -/
theorem f64Sub_correct {a b : BitVec 64} {x y : Rat} (ha : binary64.value a.toNat = some x)
    (hb : binary64.value b.toNat = some y) (hxy : x - y ≠ 0) :
    ∃ R : Format.Rounded, binary64.RoundSpec e.rm (Cut.ofRat (x - y)) R ∧
      f64Sub e a b = (BitVec.ofNat 64 R.bits, R.flags e.enables) := by
  obtain ⟨R, h1, h2⟩ := binary64.sub_correct binary64_wf e he ha hb hxy
  exact ⟨R, h1, by simp [f64Sub, he, h2]⟩

/-- `MUL.D` is correctly rounded. -/
theorem f64Mul_correct {a b : BitVec 64} {x y : Rat} (ha : binary64.value a.toNat = some x)
    (hb : binary64.value b.toNat = some y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ R : Format.Rounded, binary64.RoundSpec e.rm (Cut.ofRat (x * y)) R ∧
      f64Mul e a b = (BitVec.ofNat 64 R.bits, R.flags e.enables) := by
  obtain ⟨R, h1, h2⟩ := binary64.mul_correct binary64_wf e he ha hb hx hy
  exact ⟨R, h1, by simp [f64Mul, he, h2]⟩

/-- `DIV.D` is correctly rounded. -/
theorem f64Div_correct {a b : BitVec 64} {x y : Rat} (ha : binary64.value a.toNat = some x)
    (hb : binary64.value b.toNat = some y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ R : Format.Rounded, binary64.RoundSpec e.rm (Cut.ofRat (x / y)) R ∧
      f64Div e a b = (BitVec.ofNat 64 R.bits, R.flags e.enables) := by
  obtain ⟨R, h1, h2⟩ := binary64.div_correct binary64_wf e he ha hb hx hy
  exact ⟨R, h1, by simp [f64Div, he, h2]⟩

/-- `SQRT.D` is correctly rounded (positive operand). -/
theorem f64Sqrt_correct {a : BitVec 64} {x : Rat} (ha : binary64.value a.toNat = some x) (hx : 0 < x) :
    ∃ R : Format.Rounded, binary64.RoundSpec e.rm (Cut.sqrt x) R ∧
      f64Sqrt e a = (BitVec.ofNat 64 R.bits, R.flags e.enables) := by
  obtain ⟨R, h1, h2⟩ := binary64.sqrt_correct binary64_wf e he ha hx
  exact ⟨R, h1, by simp [f64Sqrt, he, h2]⟩

end bv

/-! ## Flush to zero (FCSR.FS = 1) -/

/-- The core's flush test is tininess **before** rounding (MD00082 Vol I-A Rev 6.01 §6.7.2.4, p.102:
"Tiny non-zero results are detected before rounding"): the exact value is strictly between
`±2^E_min`. -/
theorem flush_test_iff (f : Format) (w : Exact) (hw : w.sig ≠ 0) :
    w.exp + (bitLen w.sig : Int) - ((f.fracBits + 1 : Nat) : Int) < f.qMin ↔
      w.toRat.abs < (2 : Rat) ^ f.emin := by
  have hs : 0 < w.sig := Nat.pos_of_ne_zero hw
  have h1 := lt_two_pow_bitLen w.sig
  have h2 := two_pow_bitLen_le w.sig hs
  have h3 := bitLen_pos w.sig hs
  have habs : w.toRat.abs = (w.sig : Rat) * (2 : Rat) ^ w.exp := by
    rw [Exact.toRat_signed]
    exact abs_signed _ (Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (rat_two_zpow_pos _)))
  rw [habs, show (2 : Rat) ^ f.emin = ((1 : Nat) : Rat) * (2 : Rat) ^ f.emin by simp,
    nat_zpow_lt_iff, Format.emin_eq]
  constructor
  · intro h
    rw [show min w.exp (f.qMin + f.fracBits) = w.exp by omega, show (w.exp - w.exp).toNat = 0 by omega]
    have : 2 ^ bitLen w.sig ≤ 2 ^ (f.qMin + f.fracBits - w.exp).toNat :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simp only [Nat.pow_zero, Nat.mul_one, Nat.one_mul]; omega
  · intro h
    refine Classical.byContradiction fun h' => ?_
    rcases Int.le_total w.exp (f.qMin + f.fracBits) with hle | hle
    · rw [show min w.exp (f.qMin + f.fracBits) = w.exp by omega,
        show (w.exp - w.exp).toNat = 0 by omega] at h
      have : 2 ^ (f.qMin + f.fracBits - w.exp).toNat ≤ 2 ^ (bitLen w.sig - 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simp only [Nat.pow_zero, Nat.mul_one, Nat.one_mul] at h; omega
    · rw [show min w.exp (f.qMin + f.fracBits) = f.qMin + f.fracBits by omega,
        show (f.qMin + f.fracBits - (f.qMin + f.fracBits)).toNat = 0 by omega] at h
      have : 1 ≤ 2 ^ (w.exp - (f.qMin + f.fracBits)).toNat := Nat.one_le_two_pow
      have : 1 * 1 ≤ w.sig * 2 ^ (w.exp - (f.qMin + f.fracBits)).toNat := Nat.mul_le_mul (by omega) this
      simp only [Nat.pow_zero, Nat.one_mul] at h; omega

/-- With FCSR.FS = 1, a value that is tiny before rounding is replaced by the zero of its sign,
reported tiny and inexact (§6.7.2.4, p.102: "Every tiny non-zero result is replaced with zero of the
same sign"; "Flushing of tiny non-zero results causes Inexact and Underflow exceptions to be
signaled"). -/
theorem roundCore_flush_tiny (f : Format) (rm : RoundingMode) (w : Exact) (hw : w.sig ≠ 0)
    (ht : w.toRat.abs < (2 : Rat) ^ f.emin) :
    f.roundCore rm true w = ⟨f.zero w.sign, false, true, true⟩ := by
  have := (flush_test_iff f w hw).2 ht
  push_cast at this
  simp [Format.roundCore, hw, this]

/-- With FCSR.FS = 1, a value that is not tiny before rounding is rounded as with FS = 0. -/
theorem roundCore_flush_normal (f : Format) (rm : RoundingMode) (w : Exact) (hw : w.sig ≠ 0)
    (ht : ¬ w.toRat.abs < (2 : Rat) ^ f.emin) :
    f.roundCore rm true w = f.roundCore rm false w := by
  have := mt (flush_test_iff f w hw).1 ht
  push_cast at this
  simp [Format.roundCore, hw, this]

end Mips.Fp
