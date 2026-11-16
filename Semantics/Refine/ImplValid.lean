import Semantics.Manual.Accuracy
import Semantics.FpOpsCorrectRsqrt
import Semantics.FpOpsCorrectSpecial

/-!
# Refine.ImplValid — the model's implementation constants are valid

`Manual.modelImpl_valid`: `Manual.modelImpl` (`RECIP` = `DIV.fmt` of `1.0`, `RSQRT` = `SQRT.fmt` then
`DIV.fmt`) is of this profile and meets the accuracy of RECIP.fmt (p.336) and RSQRT.fmt (p.343),
against the IEEE-mandated representation and against the exact result. The exact-result bounds come
from the correctness of the IEEE rounding core (`Semantics/FpOpsCorrect*.lean`).

`modelImpl_recipFlags`: the Invalid Operation and Division-by-Zero conditions of the two are those
`Manual.RecipFlagsOK` requires, for every operand and environment (its Table 6.2 classifiers
`FPIsNaN`, ... are the model's `Format.isNaN`, ... by `rfl`: `FPIsNaN_eq`, ...). The one non-trivial case is
`RSQRT` of a positive finite operand: the square root is neither a NaN nor a zero, with or without
`FCSR.FS = 1` (`sqrt_not_tiny`: a square root is never below the normal range, so it is not flushed;
`sqrt_pos_class` then takes the class from `rsqrt_error`). The model's operations flush their input
operands under `FCSR.FS` (`Format.flushIn`): a flushed subnormal operand is excepted by
`RecipFlagsOK` (`flagsOK_of_flushed`), and the square root is never subnormal
(`sqrt_not_subnormal`), so `RSQRT`'s second operation does not flush it (`rsqrt_flagsOK_flush`).
-/

namespace Manual

open Mips.Fp

theorem FPValue_binary32 (n : Nat) : FPValue 8 23 n = binary32.value n := rfl
theorem FPValue_binary64 (n : Nat) : FPValue 11 52 n = binary64.value n := rfl
theorem FPMax_binary32 : FPMax 8 23 = binary32.maxValue := rfl
theorem FPMax_binary64 : FPMax 11 52 = binary64.maxValue := rfl
theorem ULP_binary32 (ex : Int) :
    ULP 8 23 ex = (2 : Rat) ^ (max binary32.ulpMin (ex - binary32.fracBits)) := rfl
theorem ULP_binary64 (ex : Int) :
    ULP 11 52 ex = (2 : Rat) ^ (max binary64.ulpMin (ex - binary64.fracBits)) := rfl

/-- `modelImpl`'s `RECIP` is within 1 ULP of the exact reciprocal. -/
theorem modelImpl_recipExact : modelImpl.RecipExact := by
  refine ⟨fun e x y he hx hy hr r hrv => ?_, fun e x y he hx hy hr r hrv => ?_⟩
  · obtain ⟨r', hv, a, h1, h2, h3⟩ := f32Recip_error e he hx hy hr
    have : r = r' := Option.some.inj (hrv.symm.trans hv)
    subst this
    exact ⟨a, h1, h2, by rw [ULP_binary32]; simpa using h3⟩
  · obtain ⟨r', hv, a, h1, h2, h3⟩ := f64Recip_error e he hx hy hr
    have : r = r' := Option.some.inj (hrv.symm.trans hv)
    subst this
    exact ⟨a, h1, h2, by rw [ULP_binary64]; simpa using h3⟩

/-- `modelImpl`'s `RSQRT` (`SQRT.fmt` then `DIV.fmt`) is within 2 ULP of `1/√fs`. -/
theorem modelImpl_rsqrtAccurate : modelImpl.RsqrtAccurate := by
  refine ⟨fun e x y he hx hy r hrv => ?_, fun e x y he hx hy r hrv => ?_⟩
  · obtain ⟨r', hv, hw1, hw2, ex, h1, h2, h3, h4⟩ :=
      rsqrt_error binary32 binary32_wf (by decide) (by decide) e he value_one32 hx hy
    have hb : (modelImpl.rsqrtS e x).1.toNat =
        (binary32.div e 0x3F800000 (binary32.sqrt e x.toNat).1).1 := by
      have w2 : (binary32.sqrt e x.toNat).1 < 2 ^ 32 := hw2
      have w1 : (binary32.div e 0x3F800000 (binary32.sqrt e x.toNat).1).1 < 2 ^ 32 := hw1
      simp only [modelImpl, f32Div, f32Sqrt, BitVec.toNat_ofNat, he, Format.flushIn_false]
      rw [Nat.mod_eq_of_lt w2, show (1065353216 % 2 ^ 32 : Nat) = 0x3F800000 by decide, Nat.mod_eq_of_lt w1]
    rw [hb] at hrv
    have : r = r' := Option.some.inj (hrv.symm.trans hv)
    subst this
    refine ⟨ex, h1, h2, ?_, ?_⟩ <;> simp only [ULP_binary32, Rat.natCast_ofNat] <;> assumption
  · obtain ⟨r', hv, hw1, hw2, ex, h1, h2, h3, h4⟩ :=
      rsqrt_error binary64 binary64_wf (by decide) (by decide) e he value_one64 hx hy
    have hb : (modelImpl.rsqrtD e x).1.toNat =
        (binary64.div e 0x3FF0000000000000 (binary64.sqrt e x.toNat).1).1 := by
      have w2 : (binary64.sqrt e x.toNat).1 < 2 ^ 64 := hw2
      have w1 : (binary64.div e 0x3FF0000000000000 (binary64.sqrt e x.toNat).1).1 < 2 ^ 64 := hw1
      simp only [modelImpl, f64Div, f64Sqrt, BitVec.toNat_ofNat, he, Format.flushIn_false]
      rw [Nat.mod_eq_of_lt w2, show (4607182418800017408 % 2 ^ 64 : Nat) = 0x3FF0000000000000 by decide,
        Nat.mod_eq_of_lt w1]
    rw [hb] at hrv
    have : r = r' := Option.some.inj (hrv.symm.trans hv)
    subst this
    refine ⟨ex, h1, h2, ?_, ?_⟩ <;> simp only [ULP_binary64, Rat.natCast_ofNat] <;> assumption

/-! ## The spec's Table 6.2 classifiers are the model's -/

theorem FPExp_eq (f : Format) (n : Nat) : FPExp f.expBits f.fracBits n = f.expField n := rfl
theorem FPFrac_eq (f : Format) (n : Nat) : FPFrac f.fracBits n = f.fracField n := rfl
theorem FPSign_eq (f : Format) (n : Nat) : FPSign f.expBits f.fracBits n = f.signBit n := rfl
theorem FPIsNaN_eq (f : Format) (n : Nat) : FPIsNaN f.expBits f.fracBits n = f.isNaN n := rfl
theorem FPIsSNaN_eq (f : Format) (n : Nat) : FPIsSNaN f.expBits f.fracBits n = f.isSNaN n := rfl
theorem FPIsQNaN_eq (f : Format) (n : Nat) : FPIsQNaN f.expBits f.fracBits n = f.isQNaN n := rfl
theorem FPIsZero_eq (f : Format) (n : Nat) : FPIsZero f.expBits f.fracBits n = f.isZero n := rfl
theorem FPIsSubnormal_eq (f : Format) (n : Nat) :
    FPIsSubnormal f.expBits f.fracBits n = f.isSubnormal n := rfl

/-- `RecipFlagsOK` of a `Format`'s field widths, in the model's classifiers. -/
theorem recipFlagsOK_iff (f : Format) (sq : Bool) (e : Env) (n : Nat) (fl : Flags) :
    RecipFlagsOK f.expBits f.fracBits sq e n fl ↔
      ((f.isQNaN n = true → fl = Flags.none) ∧
       (f.isSNaN n = true → fl.invalid = true ∧ fl.divZero = false) ∧
       (f.isNaN n = false → f.isZero n = true → fl.divZero = true ∧ fl.invalid = false) ∧
       (f.isNaN n = false → f.isZero n = false → (e.flush = false ∨ f.isSubnormal n = false) →
         fl.divZero = false ∧ fl.invalid = (sq && f.signBit n))) := Iff.rfl

section flags
variable (f : Format)

/-! ## The Invalid Operation and Division-by-Zero conditions of `RECIP` and `RSQRT` (`Impl.RecipFlags`) -/

theorem qnan_split {n : Nat} (h : f.isQNaN n = true) : f.isNaN n = true ∧ f.isSNaN n = false := by
  simp only [Format.isQNaN, Format.isSNaN, Bool.and_eq_true, beq_iff_eq] at h ⊢
  refine ⟨h.1, ?_⟩
  simp [h.1, h.2]

theorem snan_split {n : Nat} (h : f.isSNaN n = true) : f.isNaN n = true ∧ f.isQNaN n = false := by
  simp only [Format.isQNaN, Format.isSNaN, Bool.and_eq_true, beq_iff_eq] at h ⊢
  refine ⟨h.1, ?_⟩
  simp [h.1, h.2]

theorem zero_not_inf (hM : f.expMax ≠ 0) {n : Nat} (h : f.isZero n = true) : f.isInf n = false := by
  simp only [Format.isZero, Format.isInf, Bool.and_eq_true, beq_iff_eq] at h ⊢
  rw [h.1]; simp only [Bool.and_eq_false_imp, beq_iff_eq]; intro h'; exact absurd h'.symm hM

/-- The conditions of `DIV.fmt` with a dividend that is finite and non-zero, by the class of the
divisor. -/
theorem div_one_flags (hM : f.expMax ≠ 0) (e : Env) {one q : Nat} (hn : f.isNaN one = false)
    (hz : f.isZero one = false) (hi : f.isInf one = false) (hs : f.isSNaN one = false) :
    (f.isNaN q = true → (f.div e one q).2 = { invalid := f.isSNaN q }) ∧
    (f.isNaN q = false → f.isZero q = true → (f.div e one q).2 = { divZero := true }) ∧
    (f.isNaN q = false → f.isZero q = false →
      (f.div e one q).2.invalid = false ∧ (f.div e one q).2.divZero = false) := by
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · simp [Format.div, h, Format.nanFlags, hs]
  · have h3 := zero_not_inf f hM h2
    simp [Format.div, hn, h1, hz, hi, h2, h3]
  · simp only [Format.div, hn, h1, hz, hi, h2, Bool.or_false, Bool.false_and, Bool.and_false,
      Bool.false_eq_true, ite_false]
    split
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩


/-- `RECIP` as `DIV.fmt` of `one` meets `RecipFlagsOK`. -/
theorem recip_flagsOK (hM : f.expMax ≠ 0) (e : Env) {one : Nat} (hn : f.isNaN one = false)
    (hz : f.isZero one = false) (hi : f.isInf one = false) (hs : f.isSNaN one = false) (n : Nat) :
    RecipFlagsOK f.expBits f.fracBits false e n (f.div e one n).2 := by
  rw [recipFlagsOK_iff]
  obtain ⟨D1, D2, D3⟩ := div_one_flags f hM e (q := n) hn hz hi hs
  refine ⟨fun hq => ?_, fun hsn => ?_, fun h1 h2 => ?_, fun h1 h2 _ => ?_⟩
  · obtain ⟨a, b⟩ := qnan_split f hq
    rw [D1 a, b]; rfl
  · rw [D1 (snan_split f hsn).1, hsn]; exact ⟨rfl, rfl⟩
  · rw [D2 h1 h2]; exact ⟨rfl, rfl⟩
  · obtain ⟨a, b⟩ := D3 h1 h2
    exact ⟨b, by rw [a]; rfl⟩

/-- Rounding with flushing is rounding without it when the result is not tiny before rounding. -/
theorem roundCore_noflush (rm : RoundingMode) (fl : Bool) (v : Exact)
    (h : f.qMin ≤ v.exp + (bitLen v.sig : Int) - ((f.fracBits + 1 : Nat) : Int)) :
    f.roundCore rm fl v = f.roundCore rm false v := by
  cases fl
  · rfl
  · have : ¬ (v.exp + (bitLen v.sig : Int) - ((f.fracBits + 1 : Nat) : Int) < f.qMin) := by omega
    simp only [Format.roundCore, Bool.true_and, Bool.false_and, decide_eq_true_eq, this,
      ite_false, Bool.false_eq_true]

/-- **The square root of a value of the format is never tiny** (with `fracBits + 2 ≤ bias`): its
exponent at full precision is at least `qMin`. -/
theorem sqrt_not_tiny (hb : f.fracBits + 2 ≤ f.bias) (a : Exact) (hs : a.sig ≠ 0)
    (he : f.qMin ≤ a.exp) :
    f.qMin ≤ (Exact.sqrt (f.fracBits + 1) a).exp + (bitLen (Exact.sqrt (f.fracBits + 1) a).sig : Int) -
      ((f.fracBits + 1 : Nat) : Int) := by
  simp only [Exact.sqrt]
  generalize hp : f.fracBits + 1 = p
  generalize hsh : 2 * (p + 2) + (if a.exp % 2 = 0 then 0 else 1) = sh
  have hshp : 2 * (p + 2) ≤ sh ∧ sh ≤ 2 * (p + 2) + 1 ∧ (a.exp - (sh : Int)) % 2 = 0 := by
    subst hsh; split <;> omega
  have hn : 2 ^ (2 * (p + 2)) ≤ a.sig * 2 ^ sh := by
    have h1 : 2 ^ (2 * (p + 2)) ≤ 2 ^ sh := Nat.pow_le_pow_right (by omega) hshp.1
    have h2 : 1 ≤ a.sig := Nat.pos_of_ne_zero hs
    calc 2 ^ (2 * (p + 2)) ≤ 2 ^ sh := h1
      _ = 1 * 2 ^ sh := (Nat.one_mul _).symm
      _ ≤ a.sig * 2 ^ sh := Nat.mul_le_mul_right _ h2
  generalize a.sig * 2 ^ sh = n at hn
  have hr : 2 ^ (p + 2) ≤ isqrt n := by
    have hsp := (isqrt_spec n).2
    refine Nat.le_of_not_lt fun hlt => ?_
    have : isqrt n + 1 ≤ 2 ^ (p + 2) := hlt
    have := Nat.mul_le_mul this this
    rw [← Nat.pow_add, show p + 2 + (p + 2) = 2 * (p + 2) by omega] at this
    omega
  have hb2 : p + 4 ≤ bitLen (2 * isqrt n + (if isqrt n * isqrt n = n then 0 else 1)) := by
    apply bitLen_ge_of
    rw [Nat.pow_succ]; split <;> omega
  have hq := f.qMin
  simp only [Format.qMin] at he ⊢
  omega


theorem toExact_facts {n : Nat} (hz : f.isZero n = false) :
    (f.toExact n).sig ≠ 0 ∧ f.qMin ≤ (f.toExact n).exp := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [(f.toExact_sig_zero_iff n).1 h] at hz; cases hz
  simp only [Format.toExact, Format.qMin]
  split
  · exact Int.le_refl _
  · rename_i h; dsimp only; omega

/-- `SQRT.fmt` of a positive finite non-zero operand does not flush (`FCSR.FS` has no effect). -/
theorem sqrt_flush (hb : f.fracBits + 2 ≤ f.bias) (e : Env) (n : Nat) (hn : f.isNaN n = false)
    (hz : f.isZero n = false) (hs : f.signBit n = false) (hi : f.isInf n = false) :
    f.sqrt e n = f.sqrt { e with flush := false } n := by
  obtain ⟨h1, h2⟩ := toExact_facts f hz
  simp only [Format.sqrt, hn, hz, hs, hi, Bool.false_eq_true, ite_false, Format.roundEnv]
  rw [roundCore_noflush f _ e.flush _ (sqrt_not_tiny f hb _ h1 h2)]

/-- A pattern with a non-zero exponent field is not subnormal. -/
theorem isSubnormal_pack_pos (s : Bool) (E fr : Nat) (hE1 : E ≠ 0) (hE : E < 2 ^ f.expBits)
    (hfr : fr < 2 ^ f.fracBits) : f.isSubnormal (f.pack s E fr) = false := by
  have h := (f.pack_fields s E fr hE hfr).1
  simp only [Format.isSubnormal, Format.expField, h]
  simp [hE1]

/-- **A value that is not tiny before rounding rounds to a pattern that is not subnormal**: its
significand rounds to `p` bits (or carries to `2^p`), so the exponent field is at least 1. -/
theorem roundCore_not_subnormal (hf : f.WF) (rm : RoundingMode) (v : Exact) (hs : v.sig ≠ 0)
    (hq : f.qMin ≤ v.exp + (bitLen v.sig : Int) - ((f.fracBits + 1 : Nat) : Int)) :
    f.isSubnormal (f.roundCore rm false v).bits = false := by
  have hM := f.expMax_eq hf
  have hb1 := f.bias_pos hf
  have hEM : f.expMax < 2 ^ f.expBits := by simp only [Format.expMax]; have := Nat.two_pow_pos f.expBits; omega
  have hF : 0 < 2 ^ f.fracBits := Nat.two_pow_pos _
  have hnt : ¬ (v.exp + (bitLen v.sig : Int) - ((f.fracBits + 1 : Nat) : Int) < f.qMin) := by omega
  unfold Format.roundCore
  simp only [hs, ↓reduceIte, Bool.false_and, Bool.false_eq_true, hnt, decide_false]
  -- the significand window
  generalize hL : bitLen v.sig = L at hq hnt ⊢
  have hsig1 : 2 ^ (L - 1) ≤ v.sig := hL ▸ two_pow_bitLen_le v.sig (Nat.pos_of_ne_zero hs)
  have hsig2 : v.sig < 2 ^ L := hL ▸ lt_two_pow_bitLen v.sig
  have hL1 : 1 ≤ L := hL ▸ bitLen_pos v.sig (Nat.pos_of_ne_zero hs)
  generalize ha : (v.exp - (v.exp + (L : Int) - ((f.fracBits + 1 : Nat) : Int))).toNat = a
  generalize hbb : (v.exp + (L : Int) - ((f.fracBits + 1 : Nat) : Int) - v.exp).toNat = b
  have hab : a + L = b + (f.fracBits + 1) := by omega
  have hN1 : 2 ^ f.fracBits * 2 ^ b ≤ v.sig * 2 ^ a := by
    have : 2 ^ f.fracBits * 2 ^ b = 2 ^ (L - 1) * 2 ^ a := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [this]; exact Nat.mul_le_mul_right _ hsig1
  have hN2 : v.sig * 2 ^ a < 2 ^ (f.fracBits + 1) * 2 ^ b := by
    have : 2 ^ (f.fracBits + 1) * 2 ^ b = 2 ^ L * 2 ^ a := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [this]; exact Nat.mul_lt_mul_of_pos_right hsig2 (Nat.two_pow_pos _)
  have hR := roundShift_spec rm v.sign (v.sig * 2 ^ a) b
  have hm1 := hR.ge_of_le (Nat.two_pow_pos _) hN1
  have hm2 := hR.le_of_lt (Nat.two_pow_pos _) hN2
  generalize roundShift rm v.sign (v.sig * 2 ^ a) b = m at hm1 hm2
  have hp2 : 2 ^ (f.fracBits + 1) = 2 * 2 ^ f.fracBits := by rw [Nat.pow_succ]; omega
  generalize hq0 : v.exp + (L : Int) - ((f.fracBits + 1 : Nat) : Int) = q0 at hq ⊢
  simp only [Format.qMin] at hq
  simp only [Format.qMax, Format.qMin]
  have hovf : ∀ (c : Bool) (X : Format.Rounded), X.bits = (if c = true then f.inf v.sign else f.maxFinite v.sign) →
      f.isSubnormal X.bits = false := by
    intro c X hX; rw [hX]
    split
    · exact isSubnormal_pack_pos f _ _ _ (by omega) hEM (by omega)
    · exact isSubnormal_pack_pos f _ _ _ (by omega) (by omega) (by omega)
  by_cases hc : (m == 2 ^ (f.fracBits + 1)) = true
  · simp only [hc, ↓reduceIte]
    split
    · exact hovf _ _ rfl
    · rename_i hov
      have hlt : ¬ (2 ^ f.fracBits < 2 ^ f.fracBits) := Nat.lt_irrefl _
      simp only [hlt, ↓reduceIte]
      exact isSubnormal_pack_pos f _ _ _ (by omega) (by omega) (by omega)
  · have hc' : m ≠ 2 ^ (f.fracBits + 1) := by simpa using hc
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    split
    · exact hovf _ _ rfl
    · rename_i hov
      have hlt : ¬ (m < 2 ^ f.fracBits) := by omega
      simp only [hlt, ↓reduceIte]
      exact isSubnormal_pack_pos f _ _ _ (by omega) (by omega) (by omega)

/-- **`SQRT.fmt` never delivers a subnormal** (with `fracBits + 2 ≤ bias`): a NaN, a zero, an
infinity, or a rounded square root that is not tiny (`sqrt_not_tiny`). So a second operation's
`FCSR.FS` input flushing leaves it alone. -/
theorem sqrt_not_subnormal (hf : f.WF) (hb : f.fracBits + 2 ≤ f.bias) (e : Env) (n : Nat) :
    f.isSubnormal (f.sqrt e n).1 = false := by
  have hM0 : f.expMax ≠ 0 := by have := f.expMax_eq hf; omega
  have nan_ns : ∀ x, f.isNaN x = true → f.isSubnormal x = false := by
    intro x hx
    simp only [Format.isNaN, Format.isSubnormal, Bool.and_eq_true, beq_iff_eq] at hx ⊢
    simp [hx.1, hM0]
  have zero_ns : ∀ s, f.isSubnormal (f.zero s) = false := by
    intro s
    have h := (f.pack_fields s 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _)).2.1
    simp only [Format.isSubnormal, Format.fracField, Format.zero, h]
    simp
  unfold Format.sqrt
  split
  · exact nan_ns _ (qnan_split f ((f.isQNaN_iff _).2 (f.nanResult_spec hf [n]).2.2.2.2.2.1)).1
  · rename_i hn
    split
    · rename_i hz
      simp only [Format.isZero, Format.isSubnormal, Bool.and_eq_true, beq_iff_eq] at hz ⊢
      simp [hz.2]
    · rename_i hz
      split
      · have hQ : f.isQNaN f.defaultQNaN = true :=
          (f.isQNaN_iff _).2 (f.newQNaN_eq ▸ f.newQNaN_isQNaN hf)
        exact nan_ns _ (qnan_split f hQ).1
      · split
        · rename_i hi
          simp only [Format.isInf, Format.isSubnormal, Bool.and_eq_true, beq_iff_eq] at hi ⊢
          simp [hi.1, hM0]
        · have hz' : f.isZero n = false := by simpa using hz
          obtain ⟨h1, h2⟩ := toExact_facts f hz'
          show f.isSubnormal (f.roundCore e.rm e.flush _).bits = false
          by_cases hs0 : (Exact.sqrt (f.fracBits + 1) (f.toExact n)).sig = 0
          · rw [roundCore_zero f _ _ _ hs0]; exact zero_ns _
          · have ht := sqrt_not_tiny f hb _ h1 h2
            rw [roundCore_noflush f _ e.flush _ ht]
            exact roundCore_not_subnormal f hf _ _ hs0 ht

/-- **`SQRT.fmt` of a positive finite non-zero operand is neither a NaN nor a zero** (a pattern of
the format): from `rsqrt_error`, `1 / √x` is finite. -/
theorem sqrt_pos_class (hf : f.WF) (hb : f.fracBits + 2 ≤ f.bias) (hb4 : 4 ≤ f.bias)
    (hM : f.expMax ≠ 0) (hInf : ∀ s, f.expField (f.inf s) = f.expMax)
    (_hDQ : f.expField f.defaultQNaN = f.expMax) {one : Nat} (h1 : f.value one = some 1)
    (_hq1 : f.isQNaN one = false) (hn1 : f.isNaN one = false) (hz1 : f.isZero one = false)
    (hi1 : f.isInf one = false) (e : Env) (n : Nat) (hlt : n < 2 ^ f.width)
    (hn : f.isNaN n = false) (hz : f.isZero n = false) (hs : f.signBit n = false)
    (hi : f.isInf n = false) :
    f.isNaN (f.sqrt e n).1 = false ∧ f.isZero (f.sqrt e n).1 = false ∧ (f.sqrt e n).1 < 2 ^ f.width := by
  rw [sqrt_flush f hb e n hn hz hs hi]
  have hval : f.value n = some (f.toExact n).toRat := by
    rcases f.classify hf n hlt with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, -, -, h, -⟩
    · rw [hn] at h; cases h
    · rw [hi] at h; cases h
    · exact h
  have hsg : (f.toExact n).sign = false := by
    simp only [Format.toExact]; split <;> exact hs
  have hy : 0 < (f.toExact n).toRat := by
    rw [Exact.toRat_signed, hsg]
    simp only [Bool.false_eq_true, ite_false]
    have h0 : (0 : Rat) < ((f.toExact n).sig : Rat) := by
      exact_mod_cast Nat.pos_of_ne_zero (toExact_facts f hz).1
    exact Rat.mul_pos h0 (rat_two_zpow_pos _)
  obtain ⟨r, hv, -, hlt', -⟩ := rsqrt_error f hf hb hb4 { e with flush := false } rfl h1 hval hy
  have hne := (value_some_lt f hv).2
  generalize (f.sqrt { e with flush := false } n).1 = q at hne hlt' ⊢
  have hqn : f.isNaN q = false := by
    cases hq : f.isNaN q
    · rfl
    · exfalso; apply hne
      have hd : (f.div { e with flush := false } one q).1 = f.nanResult [one, q] := by
        simp [Format.div, hq]
      rw [hd]
      have hQ := (f.isQNaN_iff _).2 (f.nanResult_spec hf [one, q]).2.2.2.2.2.1
      have := (qnan_split f hQ).1
      simp only [Format.isNaN, Bool.and_eq_true, beq_iff_eq] at this
      exact this.1
  have hqz : f.isZero q = false := by
    cases hq : f.isZero q
    · rfl
    · exfalso; apply hne
      unfold Format.div
      simp only [hn1, hqn, Bool.or_false, Bool.false_eq_true, ite_false, hi1, Bool.false_and,
        hz1, zero_not_inf f hM hq, hq, ite_true]
      exact hInf _
  exact ⟨hqn, hqz, hlt'⟩

/-- `RSQRT` as `SQRT.fmt` then `DIV.fmt` of `one` (conditions ORed) meets `RecipFlagsOK`; `M` is the
modulus of the `BitVec` round trip between the two operations. -/
theorem rsqrt_flagsOK (hf : f.WF) (hb : f.fracBits + 2 ≤ f.bias) (hb4 : 4 ≤ f.bias)
    (hM : f.expMax ≠ 0) (hInf : ∀ s, f.expField (f.inf s) = f.expMax)
    (hDQ : f.expField f.defaultQNaN = f.expMax) (hQ : f.isQNaN f.defaultQNaN = true)
    {one : Nat} (h1 : f.value one = some 1) (hq1 : f.isQNaN one = false)
    (hn1 : f.isNaN one = false) (hz1 : f.isZero one = false) (hi1 : f.isInf one = false)
    (hs1 : f.isSNaN one = false) (M : Nat) (hW : 2 ^ f.width ≤ M) (e : Env) (n : Nat)
    (hlt : n < 2 ^ f.width) :
    RecipFlagsOK f.expBits f.fracBits true e n
      ((f.sqrt e n).2.or (f.div e one ((f.sqrt e n).1 % M)).2) := by
  rw [recipFlagsOK_iff]
  have D := fun q => div_one_flags f hM e (q := q) hn1 hz1 hi1 hs1
  have hnM : n % M = n := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hW)
  obtain ⟨hdqn, hdqs⟩ := qnan_split f hQ
  have hdqM : f.defaultQNaN % M = f.defaultQNaN :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (f.defaultQNaN_lt hf) hW)
  by_cases hN : f.isNaN n = true
  · have hS : f.sqrt e n = (f.nanResult [n], f.nanFlags [n]) := by simp [Format.sqrt, hN]
    rw [hS]
    refine ⟨fun hq => ?_, fun hsn => ?_, fun h => absurd hN (by simp [h]),
      fun h => absurd hN (by simp [h])⟩
    · obtain ⟨-, hsn⟩ := qnan_split f hq
      have hnr : f.nanResult [n] = n := by simp [Format.nanResult, List.find?, hq, hsn]
      simp only [hnr, hnM, (D n).1 hN, hsn, Format.nanFlags, List.any_cons, List.any_nil,
        Bool.or_false]
      rfl
    · have hQ := (f.isQNaN_iff _).2 (f.nanResult_spec hf [n]).2.2.2.2.2.1
      obtain ⟨hrn, hrs⟩ := qnan_split f hQ
      have hrM : f.nanResult [n] % M = f.nanResult [n] :=
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (f.nanResult_lt hf [n] (by simpa using hlt)) hW)
      simp only [hrM, (D _).1 hrn, hrs, Format.nanFlags, List.any_cons, List.any_nil,
        Bool.or_false, hsn]
      exact ⟨rfl, rfl⟩
  · have hN' : f.isNaN n = false := by simpa using hN
    have hq : f.isQNaN n = false := by
      cases h : f.isQNaN n
      · rfl
      · exact absurd (qnan_split f h).1 hN
    have hsn : f.isSNaN n = false := by
      cases h : f.isSNaN n
      · rfl
      · exact absurd (snan_split f h).1 hN
    refine ⟨fun h => absurd (hq.symm.trans h) (by decide), fun h => absurd (hsn.symm.trans h) (by decide),
      fun _ hz => ?_,
      fun _ hz _ => ?_⟩
    · have hS : f.sqrt e n = (n, Flags.none) := by simp [Format.sqrt, hN', hz]
      rw [hS]
      simp only [hnM, (D n).2.1 hN' hz]
      exact ⟨rfl, rfl⟩
    · by_cases hsg : f.signBit n = true
      · have hS : f.sqrt e n = (f.defaultQNaN, Flags.invalidOnly) := by simp [Format.sqrt, hN', hz, hsg]
        rw [hS]
        simp only [hdqM, (D _).1 hdqn, hdqs, hsg]
        exact ⟨rfl, rfl⟩
      · have hsg' : f.signBit n = false := by simpa using hsg
        by_cases hI : f.isInf n = true
        · have hS : f.sqrt e n = (n, Flags.none) := by simp [Format.sqrt, hN', hz, hsg', hI]
          rw [hS]
          obtain ⟨a, b⟩ := (D n).2.2 hN' hz
          simp only [hnM, hsg']
          exact ⟨by simp [Flags.or, Flags.none, b], by simp [Flags.or, Flags.none, a]⟩
        · have hI' : f.isInf n = false := by simpa using hI
          obtain ⟨hqn, hqz, hqlt⟩ :=
            sqrt_pos_class f hf hb hb4 hM hInf hDQ h1 hq1 hn1 hz1 hi1 e n hlt hN' hz hsg' hI'
          have hqM : (f.sqrt e n).1 % M = (f.sqrt e n).1 := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hqlt hW)
          obtain ⟨a, b⟩ := (D _).2.2 hqn hqz
          have hS : (f.sqrt e n).2.invalid = false ∧ (f.sqrt e n).2.divZero = false := by
            simp only [Format.sqrt, hN', hz, hsg', hI', Bool.false_eq_true, ite_false, Format.roundEnv]
            exact ⟨rfl, rfl⟩
          rw [hqM, hsg']
          exact ⟨by simp [Flags.or, hS.2, b], by simp [Flags.or, hS.1, a]⟩


/-- With `FCSR.FS = 1` a subnormal operand is excepted from the fourth clause of `RecipFlagsOK`, and
the first three do not apply to it (it is neither a NaN nor a zero): every flag set is allowed. -/
theorem flagsOK_of_flushed (hM : f.expMax ≠ 0) (sq : Bool) (e : Env) (n : Nat) (fl : Flags)
    (h : (e.flush && f.isSubnormal n) = true) : RecipFlagsOK f.expBits f.fracBits sq e n fl := by
  rw [recipFlagsOK_iff]
  simp only [Bool.and_eq_true] at h
  obtain ⟨hfl, hsub⟩ := h
  have hsub' := hsub
  simp only [Format.isSubnormal, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hsub'
  have hnn : f.isNaN n = false := by
    simp only [Format.isNaN, hsub'.1]; simp [Ne.symm hM]
  have hnz : f.isZero n = false := by
    simp only [Format.isZero, hsub'.1]; simp [hsub'.2]
  refine ⟨fun hq => ?_, fun hs => ?_, fun _ hz => ?_, fun _ _ h' => ?_⟩
  · rw [(qnan_split f hq).1] at hnn; cases hnn
  · rw [(snan_split f hs).1] at hnn; cases hnn
  · rw [hz] at hnz; cases hnz
  · rcases h' with h' | h'
    · rw [hfl] at h'; cases h'
    · rw [hsub] at h'; cases h'

/-- An operand that `FCSR.FS` does not flush. -/
theorem flushIn_of_not (e : Env) (n : Nat) (h : ¬ (e.flush && f.isSubnormal n) = true) :
    f.flushIn e.flush n = n := by
  unfold Format.flushIn; simp only [h, Bool.false_eq_true, ↓reduceIte]

/-- `SQRT.fmt` delivers a pattern of the format. -/
theorem sqrt_lt_width (hf : f.WF) (e : Env) {a : Nat} (ha : a < 2 ^ f.width) :
    (f.sqrt e a).1 < 2 ^ f.width := by
  unfold Format.sqrt
  repeat' split
  all_goals first | exact f.nanResult_lt hf _ (by simp; omega) | exact ha | exact f.defaultQNaN_lt hf |
    exact f.roundEnv_lt hf _ _

/-- `RECIP` as `DIV.fmt` of `one` with `FCSR.FS` input flushing (`Format.flushIn`, as `f32Div`)
meets `RecipFlagsOK`. -/
theorem recip_flagsOK_flush (hM : f.expMax ≠ 0) (e : Env) {one : Nat} (hn : f.isNaN one = false)
    (hz : f.isZero one = false) (hi : f.isInf one = false) (hs : f.isSNaN one = false)
    (hone : f.flushIn e.flush one = one) (n : Nat) :
    RecipFlagsOK f.expBits f.fracBits false e n
      (f.div e (f.flushIn e.flush one) (f.flushIn e.flush n)).2 := by
  rw [hone]
  by_cases hfs : (e.flush && f.isSubnormal n) = true
  · exact flagsOK_of_flushed f hM _ e n _ hfs
  · rw [flushIn_of_not f e n hfs]
    exact recip_flagsOK f hM e hn hz hi hs n

/-- `RSQRT` as `SQRT.fmt` then `DIV.fmt` of `one`, each with `FCSR.FS` input flushing (as
`f32Sqrt`, `f32Div`), meets `RecipFlagsOK`: the square root is never subnormal
(`sqrt_not_subnormal`), so the second flush is the identity. -/
theorem rsqrt_flagsOK_flush (hf : f.WF) (hb : f.fracBits + 2 ≤ f.bias) (hb4 : 4 ≤ f.bias)
    (hM : f.expMax ≠ 0) (hInf : ∀ s, f.expField (f.inf s) = f.expMax)
    (hDQ : f.expField f.defaultQNaN = f.expMax) (hQ : f.isQNaN f.defaultQNaN = true)
    {one : Nat} (h1 : f.value one = some 1) (hq1 : f.isQNaN one = false)
    (hn1 : f.isNaN one = false) (hz1 : f.isZero one = false) (hi1 : f.isInf one = false)
    (hs1 : f.isSNaN one = false) (M : Nat) (hW : 2 ^ f.width ≤ M) (e : Env)
    (hone : f.flushIn e.flush one = one) (n : Nat) (hlt : n < 2 ^ f.width) :
    RecipFlagsOK f.expBits f.fracBits true e n
      ((f.sqrt e (f.flushIn e.flush n)).2.or
        (f.div e (f.flushIn e.flush one)
          (f.flushIn e.flush ((f.sqrt e (f.flushIn e.flush n)).1 % M))).2) := by
  rw [hone]
  by_cases hfs : (e.flush && f.isSubnormal n) = true
  · exact flagsOK_of_flushed f hM _ e n _ hfs
  · rw [flushIn_of_not f e n hfs]
    have hqM : (f.sqrt e n).1 % M = (f.sqrt e n).1 :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (sqrt_lt_width f hf e hlt) hW)
    have hns : ¬ (e.flush && f.isSubnormal ((f.sqrt e n).1 % M)) = true := by
      rw [hqM, sqrt_not_subnormal f hf hb e n]; simp
    rw [flushIn_of_not f e _ hns]
    exact rsqrt_flagsOK f hf hb hb4 hM hInf hDQ hQ h1 hq1 hn1 hz1 hi1 hs1 M hW e n hlt

end flags

/-- `modelImpl`'s `RECIP` and `RSQRT` signal Invalid Operation and Division by Zero as the manual
mandates (`Impl.RecipFlags`). -/
theorem modelImpl_recipFlags : modelImpl.RecipFlags := by
  have one32 : ∀ fl, binary32.flushIn fl 0x3F800000 = 0x3F800000 := fun fl => by
    unfold Format.flushIn
    rw [show binary32.isSubnormal 0x3F800000 = false by decide, Bool.and_false]; rfl
  have one64 : ∀ fl, binary64.flushIn fl 0x3FF0000000000000 = 0x3FF0000000000000 := fun fl => by
    unfold Format.flushIn
    rw [show binary64.isSubnormal 0x3FF0000000000000 = false by decide, Bool.and_false]; rfl
  refine ⟨fun e x => ?_, fun e x => ?_, fun e x => ?_, fun e x => ?_⟩
  · have hr : (modelImpl.recipS e x).2 =
        (binary32.div e (binary32.flushIn e.flush 0x3F800000) (binary32.flushIn e.flush x.toNat)).2 :=
      rfl
    rw [hr]
    exact recip_flagsOK_flush binary32 (by decide) e (by decide) (by decide) (by decide) (by decide)
      (one32 _) x.toNat
  · have hr : (modelImpl.recipD e x).2 =
        (binary64.div e (binary64.flushIn e.flush 0x3FF0000000000000)
          (binary64.flushIn e.flush x.toNat)).2 := rfl
    rw [hr]
    exact recip_flagsOK_flush binary64 (by decide) e (by decide) (by decide) (by decide) (by decide)
      (one64 _) x.toNat
  · have hr : (modelImpl.rsqrtS e x).2 =
        ((binary32.sqrt e (binary32.flushIn e.flush x.toNat)).2.or
          (binary32.div e (binary32.flushIn e.flush 0x3F800000)
            (binary32.flushIn e.flush
              ((binary32.sqrt e (binary32.flushIn e.flush x.toNat)).1 % 2 ^ 32))).2) := rfl
    rw [hr]
    exact rsqrt_flagsOK_flush binary32 binary32_wf (by decide) (by decide) (by decide)
      (fun s => by cases s <;> decide) (by decide) (by decide) value_one32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (2 ^ 32) (Nat.le_refl _) e (one32 _) x.toNat x.isLt
  · have hr : (modelImpl.rsqrtD e x).2 =
        ((binary64.sqrt e (binary64.flushIn e.flush x.toNat)).2.or
          (binary64.div e (binary64.flushIn e.flush 0x3FF0000000000000)
            (binary64.flushIn e.flush
              ((binary64.sqrt e (binary64.flushIn e.flush x.toNat)).1 % 2 ^ 64))).2) := rfl
    rw [hr]
    exact rsqrt_flagsOK_flush binary64 binary64_wf (by decide) (by decide) (by decide)
      (fun s => by cases s <;> decide) (by decide) (by decide) value_one64 (by decide) (by decide)
      (by decide) (by decide) (by decide) (2 ^ 64) (Nat.le_refl _) e (one64 _) x.toNat x.isLt


/-- **`modelImpl` is a valid implementation** (`Impl.Valid`: `Impl.WF`, `RECIP.fmt` within 1 ULP of
the IEEE-mandated representation and of the exact result, `RSQRT.fmt` within 2 ULP of the exact
result, and the Invalid Operation / Division-by-Zero conditions of both as `Impl.RecipFlags`
requires). -/
theorem modelImpl_valid : modelImpl.Valid :=
  ⟨modelImpl_WF, modelImpl_recipAccurate, modelImpl_recipExact, modelImpl_rsqrtAccurate,
    modelImpl_recipFlags⟩

end Manual
