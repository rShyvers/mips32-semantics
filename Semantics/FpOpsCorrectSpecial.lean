import Semantics.FpOpsCorrectApi

/-!
# FpOpsCorrectSpecial — the encodings' classes, the special results, the NaN rule

Bridges the classes of `Semantics/FpOpsSpec.lean` (`Format.IsNaN`, `IsSNaN`, `IsQNaN`, `datum`,
`infBits`, `zeroBits`, `newQNaN`, Table 6.2 / 6.3 of MD00082 Vol I-A Rev 6.01) with the model's
Boolean tests (`Format.isNaN`, …), and proves the model's NaN rule (`nanResult`, `nanFlags`) meets
`Format.NaNResult`, its first-QNaN choice being the documented pin (`nanResult_first`). Also: every
result encoding the model builds is a `width`-bit pattern (`roundCore_lt`).
-/

namespace Mips.Fp

namespace Format

variable (f : Format)

/-! ## Fields and classes -/

theorem signOf_eq (n : Nat) : f.signOf n = f.signBit n := by
  simp only [signOf, signBit]; cases h : (n / 2 ^ (f.expBits + f.fracBits)) % 2 == 1 <;> simp_all

theorem isNaN_iff (n : Nat) : f.isNaN n = true ↔ f.IsNaN n := by
  simp [isNaN, IsNaN, expOf, fracOf, expField, fracField, expMax]

theorem isSNaN_iff (n : Nat) : f.isSNaN n = true ↔ f.IsSNaN n := by
  simp [isSNaN, IsSNaN, ← isNaN_iff, fracOf, fracField]

theorem isQNaN_iff (n : Nat) : f.isQNaN n = true ↔ f.IsQNaN n := by
  simp [isQNaN, IsQNaN, ← isNaN_iff, fracOf, fracField]

theorem infBits_eq (s : Bool) : f.infBits s = f.inf s := by
  simp [infBits, inf, pack, expMax]

theorem zeroBits_eq (s : Bool) : f.zeroBits s = f.zero s := by
  simp [zeroBits, zero, pack]

theorem newQNaN_eq : f.newQNaN = f.defaultQNaN := by
  simp [newQNaN, defaultQNaN, pack, expMax]

theorem invalidResult_eq : f.invalidResult = (f.defaultQNaN, Flags.invalidOnly) := by
  simp [invalidResult, newQNaN_eq, Flags.invalidOnly]

/-- The new QNaN is a quiet NaN (Table 6.3 against Table 6.2). -/
theorem newQNaN_isQNaN (hf : f.WF) : f.IsQNaN f.newQNaN := by
  have h2 := hf.2
  have hq : 2 ^ (f.fracBits - 1) - 1 < 2 ^ f.fracBits := by
    have := Nat.pow_lt_pow_right (a := 2) (by omega) (show f.fracBits - 1 < f.fracBits by omega)
    have := Nat.two_pow_pos (f.fracBits - 1)
    omega
  have hq1 : 1 ≤ 2 ^ (f.fracBits - 1) - 1 := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) (show 1 ≤ f.fracBits - 1 by omega)
    simp at this; omega
  obtain ⟨e1, e2, -, -⟩ := f.pack_fields false f.expMax _ f.expMax_lt hq
  have hpk : f.newQNaN = f.pack false f.expMax (2 ^ (f.fracBits - 1) - 1) := by
    rw [newQNaN_eq]; rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [expOf, hpk]; exact e1
  · simp only [fracOf, hpk, e2]; omega
  · simp only [fracOf, hpk, e2]
    exact Nat.div_eq_of_lt (by have := Nat.two_pow_pos (f.fracBits - 1); omega)

/-! ## The datum of an encoding -/

theorem datum_of_nan {n : Nat} (h : f.isNaN n = true) : f.datum n = .nan := by
  have h' := h
  simp only [isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h'
  simp only [datum, value_none_of_expMax f n h'.1, fracOf]
  simp only [fracField] at h'
  simp [h'.2]

theorem datum_of_inf {n : Nat} (h : f.isInf n = true) : f.datum n = .inf (f.signBit n) := by
  have h' := h
  simp only [isInf, Bool.and_eq_true, beq_iff_eq] at h'
  simp only [datum, value_none_of_expMax f n h'.1, fracOf, signOf_eq]
  simp only [fracField] at h'
  simp [h'.2]

theorem datum_of_finite {n : Nat} (hn : n < 2 ^ f.width) (h : f.expField n ≠ f.expMax) :
    f.datum n = .num (f.signBit n) (f.toExact n).toRat := by
  simp only [datum, value_eq_toExact f n hn h, signOf_eq]

theorem toRat_eq_zero_iff (v : Exact) : v.toRat = 0 ↔ v.sig = 0 := by
  constructor
  · intro h; exact Classical.byContradiction fun h' => by
      have := rat_two_zpow_pos v.exp
      have hs : (0 : Rat) < v.sig := by exact_mod_cast Nat.pos_of_ne_zero h'
      have hm : (v.sig : Rat) * (2 : Rat) ^ v.exp ≠ 0 := by
        have := Rat.mul_pos hs this; grind
      simp only [Exact.toRat] at h
      cases v.sign <;> grind
  · intro h; simp [Exact.toRat, h]

theorem toExact_sig_zero_iff (n : Nat) :
    (f.toExact n).sig = 0 ↔ f.isZero n = true := by
  simp only [toExact, isZero, Bool.and_eq_true, beq_iff_eq]
  split
  · rename_i h; simp [h]
  · rename_i h; simp only [h, false_and, iff_false]
    have := Nat.two_pow_pos f.fracBits; omega

/-- **The three classes are exhaustive** on `width`-bit patterns: a NaN, an infinity, or a finite
number whose value is that of `toExact` (and which is zero iff `isZero`). -/
theorem classify (hf : f.WF) (n : Nat) (hn : n < 2 ^ f.width) :
    (f.isNaN n = true ∧ f.isInf n = false ∧ f.datum n = .nan) ∨
    (f.isNaN n = false ∧ f.isInf n = true ∧ f.isZero n = false ∧
      f.datum n = .inf (f.signBit n)) ∨
    (f.isNaN n = false ∧ f.isInf n = false ∧ f.expField n ≠ f.expMax ∧
      f.datum n = .num (f.signBit n) (f.toExact n).toRat ∧
      f.value n = some (f.toExact n).toRat ∧
      ((f.toExact n).toRat = 0 ↔ f.isZero n = true)) := by
  have hM : 1 ≤ f.expMax := by
    simp only [expMax]; have := Nat.pow_le_pow_right (n := 2) (by omega) hf.1; simp at this; omega
  by_cases he : f.expField n = f.expMax
  · by_cases hz : f.fracField n = 0
    · have hi : f.isInf n = true := by simp [isInf, he, hz]
      refine .inr (.inl ⟨by simp [isNaN, hz], hi, by simp [isZero, he]; omega, f.datum_of_inf hi⟩)
    · have hi : f.isNaN n = true := by simp [isNaN, he, hz]
      exact .inl ⟨hi, by simp [isInf, hz], f.datum_of_nan hi⟩
  · refine .inr (.inr ⟨by simp [isNaN, he], by simp [isInf, he], he, f.datum_of_finite hn he,
      value_eq_toExact f n hn he, ?_⟩)
    rw [toRat_eq_zero_iff, toExact_sig_zero_iff f]

/-! ## The NaN rule -/

/-- **The model's NaN rule meets `NaNResult`** for any operand list. -/
theorem nanResult_spec (hf : f.WF) (ops : List Nat) :
    f.NaNResult ops (f.nanResult ops, f.nanFlags ops) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp only [nanFlags, List.any_eq_true, ← isSNaN_iff]
  · unfold nanResult
    split
    · rename_i q hq
      have h1 := List.find?_some hq
      have h2 := List.mem_of_find?_eq_some hq
      exact ⟨(f.isQNaN_iff q).1 h1, fun _ => h2, fun hn => absurd ((f.isQNaN_iff q).1 h1) (hn q h2)⟩
    · rename_i hn
      rw [List.find?_eq_none] at hn
      refine ⟨f.newQNaN_eq ▸ f.newQNaN_isQNaN hf, fun ⟨x, hx, hq⟩ => ?_, fun _ => (f.newQNaN_eq).symm⟩
      exact absurd ((f.isQNaN_iff x).2 hq) (by simpa using hn x hx)

/-- **The pin**: with a quiet NaN among the operands, the model returns the first one in operand
order (SPEC-NOTES §9 item 13). -/
theorem nanResult_first (ops : List Nat) (q : Nat) (h : ops.find? (fun x => f.isQNaN x) = some q) :
    f.nanResult ops = q := by
  simp [nanResult, h]

/-! ## Results are `width`-bit patterns -/

theorem pack_lt (s : Bool) (e fr : Nat) (he : e < 2 ^ f.expBits) (hfr : fr < 2 ^ f.fracBits) :
    f.pack s e fr < 2 ^ f.width := (f.pack_fields s e fr he hfr).2.2.2

theorem zero_lt (s : Bool) : f.zero s < 2 ^ f.width :=
  f.pack_lt s 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _)

theorem inf_lt (s : Bool) : f.inf s < 2 ^ f.width :=
  f.pack_lt s _ 0 f.expMax_lt (Nat.two_pow_pos _)

theorem defaultQNaN_lt (hf : f.WF) : f.defaultQNaN < 2 ^ f.width := by
  have h2 := hf.2
  refine f.pack_lt false _ _ f.expMax_lt ?_
  have := Nat.pow_lt_pow_right (a := 2) (by omega) (show f.fracBits - 1 < f.fracBits by omega)
  have := Nat.two_pow_pos (f.fracBits - 1)
  omega

theorem overflowResult_lt (rm : RoundingMode) (s : Bool) : f.overflowResult rm s < 2 ^ f.width := by
  rw [← overflow_bits]
  have hF : 2 ^ f.fracBits - 1 < 2 ^ f.fracBits := by have := Nat.two_pow_pos f.fracBits; omega
  have hE : f.expMax - 1 < 2 ^ f.expBits := by have := f.expMax_lt; omega
  split <;> (try split) <;> first | exact f.inf_lt s | exact f.pack_lt s _ _ hE hF

theorem roundSpec_lt {rm : RoundingMode} {c : Cut} {R : Rounded} (h : f.RoundSpec rm c R) :
    R.bits < 2 ^ f.width := by
  obtain ⟨r, -, -, hv, hov, -⟩ := h
  cases ho : R.overflow
  · exact (value_some_lt f (hv ho)).1
  · obtain ⟨neg, -, hb⟩ := hov ho
    rw [hb]; exact f.overflowResult_lt rm neg

/-- Every encoding the rounding core delivers is a `width`-bit pattern. -/
theorem roundCore_lt (hf : f.WF) (rm : RoundingMode) (fl : Bool) (w : Exact) :
    (f.roundCore rm fl w).bits < 2 ^ f.width := by
  by_cases hw : w.sig = 0
  · rw [roundCore_zero f rm fl w hw]; exact f.zero_lt _
  · have hc := roundCore_correct f hf rm w hw _ (Cut.ofRat_valid _) (CutAgree.ofRat _ _)
    cases fl
    · exact f.roundSpec_lt hc
    · by_cases ht : w.toRat.abs < (2 : Rat) ^ f.emin
      · rw [roundCore_flush_tiny f rm w hw ht]; exact f.zero_lt _
      · rw [roundCore_flush_normal f rm w hw ht]; exact f.roundSpec_lt hc

theorem roundEnv_lt (hf : f.WF) (e : Env) (w : Exact) : (f.roundEnv e w).1 < 2 ^ f.width :=
  f.roundCore_lt hf _ _ w

theorem nanResult_lt (hf : f.WF) (ops : List Nat) (hops : ∀ x ∈ ops, x < 2 ^ f.width) :
    f.nanResult ops < 2 ^ f.width := by
  unfold nanResult
  split
  · rename_i q hq; exact hops q (List.mem_of_find?_eq_some hq)
  · exact f.defaultQNaN_lt hf

end Format

/-- Table 6.3 (MD00082 Vol I-A Rev 6.01, p.82): the single new QNaN is `0x7fbf ffff`. -/
theorem newQNaN_binary32 : binary32.newQNaN = 0x7FBFFFFF := by decide

/-- Table 6.3: the double new QNaN is `0x7ff7 ffff ffff ffff`. -/
theorem newQNaN_binary64 : binary64.newQNaN = 0x7FF7FFFFFFFFFFFF := by decide

end Mips.Fp
