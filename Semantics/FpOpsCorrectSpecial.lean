import Semantics.FpOpsCorrectApi

/-!
# FpOpsCorrectSpecial — the encodings' classes, the special results, the NaN rule

Bridges the classes of `Semantics/FpOpsSpec.lean` (`Format.IsNaN`, `IsSNaN`, `IsQNaN`, `datum`,
`infBits`, `zeroBits`, `newQNaN`, Table 6.2 / 6.3 of MD00082 Vol I-A Rev 6.01) with the model's
Boolean tests (`Format.isNaN`, …), and proves the model's NaN rule (`nanResult`, `nanFlags`) meets
`Format.NaNResult`, its first-SNaN-else-first-QNaN choice being the documented pin (`nanResult_first`,
`nanResult_first_snan`); `quiet_eq_passedNaN` identifies the model's `quiet` with `passedNaN`. Also: every
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
  have hq : 2 ^ (f.fracBits - 1) < 2 ^ f.fracBits :=
    Nat.pow_lt_pow_right (a := 2) (by omega) (show f.fracBits - 1 < f.fracBits by omega)
  have hq1 : 1 ≤ 2 ^ (f.fracBits - 1) := Nat.one_le_two_pow
  obtain ⟨e1, e2, -, -⟩ := f.pack_fields false f.expMax _ f.expMax_lt hq
  have hpk : f.newQNaN = f.pack false f.expMax (2 ^ (f.fracBits - 1)) := by
    rw [newQNaN_eq]; rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [expOf, hpk]; exact e1
  · simp only [fracOf, hpk, e2]; omega
  · simp only [fracOf, hpk, e2]
    exact Nat.div_self (Nat.two_pow_pos _)

/-! ## Quieting a NaN -/

theorem nat_or_two_pow_split (n k : Nat) :
    (n / 2 ^ k % 2 = 1 → n ||| 2 ^ k = n) ∧ (n / 2 ^ k % 2 = 0 → n ||| 2 ^ k = n + 2 ^ k) := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_or, Nat.testBit_two_pow]
    by_cases hi : k = i
    · subst hi; simp [Nat.testBit_eq_decide_div_mod_eq, h]
    · simp [hi]
  · intro h
    have hr : n % 2 ^ (k + 1) < 2 ^ k := by
      rw [Nat.pow_succ]
      have := Nat.mod_mul_right_div_self n (2 ^ k) 2
      rw [h] at this
      have := Nat.div_add_mod (n % (2 ^ k * 2)) (2 ^ k)
      have := Nat.mod_lt (n % (2 ^ k * 2)) (Nat.two_pow_pos k)
      rw [‹n % (2 ^ k * 2) / 2 ^ k = 0›] at *
      omega
    have hd := (Nat.div_add_mod n (2 ^ (k + 1))).symm
    have h1 : n % 2 ^ (k + 1) + 2 ^ k < 2 ^ (k + 1) := by
      have : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..; omega
    calc n ||| 2 ^ k = (2 ^ (k + 1) * (n / 2 ^ (k + 1)) ||| n % 2 ^ (k + 1)) ||| 2 ^ k := by
          rw [← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), ← hd]
      _ = 2 ^ (k + 1) * (n / 2 ^ (k + 1)) ||| (n % 2 ^ (k + 1) + 2 ^ k) := by
          rw [Nat.or_assoc, Nat.or_two_pow_eq_add_of_lt hr]
      _ = n + 2 ^ k := by
          rw [← Nat.two_pow_add_eq_or_of_lt h1]; omega

/-- The fraction MSB `b1` of an encoding is its bit `fracBits - 1`. -/
theorem fracMsb_eq (hf : f.WF) (n : Nat) :
    f.fracField n / 2 ^ (f.fracBits - 1) = n / 2 ^ (f.fracBits - 1) % 2 := by
  obtain ⟨k, hk⟩ : ∃ k, f.fracBits = k + 1 := ⟨f.fracBits - 1, by have := hf.2; omega⟩
  simp only [fracField, hk, Nat.add_sub_cancel, Nat.pow_succ, Nat.mod_mul_right_div_self]

/-- The model's `quiet` is the specification's `passedNaN` (`b1` set, every other bit kept). -/
theorem quiet_eq_passedNaN (hf : f.WF) (n : Nat) : f.quiet n = f.passedNaN n := by
  have hs := nat_or_two_pow_split n (f.fracBits - 1)
  simp only [quiet, passedNaN, fracMsb_eq f hf]
  have := Nat.mod_two_eq_zero_or_one (n / 2 ^ (f.fracBits - 1))
  split
  · rename_i h; simp at h; exact (hs.1 h).symm
  · rename_i h; simp at h; rw [hs.2 (by omega)]

/-- A quiet NaN is passed unchanged. -/
theorem passedNaN_of_isQNaN (hf : f.WF) {q : Nat} (h : f.IsQNaN q) : f.passedNaN q = q := by
  have := h.2
  simp only [fracOf] at this
  rw [show q % 2 ^ f.fracBits = f.fracField q from rfl, fracMsb_eq f hf] at this
  exact (nat_or_two_pow_split q _).1 this

/-- Setting `b1` of an encoding whose biased exponent is all ones gives a quiet NaN (whatever the
fraction was). -/
theorem passedNaN_isQNaN_of_exp (hf : f.WF) {x : Nat} (hx : f.expOf x = 2 ^ f.expBits - 1) :
    f.IsQNaN (f.passedNaN x) := by
  have h2 := hf.2
  have hlt : 2 ^ (f.fracBits - 1) < 2 ^ f.fracBits :=
    Nat.pow_lt_pow_right (a := 2) (by omega) (show f.fracBits - 1 < f.fracBits by omega)
  have hexp : f.expOf (f.passedNaN x) = f.expOf x := by
    simp only [expOf, passedNaN, Nat.or_div_two_pow, Nat.div_eq_of_lt hlt, Nat.or_zero]
  have hmsb : f.fracOf (f.passedNaN x) / 2 ^ (f.fracBits - 1) = 1 := by
    rw [show f.fracOf (f.passedNaN x) = f.fracField (f.passedNaN x) from rfl, fracMsb_eq f hf]
    have := Nat.testBit_eq_decide_div_mod_eq (x := f.passedNaN x) (i := f.fracBits - 1)
    simp only [passedNaN, Nat.testBit_or, Nat.testBit_two_pow, decide_true, Bool.or_true] at this
    exact of_decide_eq_true this.symm
  refine ⟨⟨hexp ▸ hx, fun h0 => ?_⟩, hmsb⟩
  rw [h0, Nat.zero_div] at hmsb; exact absurd hmsb (by decide)

/-- A NaN passed to the output is a quiet NaN. -/
theorem passedNaN_isQNaN (hf : f.WF) {x : Nat} (hx : f.IsNaN x) : f.IsQNaN (f.passedNaN x) :=
  f.passedNaN_isQNaN_of_exp hf hx.1

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
    · rename_i x hx
      have h1 := List.find?_some hx
      have h2 := List.mem_of_find?_eq_some hx
      have hn : f.IsNaN x := ((f.isSNaN_iff x).1 h1).1
      simp only [quiet_eq_passedNaN f hf]
      exact ⟨f.passedNaN_isQNaN hf hn, .inr ⟨x, h2, hn, rfl⟩, fun _ => ⟨x, h2, hn, rfl⟩⟩
    · split
      · rename_i q hq
        have h1 := List.find?_some hq
        have h2 := List.mem_of_find?_eq_some hq
        have hQ := (f.isQNaN_iff q).1 h1
        have hp := (f.passedNaN_of_isQNaN hf hQ).symm
        exact ⟨hQ, .inr ⟨q, h2, hQ.1, hp⟩, fun _ => ⟨q, h2, hQ.1, hp⟩⟩
      · rename_i hn
        rw [List.find?_eq_none] at hn
        refine ⟨f.newQNaN_eq ▸ f.newQNaN_isQNaN hf, .inl (f.newQNaN_eq).symm,
          fun ⟨x, hx, hq⟩ => ?_⟩
        exact absurd ((f.isQNaN_iff x).2 hq) (by simpa using hn x hx)

/-- **The pin**, no signaling NaN among the operands: the model returns the first quiet NaN operand
in operand order, unchanged (SPEC-NOTES §9 item 13). -/
theorem nanResult_first (ops : List Nat) (q : Nat) (hs : ops.find? (fun x => f.isSNaN x) = none)
    (h : ops.find? (fun x => f.isQNaN x) = some q) : f.nanResult ops = q := by
  simp [nanResult, hs, h]

/-- **The pin**, a signaling NaN among the operands: the model returns the first signaling NaN
operand in operand order, made quiet (SPEC-NOTES §9 item 13). -/
theorem nanResult_first_snan (ops : List Nat) (q : Nat)
    (h : ops.find? (fun x => f.isSNaN x) = some q) : f.nanResult ops = f.quiet q := by
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

theorem passedNaN_lt (hf : f.WF) {x : Nat} (hx : x < 2 ^ f.width) : f.passedNaN x < 2 ^ f.width := by
  have h2 := hf.2
  refine Nat.or_lt_two_pow hx (Nat.pow_lt_pow_right (a := 2) (by omega) ?_)
  simp only [width]; omega

theorem nanResult_lt (hf : f.WF) (ops : List Nat) (hops : ∀ x ∈ ops, x < 2 ^ f.width) :
    f.nanResult ops < 2 ^ f.width := by
  unfold nanResult
  split
  · rename_i q hq
    rw [quiet_eq_passedNaN f hf]; exact f.passedNaN_lt hf (hops q (List.mem_of_find?_eq_some hq))
  · split
    · rename_i q hq; exact hops q (List.mem_of_find?_eq_some hq)
    · exact f.defaultQNaN_lt hf

end Format

/-- Table 6.3 (MD00082 Vol I-A Rev 6.01, p.82, column `FCSR.NAN2008 = 1`): the single new QNaN is
`0x7fc0 0000`. -/
theorem newQNaN_binary32 : binary32.newQNaN = 0x7FC00000 := by decide

/-- Table 6.3 (column `FCSR.NAN2008 = 1`): the double new QNaN is `0x7ff8 0000 0000 0000`. -/
theorem newQNaN_binary64 : binary64.newQNaN = 0x7FF8000000000000 := by decide

end Mips.Fp
