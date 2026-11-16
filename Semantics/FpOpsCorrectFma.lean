import Semantics.FpOpsCorrectIEEE

/-!
# FpOpsCorrectFma — `MADDF.fmt` / `MSUBF.fmt` on every operand (Wave R6-6)

`Format.fma` (the fused multiply-add of `FpOps.lean` §12) meets `Format.FmaSpec` of
`Semantics/FpOpsSpec.lean` for **all** `width`-bit operands (NaN, ±∞, ±0, finite) and every FCSR
environment (rounding mode, Enables, FS): `Format.fma_spec`. The finite case is one rounding
(`roundEnv_spec_rat`) of the exact sum `Exact.add` of the addend and the exact product `Exact.mul`.
`f32Fma_spec` / `f64Fma_spec` lift it to the `BitVec` wrappers, each operand flushed under FCSR.FS
(`FlushedIn`), as `f32Add_spec` does (MD00086 Vol II-A Rev 6.06, MADDF.fmt / MSUBF.fmt, p.259-260).
-/

namespace Mips.Fp

/-- The value of an `Exact` with its sign replaced. -/
theorem Exact.toRat_withSign (q : Exact) (s : Bool) :
    ({ q with sign := s } : Exact).toRat = if s = q.sign then q.toRat else -q.toRat := by
  obtain ⟨qs, m, E⟩ := q
  simp only [Exact.toRat]
  cases s <;> cases qs <;> simp <;> grind

namespace Format

variable (f : Format)

theorem bne_xor (x y : Bool) : (x != y) = (x ^^ y) := rfl

theorem toExact_sign (n : Nat) : (f.toExact n).sign = f.signBit n := by
  simp only [toExact]; split <;> rfl

/-- The model's `infTimesZero` is `InfTimesZero` (on every `width`-bit pair). -/
theorem infTimesZero_iff (hf : f.WF) {a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    f.infTimesZero a b = true ↔ f.InfTimesZero a b := by
  have nz : ∀ n, f.isNaN n = true → f.isZero n = false := by
    intro n h; simp only [isNaN, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp [isZero, h.2]
  rcases f.classify hf a ha with ⟨na, ia, da⟩ | ⟨na, ia, za, da⟩ | ⟨na, ia, -, da, -, za⟩
  all_goals rcases f.classify hf b hb with ⟨nb, ib, db⟩ | ⟨nb, ib, zb, db⟩ | ⟨nb, ib, -, db, -, zb⟩
  all_goals simp [infTimesZero, InfTimesZero, nz a, nz b, *]

/-- The NaN arm of the model meets `FmaNaNResult`. -/
theorem fma_nan_spec (hf : f.WF) {c a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    f.FmaNaNResult c a b
      (f.nanResult [c, a, b],
        { invalid := [c, a, b].any (fun x => f.isSNaN x) || f.infTimesZero a b }) := by
  refine ⟨⟨[c, a, b].any (fun x => f.isSNaN x), f.nanResult_spec hf _⟩, ?_⟩
  simp only [Bool.or_eq_true, List.any_eq_true, ← isSNaN_iff, f.infTimesZero_iff hf ha hb]

/-- **`MADDF.fmt` / `MSUBF.fmt` meet `FmaSpec`** on every triple of `width`-bit operands, every
FCSR environment and both signs of the product. -/
theorem fma_spec (hf : f.WF) (e : Env) (sub : Bool) {c a b : Nat} (hc : c < 2 ^ f.width)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    f.FmaSpec e sub c a b (f.fma e sub c a b) := by
  have hN := f.fma_nan_spec hf (c := c) ha hb
  by_cases hn : f.isNaN c = true ∨ f.isNaN a = true ∨ f.isNaN b = true
  · have hr : f.fma e sub c a b = (f.nanResult [c, a, b],
        { invalid := [c, a, b].any (fun x => f.isSNaN x) || f.infTimesZero a b }) := by
      simp only [fma]; rcases hn with h | h | h <;> simp [h]
    rw [hr]
    rcases hn with h | h | h
    · simp only [FmaSpec, f.datum_of_nan h]; exact hN
    · rcases f.classify hf c hc with ⟨-, -, dc⟩ | ⟨-, -, -, dc⟩ | ⟨-, -, -, dc, -⟩ <;>
        simp only [FmaSpec, dc, f.datum_of_nan h] <;> exact hN
    · rcases f.classify hf c hc with ⟨-, -, dc⟩ | ⟨-, -, -, dc⟩ | ⟨-, -, -, dc, -⟩ <;>
      rcases f.classify hf a ha with ⟨-, -, da⟩ | ⟨-, -, -, da⟩ | ⟨-, -, -, da, -⟩ <;>
        simp only [FmaSpec, dc, da, f.datum_of_nan h] <;> exact hN
  · simp only [not_or, Bool.not_eq_true] at hn
    obtain ⟨nc, na, nb⟩ := hn
    have hz := f.infTimesZero_iff hf ha hb
    rcases f.classify hf c hc with ⟨h1, -⟩ | ⟨-, ic, zc, dc⟩ | ⟨-, ic, -, dc, vc, zc⟩
    · simp [h1] at nc
    all_goals rcases f.classify hf a ha with ⟨h1, -⟩ | ⟨-, ia, za, da⟩ | ⟨-, ia, -, da, va, za⟩
    all_goals (try simp [h1] at na)
    all_goals rcases f.classify hf b hb with ⟨h1, -⟩ | ⟨-, ib, zb, db⟩ | ⟨-, ib, -, db, vb, zb⟩
    all_goals (try simp [h1] at nb)
    · -- ∞, ∞, ∞
      simp only [FmaSpec, dc, da, db, FmaInfProduct, fma, nc, na, nb, infTimesZero, ia, ib, ic, za, zb,
        Bool.or_self, Bool.false_eq_true, ite_false, Bool.and_false, ite_true, Bool.true_and, bne_xor]
      by_cases h : f.signBit c = (f.signBit a ^^ f.signBit b ^^ sub) <;>
        simp [h, infBits_eq, invalidResult_eq, flags_none, flags_invalidOnly]
    · -- ∞, ∞, finite
      by_cases hb0 : f.isZero b = true
      · simp [FmaSpec, dc, da, db, zb.2 hb0, fma, nc, na, nb, infTimesZero, ia, hb0, invalidResult_eq,
          flags_invalidOnly]
      · have hb1 : (f.toExact b).toRat ≠ 0 := fun h => hb0 (zb.1 h)
        simp only [Bool.not_eq_true] at hb0
        simp only [FmaSpec, dc, da, db, hb1, FmaInfProduct, fma, nc, na, nb, infTimesZero, ia, ib, ic, za,
          hb0, Bool.or_self, Bool.false_eq_true, ite_false, Bool.and_false, ite_true, Bool.true_and,
          Bool.or_false, bne_xor]
        by_cases h : f.signBit c = (f.signBit a ^^ f.signBit b ^^ sub) <;>
          simp [h, infBits_eq, invalidResult_eq, flags_none, flags_invalidOnly]
    · -- ∞, finite, ∞
      by_cases ha0 : f.isZero a = true
      · simp [FmaSpec, dc, da, db, za.2 ha0, fma, nc, na, nb, infTimesZero, ib, ha0, invalidResult_eq,
          flags_invalidOnly]
      · have ha1 : (f.toExact a).toRat ≠ 0 := fun h => ha0 (za.1 h)
        simp only [Bool.not_eq_true] at ha0
        simp only [FmaSpec, dc, da, db, ha1, FmaInfProduct, fma, nc, na, nb, infTimesZero, ia, ib, ic, zb,
          ha0, Bool.or_self, Bool.false_eq_true, ite_false, Bool.and_false, ite_true, Bool.true_and,
          Bool.or_true, Bool.false_and, Bool.or_false, bne_xor]
        by_cases h : f.signBit c = (f.signBit a ^^ f.signBit b ^^ sub) <;>
          simp [h, infBits_eq, invalidResult_eq, flags_none, flags_invalidOnly]
    · -- ∞, finite, finite
      simp only [FmaSpec, dc, da, db, fma, nc, na, nb, infTimesZero, ia, ib, ic, Bool.or_self,
        Bool.false_eq_true, ite_false, Bool.false_and, Bool.and_false, ite_true, infBits_eq, flags_none]
      exact congrArg (·, _) (f.eq_inf_of_isInf hc ic)
    · -- finite, ∞, ∞
      simp only [FmaSpec, dc, da, db, FmaInfProduct, fma, nc, na, nb, infTimesZero, ia, ib, ic, za, zb,
        Bool.or_self, Bool.false_eq_true, ite_false, Bool.and_false, ite_true, Bool.false_and, bne_xor,
        infBits_eq, flags_none]
    · -- finite, ∞, finite
      by_cases hb0 : f.isZero b = true
      · simp [FmaSpec, dc, da, db, zb.2 hb0, fma, nc, na, nb, infTimesZero, ia, hb0, invalidResult_eq,
          flags_invalidOnly]
      · have hb1 : (f.toExact b).toRat ≠ 0 := fun h => hb0 (zb.1 h)
        simp only [Bool.not_eq_true] at hb0
        simp only [FmaSpec, dc, da, db, hb1, FmaInfProduct, fma, nc, na, nb, infTimesZero, ia, ib, ic, za,
          hb0, Bool.or_self, Bool.false_eq_true, ite_false, Bool.and_false, ite_true, Bool.false_and,
          Bool.or_false, bne_xor, infBits_eq, flags_none]
    · -- finite, finite, ∞
      by_cases ha0 : f.isZero a = true
      · simp [FmaSpec, dc, da, db, za.2 ha0, fma, nc, na, nb, infTimesZero, ib, ha0, invalidResult_eq,
          flags_invalidOnly]
      · have ha1 : (f.toExact a).toRat ≠ 0 := fun h => ha0 (za.1 h)
        simp only [Bool.not_eq_true] at ha0
        simp only [FmaSpec, dc, da, db, ha1, FmaInfProduct, fma, nc, na, nb, infTimesZero, ia, ib, ic, zb,
          ha0, Bool.or_self, Bool.false_eq_true, ite_false, Bool.and_false, ite_true, Bool.false_and,
          Bool.or_true, Bool.or_false, bne_xor, infBits_eq, flags_none]
    · -- finite, finite, finite
      simp only [FmaSpec, dc, da, db, fma, nc, na, nb, infTimesZero, ia, ib, ic, Bool.or_self,
        Bool.false_eq_true, ite_false, Bool.false_and, Bool.and_false]
      generalize hq : ({ Exact.mul (f.toExact a) (f.toExact b) with
        sign := (f.signBit a != f.signBit b) != sub } : Exact) = q
      have hqv : q.toRat =
          if sub then -((f.toExact a).toRat * (f.toExact b).toRat)
          else (f.toExact a).toRat * (f.toExact b).toRat := by
        rw [← hq, Exact.toRat_withSign, Exact.mul_toRat]
        simp only [Exact.mul, toExact_sign]
        cases sub <;> simp
      have hqs : q.sign = (f.signBit a ^^ f.signBit b ^^ sub) := by rw [← hq]
      have hw := Exact.add_toRat e.rm (f.toExact c) q
      have hv : (if sub then (f.toExact c).toRat - (f.toExact a).toRat * (f.toExact b).toRat
          else (f.toExact c).toRat + (f.toExact a).toRat * (f.toExact b).toRat) =
          (Exact.add e.rm (f.toExact c) q).toRat := by
        rw [hw, hqv]; cases sub <;> simp [Rat.sub_eq_add_neg]
      rw [hv]
      by_cases hv0 : (Exact.add e.rm (f.toExact c) q).toRat = 0
      · simp only [hv0, ↓reduceIte]
        obtain ⟨h0, hsg⟩ := Exact.add_zero e.rm _ _ hv0
        rw [f.roundEnv_zero e _ h0, hsg, zeroBits_eq, toExact_sign, hqs]
        by_cases hs : f.signBit c = (f.signBit a ^^ f.signBit b ^^ sub) <;> simp [hs]
      · simp only [hv0, ↓reduceIte]
        exact f.roundEnv_spec_rat hf e _ (Format.exact_sig_ne_zero hv0)

/-- The encoding `fma` delivers is a `width`-bit pattern. -/
theorem fma_lt (hf : f.WF) (e : Env) (sub : Bool) {c a b : Nat} (hc : c < 2 ^ f.width)
    (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) : (f.fma e sub c a b).1 < 2 ^ f.width := by
  have hops : ∀ x ∈ [c, a, b], x < 2 ^ f.width := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  unfold fma
  dsimp only
  repeat' split
  all_goals first
    | exact hc | exact f.defaultQNaN_lt hf | exact f.inf_lt _ | exact f.roundEnv_lt hf _ _
    | exact f.nanResult_lt hf _ hops

end Format

/-! ## The `BitVec` wrappers -/

/-- **`MADDF.S` (`sub = false`) / `MSUBF.S` (`sub = true`)** on all operands, every FCSR environment;
each operand flushed under FCSR.FS (`FlushedIn`), the flush signaling Inexact (`WithFlushInexact`). -/
theorem f32Fma_spec (e : Env) (sub : Bool) (c a b : BitVec 32) :
    binary32.WithFlushInexact e.flush [c.toNat, a.toNat, b.toNat]
      (binary32.FmaSpec e sub (binary32.FlushedIn e.flush c.toNat) (binary32.FlushedIn e.flush a.toNat)
        (binary32.FlushedIn e.flush b.toNat))
      ((f32Fma e sub c a b).1.toNat, (f32Fma e sub c a b).2) := by
  have hc := binary32.flushIn_lt e.flush c.isLt
  have ha := binary32.flushIn_lt e.flush a.isLt; have hb := binary32.flushIn_lt e.flush b.isLt
  simp only [f32Fma, Format.withFlush, ← Format.flushIn_eq]
  rw [toNat_ofNat_lt (w := 32) (binary32.fma_lt binary32_wf e sub hc ha hb)]
  exact binary32.withFlush_intro _ _ _ _ _ (binary32.fma_spec binary32_wf e sub hc ha hb)

/-- **`MADDF.D` / `MSUBF.D`** on all operands, every FCSR environment; each operand flushed under
FCSR.FS (`FlushedIn`). -/
theorem f64Fma_spec (e : Env) (sub : Bool) (c a b : BitVec 64) :
    binary64.WithFlushInexact e.flush [c.toNat, a.toNat, b.toNat]
      (binary64.FmaSpec e sub (binary64.FlushedIn e.flush c.toNat) (binary64.FlushedIn e.flush a.toNat)
        (binary64.FlushedIn e.flush b.toNat))
      ((f64Fma e sub c a b).1.toNat, (f64Fma e sub c a b).2) := by
  have hc := binary64.flushIn_lt e.flush c.isLt
  have ha := binary64.flushIn_lt e.flush a.isLt; have hb := binary64.flushIn_lt e.flush b.isLt
  simp only [f64Fma, Format.withFlush, ← Format.flushIn_eq]
  rw [toNat_ofNat_lt (w := 64) (binary64.fma_lt binary64_wf e sub hc ha hb)]
  exact binary64.withFlush_intro _ _ _ _ _ (binary64.fma_spec binary64_wf e sub hc ha hb)

end Mips.Fp
