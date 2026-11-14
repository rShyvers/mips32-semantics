import Semantics.Manual.Accuracy
import Semantics.FpOpsCorrectRsqrt

/-!
# Refine.ImplValid — the model's implementation constants are valid

`Manual.modelImpl_valid`: `Manual.modelImpl` (`RECIP` = `DIV.fmt` of `1.0`, `RSQRT` = `SQRT.fmt` then
`DIV.fmt`) is of this profile and meets the accuracy of RECIP.fmt (p.336) and RSQRT.fmt (p.343),
against the IEEE-mandated representation and against the exact result. The exact-result bounds come
from the correctness of the IEEE rounding core (`Semantics/FpOpsCorrect*.lean`).
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
      simp only [modelImpl, f32Div, f32Sqrt, BitVec.toNat_ofNat]
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
      simp only [modelImpl, f64Div, f64Sqrt, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt w2, show (4607182418800017408 % 2 ^ 64 : Nat) = 0x3FF0000000000000 by decide,
        Nat.mod_eq_of_lt w1]
    rw [hb] at hrv
    have : r = r' := Option.some.inj (hrv.symm.trans hv)
    subst this
    refine ⟨ex, h1, h2, ?_, ?_⟩ <;> simp only [ULP_binary64, Rat.natCast_ofNat] <;> assumption

/-- **`modelImpl` is a valid implementation** (`Impl.Valid`: `Impl.WF`, `RECIP.fmt` within 1 ULP of
the IEEE-mandated representation and of the exact result, `RSQRT.fmt` within 2 ULP of the exact
result). -/
theorem modelImpl_valid : modelImpl.Valid :=
  ⟨modelImpl_WF, modelImpl_recipAccurate, modelImpl_recipExact, modelImpl_rsqrtAccurate⟩

end Manual
