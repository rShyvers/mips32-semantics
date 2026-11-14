import Semantics.FpOpsCorrectShape

/-!
# FpOpsCorrectPack — the encodings the core delivers

The value and the sign of `Format.pack s E fr` (a finite encoding), and the overflow encodings
(`inf`, `maxFinite`) as `Format.overflowResult`.
-/

namespace Mips.Fp

namespace Format

theorem expMax_lt (f : Format) : f.expMax < 2 ^ f.expBits := by
  simp only [expMax]; have := Nat.two_pow_pos f.expBits; omega

theorem toExact_pack (f : Format) (s : Bool) (E fr : Nat) (hE : E < 2 ^ f.expBits)
    (hfr : fr < 2 ^ f.fracBits) :
    f.toExact (f.pack s E fr) =
      if E = 0 then ⟨s, fr, f.qMin⟩ else ⟨s, fr + 2 ^ f.fracBits, (E : Int) - f.bias - f.fracBits⟩ := by
  obtain ⟨h1, h2, h3, -⟩ := f.pack_fields s E fr hE hfr
  have hs : f.signBit (f.pack s E fr) = s := by
    simp only [signBit, h3]; cases s <;> rfl
  simp only [toExact, expField, fracField, h1, h2, hs]

theorem signBit_pack (f : Format) (s : Bool) (E fr : Nat) (hE : E < 2 ^ f.expBits)
    (hfr : fr < 2 ^ f.fracBits) :
    (f.pack s E fr / 2 ^ (f.expBits + f.fracBits) % 2 = 1) ↔ s = true := by
  obtain ⟨-, -, h3, -⟩ := f.pack_fields s E fr hE hfr
  rw [h3]; cases s <;> simp

/-- **The value of a finite encoding assembled by `pack`.** -/
theorem value_pack (f : Format) (s : Bool) (E fr : Nat) (hE : E < f.expMax)
    (hfr : fr < 2 ^ f.fracBits) :
    f.value (f.pack s E fr) =
      some ((if s then -1 else 1) * ((if E = 0 then fr else fr + 2 ^ f.fracBits : Nat) : Rat) *
        (2 : Rat) ^ (if E = 0 then f.qMin else (E : Int) - f.bias - f.fracBits)) := by
  have hE' : E < 2 ^ f.expBits := Nat.lt_trans hE f.expMax_lt
  obtain ⟨h1, -, -, h4⟩ := f.pack_fields s E fr hE' hfr
  rw [value_eq_toExact f _ h4 (by simp only [expField] at h1 ⊢; rw [h1]; omega),
    toExact_pack f s E fr hE' hfr]
  split <;> simp [Exact.toRat]

theorem inf_eq (f : Format) (s : Bool) : f.inf s = f.pack s f.expMax 0 := rfl

theorem maxFinite_eq (f : Format) (s : Bool) :
    f.maxFinite s = f.pack s (f.expMax - 1) (2 ^ f.fracBits - 1) := rfl

/-- The core's overflow encoding is the one of Table 6.14. -/
theorem overflow_bits (f : Format) (rm : RoundingMode) (s : Bool) :
    (if (match rm with
        | .RN => true
        | .RZ => false
        | .RP => !s
        | .RM => s) = true then f.inf s else f.maxFinite s) = f.overflowResult rm s := by
  have e : 2 ^ f.expBits - 1 - 1 = 2 ^ f.expBits - 2 := by omega
  cases rm <;> cases s <;>
    simp [inf_eq, maxFinite_eq, pack, overflowResult, e, expMax]

theorem overflowResult_sign (f : Format) (rm : RoundingMode) (s : Bool) :
    (f.overflowResult rm s / 2 ^ (f.expBits + f.fracBits) % 2 = 1) ↔ s = true := by
  rw [← overflow_bits]
  have hF : 2 ^ f.fracBits - 1 < 2 ^ f.fracBits := by have := Nat.two_pow_pos f.fracBits; omega
  have hE : f.expMax - 1 < 2 ^ f.expBits := by have := f.expMax_lt; omega
  have a1 := signBit_pack f s _ 0 f.expMax_lt (Nat.two_pow_pos _)
  have a2 := signBit_pack f s _ _ hE hF
  rw [← inf_eq] at a1; rw [← maxFinite_eq] at a2
  split <;> (try split) <;> assumption

end Format

end Mips.Fp
