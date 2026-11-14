import Semantics.FpOpsCorrectSpecial

/-!
# FpOpsCorrectEnv — rounding under the whole FCSR environment

`Format.roundEnv e w` (the core under FCSR.RM, Enables and FS) meets `Format.RoundEnvSpec`: the
signaled exceptions are `Format.Signaled` of the rounding outcome (`signaled_flags`, MD00082 Vol I-A
Rev 6.01 §6.7.2.3/5/6, p.101-102), and with FCSR.FS = 1 a value tiny before rounding is flushed to the
zero of its sign with Underflow and Inexact (§6.7.2.4, p.102). Stated for any exact result `c` that the
core's `Exact` agrees with on the rounding grids (`CutAgree`), so it covers the sticky quotient and
root of `DIV`/`SQRT` as well as the exact sums and products.
-/

namespace Mips.Fp

/-- `Rounded.flags` signals exactly what `Format.Signaled` says. -/
theorem signaled_flags (en : Flags) (R : Format.Rounded) : Format.Signaled en R (R.flags en) := by
  refine ⟨rfl, rfl, Iff.rfl, ?_, ?_⟩ <;>
    simp [Format.Rounded.flags, Bool.and_eq_true, Bool.or_eq_true]

theorem exact_abs_ge (w : Exact) (hw : w.sig ≠ 0) :
    (2 : Rat) ^ (w.exp + (bitLen w.sig : Int) - 1) ≤ w.toRat.abs := by
  have hs : 0 < w.sig := Nat.pos_of_ne_zero hw
  have h2 := two_pow_bitLen_le w.sig hs
  have h3 := bitLen_pos w.sig hs
  rw [Exact.toRat_signed, abs_signed _ (Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (rat_two_zpow_pos _))),
    show (2 : Rat) ^ (w.exp + (bitLen w.sig : Int) - 1) = ((1 : Nat) : Rat) * (2 : Rat) ^ (w.exp + (bitLen w.sig : Int) - 1)
      by simp, nat_zpow_le_iff]
  rw [show min (w.exp + (bitLen w.sig : Int) - 1) w.exp = w.exp by omega,
    show (w.exp - w.exp).toNat = 0 by omega,
    show (w.exp + (bitLen w.sig : Int) - 1 - w.exp).toNat = bitLen w.sig - 1 by omega]
  simp only [Nat.pow_zero, Nat.mul_one, Nat.one_mul]; exact h2

theorem exact_sign_iff (w : Exact) (hw : w.sig ≠ 0) : w.sign = true ↔ w.toRat ≤ 0 := by
  have hp : 0 < (w.sig : Rat) * (2 : Rat) ^ w.exp :=
    Rat.mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hw) (rat_two_zpow_pos _)
  rw [Exact.toRat_signed]; cases w.sign <;> simp <;> grind

theorem rat_abs_lt_iff {x g : Rat} : x.abs < g ↔ -g < x ∧ x < g := by
  simp only [Rat.abs]; split <;> constructor <;> intro h <;> grind

namespace Format

variable (f : Format)

/-- **`roundEnv` meets `RoundEnvSpec`** for an exact result `c` that the core's `w` agrees with on
the rounding grids. -/
theorem roundEnv_spec (hf : f.WF) (e : Env) (w : Exact) (hw : w.sig ≠ 0) (c : Cut) (hc : c.Valid)
    (hag : CutAgree c w.toRat (w.exp + bitLen w.sig - ((f.fracBits + 1 : Nat) : Int) - 1)) :
    f.RoundEnvSpec e c (f.roundEnv e w) := by
  generalize he0 : w.exp + bitLen w.sig - ((f.fracBits + 1 : Nat) : Int) - 1 = e0 at hag
  have hsign : (w.sign = true ↔ c.ge 0) := by
    have : c.ge 0 ↔ w.toRat ≤ 0 := by have := (hag 0 e0 (Int.le_refl _)).2; simpa using this
    rw [this]; exact exact_sign_iff w hw
  have htiny : f.TinyBefore c ↔ w.toRat.abs < (2 : Rat) ^ f.emin := by
    rw [rat_abs_lt_iff]
    rcases Int.le_total e0 f.emin with hle | hle
    · have h1 : c.le ((2 : Rat) ^ f.emin) ↔ (2 : Rat) ^ f.emin ≤ w.toRat := by
        have := (hag 1 f.emin hle).1; simpa using this
      have h2 : c.ge (-(2 : Rat) ^ f.emin) ↔ w.toRat ≤ -(2 : Rat) ^ f.emin := by
        have := (hag (-1) f.emin hle).2; simpa [Rat.neg_mul] using this
      simp only [TinyBefore, h1, h2]; constructor <;> intro ⟨a, b⟩ <;> exact ⟨by grind, by grind⟩
    · have hge := exact_abs_ge w hw
      have hpow : (2 : Rat) ^ f.emin ≤ (2 : Rat) ^ e0 := two_zpow_le hle
      have hpow2 : (2 : Rat) ^ e0 ≤ (2 : Rat) ^ (w.exp + (bitLen w.sig : Int) - 1) := two_zpow_le (by omega)
      have h1 : c.le ((2 : Rat) ^ e0) ↔ (2 : Rat) ^ e0 ≤ w.toRat := by
        have := (hag 1 e0 (Int.le_refl _)).1; simpa using this
      have h2 : c.ge (-(2 : Rat) ^ e0) ↔ w.toRat ≤ -(2 : Rat) ^ e0 := by
        have := (hag (-1) e0 (Int.le_refl _)).2; simpa [Rat.neg_mul] using this
      have hpos := rat_two_zpow_pos f.emin
      constructor
      · rintro ⟨t1, t2⟩
        rw [rat_abs_lt_iff.symm.trans (Iff.rfl)] at *
        exfalso
        rcases (Rat.le_total : (0 : Rat) ≤ w.toRat ∨ w.toRat ≤ 0) with hv | hv
        · have : w.toRat.abs = w.toRat := by simp only [Rat.abs]; split <;> grind
          exact t1 (hc.le_of_le _ _ hpow (h1.2 (by grind)))
        · have : w.toRat.abs = -w.toRat := by simp only [Rat.abs]; split <;> grind
          exact t2 (hc.ge_of_le _ _ (Rat.neg_le_neg hpow) (h2.2 (by grind)))
      · rintro ⟨t1, t2⟩
        exfalso
        simp only [Rat.abs] at hge; split at hge <;> grind
  rw [roundEnv]
  constructor
  · intro hfl ht
    rw [hfl, roundCore_flush_tiny f e.rm w hw (htiny.1 ht)]
    exact ⟨w.sign, hsign, by simp [zeroBits_eq, Rounded.flags]⟩
  · intro hn
    have hcore := roundCore_correct f hf e.rm w hw c hc (he0 ▸ hag)
    have heq : f.roundCore e.rm e.flush w = f.roundCore e.rm false w := by
      cases hfl : e.flush
      · rfl
      · exact roundCore_flush_normal f e.rm w hw (fun h => hn ⟨hfl, htiny.2 h⟩)
    rw [heq]
    exact ⟨_, hcore, rfl, signaled_flags _ _⟩

/-- For a rational exact result (sums, products, conversions). -/
theorem roundEnv_spec_rat (hf : f.WF) (e : Env) (w : Exact) (hw : w.sig ≠ 0) :
    f.RoundEnvSpec e (Cut.ofRat w.toRat) (f.roundEnv e w) :=
  f.roundEnv_spec hf e w hw _ (Cut.ofRat_valid _) (CutAgree.ofRat _ _)

end Format

end Mips.Fp
