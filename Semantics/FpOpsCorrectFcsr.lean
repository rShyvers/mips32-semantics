import Semantics.FpOpsSpec

/-!
# FpOpsCorrectFcsr — the FCSR update of an FP operation

`Mips.Fp.fpUpdate` (used by `step` through `fpFinishS`/`fpFinishD`/`fpThen`) meets
`FcsrSpec` (MD00082 Vol I-A Rev 6.01 §6.7.1, p.99; CheckFPException, MD00086 Vol II-A Rev 6.06
§2.2.2.3.3, Figure 2.24, p.23), and `FcsrSpec` determines the new FCSR and the trap decision
uniquely (`fcsrSpec_unique`), so the reference is a complete description, not a loose constraint.
-/

namespace Mips.Fp

theorem toBits_getLsbD (fl : Flags) : ∀ k, k < 5 → fl.toBits.getLsbD k = flagBit fl k := by
  cases fl with
  | mk v z o u i => cases v <;> cases z <;> cases o <;> cases u <;> cases i <;> decide

theorem bv5_ne_zero (x : BitVec 5) : x ≠ 0#5 ↔ ∃ k, k < 5 ∧ x.getLsbD k = true := by
  constructor
  · intro h; refine Classical.byContradiction fun hn => h ?_
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_zero]
    cases hx : x.getLsbD i
    · rfl
    · exact absurd ⟨i, hi, hx⟩ hn
  · rintro ⟨k, hk, hx⟩ h; subst h; simp at hx

theorem lt32_cases (i : Nat) (h : i < 32) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
    i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨
    i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by
  omega

theorem lt5_cases (k : Nat) (h : k < 5) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega

/-- Every bit of the FCSR after `fpUpdate`. -/
theorem fpUpdate_bit (fcsr : BitVec 32) (fl : Flags) (i : Nat) (hi : i < 32) :
    (fpUpdate fcsr fl).1.getLsbD i =
      if 12 ≤ i ∧ i ≤ 16 then flagBit fl (i - 12)
      else if i = 17 then false
      else if 2 ≤ i ∧ i ≤ 6 then (fcsr.getLsbD i || (!fpeEnabled fcsr fl && flagBit fl (i - 2)))
      else fcsr.getLsbD i := by
  have h0 := toBits_getLsbD fl 0 (by omega)
  have h1 := toBits_getLsbD fl 1 (by omega)
  have h2 := toBits_getLsbD fl 2 (by omega)
  have h3 := toBits_getLsbD fl 3 (by omega)
  have h4 := toBits_getLsbD fl 4 (by omega)
  simp only [BitVec.getLsbD_eq_getElem (by decide : 0 < 5), BitVec.getLsbD_eq_getElem (by decide : 1 < 5),
    BitVec.getLsbD_eq_getElem (by decide : 2 < 5), BitVec.getLsbD_eq_getElem (by decide : 3 < 5),
    BitVec.getLsbD_eq_getElem (by decide : 4 < 5)] at h0 h1 h2 h3 h4
  unfold fpUpdate raiseFlags
  rcases lt32_cases i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;>
    split <;> rename_i he <;> simp [fcsrCauseMask, he, h0, h1, h2, h3, h4]

/-- The trap decision of `fpUpdate` is `fpeEnabled`. -/
theorem fpUpdate_trap (fcsr : BitVec 32) (fl : Flags) : (fpUpdate fcsr fl).2 = fpeEnabled fcsr fl := by
  unfold fpUpdate; split <;> simp_all

/-- Every bit of `setCause` (the Cause write of one operation of a multi-operation instruction). -/
theorem setCause_bit (fcsr : BitVec 32) (fl : Flags) (i : Nat) (hi : i < 32) :
    (setCause fcsr fl).getLsbD i =
      if 12 ≤ i ∧ i ≤ 16 then flagBit fl (i - 12)
      else if i = 17 then false
      else fcsr.getLsbD i := by
  have h0 := toBits_getLsbD fl 0 (by omega)
  have h1 := toBits_getLsbD fl 1 (by omega)
  have h2 := toBits_getLsbD fl 2 (by omega)
  have h3 := toBits_getLsbD fl 3 (by omega)
  have h4 := toBits_getLsbD fl 4 (by omega)
  simp only [BitVec.getLsbD_eq_getElem (by decide : 0 < 5), BitVec.getLsbD_eq_getElem (by decide : 1 < 5),
    BitVec.getLsbD_eq_getElem (by decide : 2 < 5), BitVec.getLsbD_eq_getElem (by decide : 3 < 5),
    BitVec.getLsbD_eq_getElem (by decide : 4 < 5)] at h0 h1 h2 h3 h4
  unfold setCause
  rcases lt32_cases i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;>
    simp [fcsrCauseMask, h0, h1, h2, h3, h4]

/-- The Enables bits, and so the trap decision, do not depend on the Cause bits. -/
theorem fpeEnabled_setCause (fcsr : BitVec 32) (c fl : Flags) :
    fpeEnabled (setCause fcsr c) fl = fpeEnabled fcsr fl := by
  unfold fpeEnabled
  have : (setCause fcsr c).extractLsb' 7 5 = fcsr.extractLsb' 7 5 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and]
    rw [setCause_bit _ _ _ (by omega)]
    simp only [show ¬ (12 ≤ 7 + k ∧ 7 + k ≤ 16) by omega, show ¬ (7 + k = 17) by omega, ite_false]
  rw [this]

/-- **The FCSR side of an operation does not depend on the Cause an earlier operation wrote**:
`fpUpdate` rewrites the whole Cause field and reads only Enables and Flags. -/
theorem fpUpdate_setCause (fcsr : BitVec 32) (c fl : Flags) :
    fpUpdate (setCause fcsr c) fl = fpUpdate fcsr fl := by
  refine Prod.ext (BitVec.eq_of_getLsbD_eq fun i hi => ?_) ?_
  · rw [fpUpdate_bit _ _ i hi, fpUpdate_bit _ _ i hi, fpeEnabled_setCause, setCause_bit _ _ i hi]
    by_cases r1 : 12 ≤ i ∧ i ≤ 16
    · simp only [r1, and_self, ite_true]
    · by_cases r2 : i = 17
      · simp only [r2, ite_true]
      · simp only [r1, r2, ite_false]
  · rw [fpUpdate_trap, fpUpdate_trap, fpeEnabled_setCause]

/-- A second Cause write replaces the first. -/
theorem setCause_setCause (fcsr : BitVec 32) (c d : Flags) :
    setCause (setCause fcsr c) d = setCause fcsr d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [setCause_bit _ _ i hi, setCause_bit _ _ i hi, setCause_bit _ _ i hi]
  by_cases r1 : 12 ≤ i ∧ i ≤ 16
  · simp only [r1, and_self, ite_true]
  · by_cases r2 : i = 17
    · simp only [r2, ite_true]
    · simp only [r1, r2, ite_false]

/-- A trapping `fpUpdate` writes exactly the Cause. -/
theorem fpUpdate_of_enabled (fcsr : BitVec 32) (fl : Flags) (h : fpeEnabled fcsr fl = true) :
    fpUpdate fcsr fl = (setCause fcsr fl, true) := by
  unfold fpUpdate setCause; simp [h]

/-- No exception before the first operation. -/
theorem Flags.none_or (f : Flags) : Flags.none.or f = f := by
  cases f; rfl

/-- **`fpUpdate` meets `FcsrSpec`.** -/
theorem fpUpdate_spec (fcsr : BitVec 32) (fl : Flags) :
    FcsrSpec fcsr fl (fpUpdate fcsr fl).1 (fpUpdate fcsr fl).2 := by
  have hb := fpUpdate_bit fcsr fl
  rw [fpUpdate_trap]
  refine ⟨?_, fun k hk => ?_, ?_, fun k hk => ?_, fun i hi h1 h2 => ?_⟩
  · rw [hb 17 (by omega)]; simp
  · rw [hb (12 + k) (by omega)]
    simp only [show 12 ≤ 12 + k ∧ 12 + k ≤ 16 by omega, and_self, ite_true, show 12 + k - 12 = k by omega]
  · rw [hb 17 (by omega)]
    simp only [show ¬ (12 ≤ 17 ∧ 17 ≤ 16) by omega, ite_false, ite_true, Bool.false_eq_true, false_or]
    have hc : ∀ k, k < 5 → (fpUpdate fcsr fl).1.getLsbD (12 + k) = flagBit fl k := fun k hk => by
      rw [hb (12 + k) (by omega)]
      simp only [show 12 ≤ 12 + k ∧ 12 + k ≤ 16 by omega, and_self, ite_true, show 12 + k - 12 = k by omega]
    have he : ∀ k, k < 5 → (fpUpdate fcsr fl).1.getLsbD (7 + k) = fcsr.getLsbD (7 + k) := fun k hk => by
      rw [hb (7 + k) (by omega)]
      simp only [show ¬ (12 ≤ 7 + k ∧ 7 + k ≤ 16) by omega, show ¬ (7 + k = 17) by omega,
        show ¬ (2 ≤ 7 + k ∧ 7 + k ≤ 6) by omega, ite_false]
    have hbits : ∀ k, k < 5 → (fl.toBits &&& fcsr.extractLsb' 7 5).getLsbD k =
        (flagBit fl k && fcsr.getLsbD (7 + k)) := fun k hk => by
      rw [BitVec.getLsbD_and, toBits_getLsbD fl k hk, BitVec.getLsbD_extractLsb']
      simp [hk, Nat.add_comm]
    simp only [fpeEnabled, bne_iff_ne, ne_eq, bv5_ne_zero]
    constructor
    · rintro ⟨k, hk, h⟩
      rw [hbits k hk, Bool.and_eq_true] at h
      exact ⟨k, hk, by rw [hc k hk]; exact h.1, by rw [he k hk]; exact h.2⟩
    · rintro ⟨k, hk, h1, h2⟩
      rw [hc k hk] at h1; rw [he k hk] at h2
      exact ⟨k, hk, by rw [hbits k hk, h1, h2]; rfl⟩
  · rw [hb (2 + k) (by omega)]
    simp only [show ¬ (12 ≤ 2 + k ∧ 2 + k ≤ 16) by omega, show ¬ (2 + k = 17) by omega,
      show 2 ≤ 2 + k ∧ 2 + k ≤ 6 by omega, and_self, ite_true, ite_false, show 2 + k - 2 = k by omega]
  · rw [hb i hi]
    simp only [show ¬ (12 ≤ i ∧ i ≤ 16) by omega, show ¬ (i = 17) by omega, h1, ite_false]

/-- **`FcsrSpec` determines the new FCSR and the trap decision.** -/
theorem fcsrSpec_unique {old : BitVec 32} {fl : Flags} {n1 n2 : BitVec 32} {t1 t2 : Bool}
    (h1 : FcsrSpec old fl n1 t1) (h2 : FcsrSpec old fl n2 t2) : n1 = n2 ∧ t1 = t2 := by
  obtain ⟨a1, b1, c1, d1, e1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2⟩ := h2
  have ht : t1 = t2 := by
    have en : ∀ k, k < 5 → n1.getLsbD (7 + k) = n2.getLsbD (7 + k) := fun k hk => by
      rw [e1 (7 + k) (by omega) (by omega) (by omega), e2 (7 + k) (by omega) (by omega) (by omega)]
    have : (t1 = true) ↔ (t2 = true) := by
      rw [c1, c2, a1, a2]
      simp only [Bool.false_eq_true, false_or]
      constructor
      · rintro ⟨k, hk, x, y⟩; exact ⟨k, hk, by rw [b2 k hk, ← b1 k hk]; exact x, by rw [← en k hk]; exact y⟩
      · rintro ⟨k, hk, x, y⟩; exact ⟨k, hk, by rw [b1 k hk, ← b2 k hk]; exact x, by rw [en k hk]; exact y⟩
    cases t1 <;> cases t2 <;> first | rfl | simp at this
  subst ht
  refine ⟨BitVec.eq_of_getLsbD_eq fun i hi => ?_, rfl⟩
  by_cases r1 : 2 ≤ i ∧ i ≤ 6
  · have := d1 (i - 2) (by omega); have := d2 (i - 2) (by omega)
    rw [show 2 + (i - 2) = i by omega] at *; simp_all
  · by_cases r2 : 12 ≤ i ∧ i ≤ 16
    · have := b1 (i - 12) (by omega); have := b2 (i - 12) (by omega)
      rw [show 12 + (i - 12) = i by omega] at *; simp_all
    · by_cases r3 : i = 17
      · subst r3; rw [a1, a2]
      · rw [e1 i hi r1 (by omega), e2 i hi r1 (by omega)]

end Mips.Fp
