import Semantics.FpOpsCorrectConv

/-!
# FpOpsCorrectCompare — `C.cond.fmt` against Tables 3.1 / 3.2

The model's `Format.relation` (sign-magnitude keys `orderKey`) is the ordering relation of the
operands' values in the extended reals (`Format.cmpRel`, MD00086 Vol II-A Rev 6.06 C.cond.fmt p.110;
MD00082 Vol I-A Rev 6.01 §6.3.1.3, p.81), and the predicate `fpCompare` / `fpCompareInvalid` is the
table of the 16 conditions (Tables 3.1, 3.2, p.111-112). Hence `C.cond.fmt` meets
`Format.CompareSpec` for all operands.
-/

namespace Mips.Fp

/-- The two compare tables are the predicate formula of the Operation (p.112-113):
`condition ← (cond2 and less) or (cond1 and equal) or (cond0 and unordered)`, and the
"Inv Op Excp. if QNaN?" column is `cond3`. -/
theorem condTable_formula : ∀ (cond : BitVec 4) (r : Format.Relation),
    fpCompare cond (decide (r = .un)) (decide (r = .lt)) (decide (r = .eq)) = condHolds cond.toNat r ∧
    (condTable cond.toNat).2.2.2.2 = cond.getLsbD 3 := by
  intro cond r; cases r <;> revert cond <;> decide

namespace Format

variable (f : Format)

/-- The integer significand of a finite magnitude `m` (sign bit cleared): value `= N · 2^qMin`. -/
def magN (m : Nat) : Nat :=
  if m / 2 ^ f.fracBits = 0 then m % 2 ^ f.fracBits
  else (m % 2 ^ f.fracBits + 2 ^ f.fracBits) * 2 ^ (m / 2 ^ f.fracBits - 1)

theorem magN_zero_iff (m : Nat) : f.magN m = 0 ↔ m = 0 := by
  have hB := Nat.two_pow_pos f.fracBits
  have hd := Nat.div_add_mod m (2 ^ f.fracBits)
  simp only [magN]
  split
  · rename_i h; rw [h] at hd; omega
  · rename_i h
    have : 0 < (m % 2 ^ f.fracBits + 2 ^ f.fracBits) * 2 ^ (m / 2 ^ f.fracBits - 1) :=
      Nat.mul_pos (by omega) (Nat.two_pow_pos _)
    constructor
    · intro h'; omega
    · intro h'; subst h'; simp at h

theorem magN_lt_bound (m : Nat) :
    f.magN m < 2 ^ f.fracBits * 2 ^ (m / 2 ^ f.fracBits) := by
  have hF : m % 2 ^ f.fracBits < 2 ^ f.fracBits := Nat.mod_lt _ (Nat.two_pow_pos _)
  simp only [magN]
  split
  · rename_i h; rw [h, Nat.pow_zero, Nat.mul_one]; exact hF
  · rename_i h
    have e : 2 ^ (m / 2 ^ f.fracBits) = 2 * 2 ^ (m / 2 ^ f.fracBits - 1) := by
      rw [← Nat.pow_succ']; congr 1; generalize m / 2 ^ f.fracBits = E at h; omega
    rw [e, ← Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)

theorem magN_ge_bound (m : Nat) (h : m / 2 ^ f.fracBits ≠ 0) :
    2 ^ f.fracBits * 2 ^ (m / 2 ^ f.fracBits - 1) ≤ f.magN m := by
  simp only [magN, h, ite_false]
  exact Nat.mul_le_mul_right _ (by omega)

/-- `magN` is strictly increasing. -/
theorem magN_strictMono {m m' : Nat} (h : m < m') : f.magN m < f.magN m' := by
  have hB := Nat.two_pow_pos f.fracBits
  have hd := Nat.div_add_mod m (2 ^ f.fracBits)
  have hd' := Nat.div_add_mod m' (2 ^ f.fracBits)
  have hF := Nat.mod_lt m hB
  have hF' := Nat.mod_lt m' hB
  have hE : m / 2 ^ f.fracBits ≤ m' / 2 ^ f.fracBits := Nat.div_le_div_right (Nat.le_of_lt h)
  have lb := f.magN_lt_bound m
  have ub := f.magN_ge_bound m'
  unfold magN at lb ub ⊢
  generalize m / 2 ^ f.fracBits = E at *
  generalize m' / 2 ^ f.fracBits = E' at *
  generalize m % 2 ^ f.fracBits = F at *
  generalize m' % 2 ^ f.fracBits = F' at *
  generalize 2 ^ f.fracBits = B at *
  rcases Nat.lt_or_eq_of_le hE with hlt | heq
  · have h1 : B * 2 ^ E ≤ B * 2 ^ (E' - 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 := ub (by omega)
    simp only [show E' ≠ 0 by omega, ite_false] at h2 ⊢
    omega
  · subst heq
    have hfr : F < F' := by
      have e1 : B * E = B * E := rfl
      omega
    split
    · exact hfr
    · exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)

theorem magN_lt_iff (m m' : Nat) : f.magN m < f.magN m' ↔ m < m' := by
  constructor
  · intro h; rcases Nat.lt_or_ge m m' with h1 | h1
    · exact h1
    · rcases Nat.lt_or_eq_of_le h1 with h2 | h2
      · exact absurd (f.magN_strictMono h2) (by omega)
      · subst h2; omega
  · exact f.magN_strictMono

theorem magN_eq_iff (m m' : Nat) : f.magN m = f.magN m' ↔ m = m' := by
  constructor
  · intro h; rcases Nat.lt_trichotomy m m' with h1 | h1 | h1
    · have := f.magN_strictMono h1; omega
    · exact h1
    · have := f.magN_strictMono h1; omega
  · intro h; rw [h]

/-- The value of a finite encoding: `±magN(m) · 2^qMin`, `m` the magnitude bits. -/
theorem toExact_toRat_magN (hf : f.WF) {n : Nat} (hn : n < 2 ^ f.width) (he : f.expField n ≠ f.expMax) :
    (f.toExact n).toRat =
      (((if f.signBit n then -(f.magN (n % 2 ^ (f.expBits + f.fracBits)) : Int)
        else (f.magN (n % 2 ^ (f.expBits + f.fracBits)) : Int)) : Int) : Rat) * (2 : Rat) ^ f.qMin := by
  obtain ⟨t, m, ht, hm, rfl⟩ := f.split_bits hn
  obtain ⟨e1, f1, s1, -⟩ := f.fields_split t m ht hm
  have hmod : (t * 2 ^ (f.expBits + f.fracBits) + m) % 2 ^ (f.expBits + f.fracBits) = m := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]
  rw [hmod]
  simp only [toExact, e1, f1, s1, Exact.toRat, magN]
  have hb := f.bias_pos hf
  generalize m / 2 ^ f.fracBits = E
  generalize m % 2 ^ f.fracBits = F
  generalize (t == 1) = s
  split
  · cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true, Rat.intCast_neg, Rat.intCast_natCast] <;>
      grind
  · have hq : (E : Int) - f.bias - f.fracBits = f.qMin + ((E - 1 : Nat) : Int) := by
      simp only [qMin]; omega
    rw [hq, two_zpow_add, two_zpow_nat]
    cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true, Rat.intCast_neg, Rat.intCast_natCast] <;>
      push_cast <;> grind

/-- The magnitude of an infinity is above every finite magnitude. -/
theorem mag_finite_lt {n : Nat} (hn : n < 2 ^ f.width) (he : f.expField n ≠ f.expMax) :
    n % 2 ^ (f.expBits + f.fracBits) < f.expMax * 2 ^ f.fracBits := by
  obtain ⟨t, m, ht, hm, rfl⟩ := f.split_bits hn
  obtain ⟨e1, -, -, -⟩ := f.fields_split t m ht hm
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]
  rw [e1] at he
  have hE : m / 2 ^ f.fracBits < 2 ^ f.expBits := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]; exact hm
  have : m / 2 ^ f.fracBits < f.expMax := by simp only [expMax] at he ⊢; omega
  have hd := Nat.div_add_mod m (2 ^ f.fracBits)
  have hF := Nat.mod_lt m (Nat.two_pow_pos f.fracBits)
  have : (m / 2 ^ f.fracBits + 1) * 2 ^ f.fracBits ≤ f.expMax * 2 ^ f.fracBits :=
    Nat.mul_le_mul_right _ this
  rw [Nat.succ_mul] at this
  rw [Nat.mul_comm] at hd; omega

theorem mag_inf (hn : n < 2 ^ f.width) (h : f.isInf n = true) :
    n % 2 ^ (f.expBits + f.fracBits) = f.expMax * 2 ^ f.fracBits := by
  have he := f.eq_inf_of_isInf hn h
  obtain ⟨t, m, ht, hm, hnm⟩ := f.split_bits hn
  obtain ⟨e1, f1, -, -⟩ := f.fields_split t m ht hm
  simp only [isInf, Bool.and_eq_true, beq_iff_eq] at h
  rw [hnm, e1, f1] at h
  rw [hnm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]
  have hd := Nat.div_add_mod m (2 ^ f.fracBits)
  rw [h.1, h.2] at hd; rw [Nat.mul_comm]; omega

theorem key_cases (sa sb : Bool) (ma mb Na Nb : Nat) (hlt : Na < Nb ↔ ma < mb) (heq : Na = Nb ↔ ma = mb)
    (ha0 : Na = 0 ↔ ma = 0) (hb0 : Nb = 0 ↔ mb = 0) :
    ((if sa then -(ma : Int) else ma) < (if sb then -(mb : Int) else mb) ↔
      (if sa then -(Na : Int) else Na) < (if sb then -(Nb : Int) else Nb)) ∧
    ((if sa then -(ma : Int) else ma) = (if sb then -(mb : Int) else mb) ↔
      (if sa then -(Na : Int) else Na) = (if sb then -(Nb : Int) else Nb)) := by
  have h1 : Na < Nb → ma < mb := hlt.1
  have h2 : ma < mb → Na < Nb := hlt.2
  have h3 : Nb < Na → mb < ma := fun h => by
    rcases Nat.lt_or_ge mb ma with h' | h'
    · exact h'
    · rcases Nat.lt_or_eq_of_le h' with h'' | h''
      · have := h2 h''; omega
      · have := heq.2 h''; omega
  have h4 : mb < ma → Nb < Na := fun h => by
    rcases Nat.lt_or_ge Nb Na with h' | h'
    · exact h'
    · rcases Nat.lt_or_eq_of_le h' with h'' | h''
      · have := h1 h''; omega
      · have := heq.1 h''; omega
  have h5 := heq.1
  have h6 := heq.2
  have h7 := ha0.1
  have h8 := ha0.2
  have h9 := hb0.1
  have h10 := hb0.2
  cases sa <;> cases sb <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem rel_of {KA KB : Int} {R : Relation} (h1 : KA < KB ↔ R = .lt) (h2 : KA = KB ↔ R = .eq)
    (h3 : R ≠ .un) :
    (⟨false, decide (KA < KB), decide (KA = KB)⟩ : FpRel).unordered = decide (R = .un) ∧
    (⟨false, decide (KA < KB), decide (KA = KB)⟩ : FpRel).less = decide (R = .lt) ∧
    (⟨false, decide (KA < KB), decide (KA = KB)⟩ : FpRel).equal = decide (R = .eq) := by
  refine ⟨by simp [h3], ?_, ?_⟩ <;> simp only [decide_eq_decide] <;> assumption

/-- **The model's order keys give the relation of the values.** -/
theorem relation_spec (hf : f.WF) {a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width) :
    (f.relation a b).unordered = decide (f.cmpRel a b = .un) ∧
    (f.relation a b).less = decide (f.cmpRel a b = .lt) ∧
    (f.relation a b).equal = decide (f.cmpRel a b = .eq) := by
  have hq := rat_two_zpow_pos f.qMin
  have hM : 0 < f.expMax * 2 ^ f.fracBits := Nat.mul_pos (by
    simp only [expMax]; have := Nat.pow_le_pow_right (n := 2) (by omega) hf.1; simp at this; omega)
    (Nat.two_pow_pos _)
  have kA : f.orderKey a = if f.signBit a then -((a % 2 ^ (f.expBits + f.fracBits) : Nat) : Int)
      else ((a % 2 ^ (f.expBits + f.fracBits) : Nat) : Int) := rfl
  have kB : f.orderKey b = if f.signBit b then -((b % 2 ^ (f.expBits + f.fracBits) : Nat) : Int)
      else ((b % 2 ^ (f.expBits + f.fracBits) : Nat) : Int) := rfl
  rcases f.classify hf a ha with ⟨na, -, da⟩ | ⟨na, ia, -, da⟩ | ⟨na, ia, ea, da, -, -⟩
  · simp [relation, na, cmpRel, da]
  all_goals rcases f.classify hf b hb with ⟨nb, -, db⟩ | ⟨nb, ib, -, db⟩ | ⟨nb, ib, eb, db, -, -⟩
  all_goals (try (simp [relation, na, nb, cmpRel, da, db]; done))
  all_goals simp only [relation, na, nb, Bool.or_false, Bool.false_eq_true, ite_false]
  · -- ∞, ∞
    rw [f.mag_inf ha ia] at kA; rw [f.mag_inf hb ib] at kB
    rw [kA, kB]
    apply rel_of <;> simp only [cmpRel, da, db] <;>
      generalize f.expMax * 2 ^ f.fracBits = M at * <;>
      generalize a % 2 ^ (f.expBits + f.fracBits) = ma at * <;>
      generalize b % 2 ^ (f.expBits + f.fracBits) = mb at * <;>
      generalize f.signBit a = sa at * <;> generalize f.signBit b = sb at * <;>
      cases sa <;> cases sb <;> simp <;> omega
  · -- ∞, finite
    rw [f.mag_inf ha ia] at kA
    have := f.mag_finite_lt hb eb
    rw [kA, kB]
    apply rel_of <;> simp only [cmpRel, da, db] <;>
      generalize f.expMax * 2 ^ f.fracBits = M at * <;>
      generalize a % 2 ^ (f.expBits + f.fracBits) = ma at * <;>
      generalize b % 2 ^ (f.expBits + f.fracBits) = mb at * <;>
      generalize f.signBit a = sa at * <;> generalize f.signBit b = sb at * <;>
      cases sa <;> cases sb <;> simp <;> omega
  · -- finite, ∞
    rw [f.mag_inf hb ib] at kB
    have := f.mag_finite_lt ha ea
    rw [kA, kB]
    apply rel_of <;> simp only [cmpRel, da, db] <;>
      generalize f.expMax * 2 ^ f.fracBits = M at * <;>
      generalize a % 2 ^ (f.expBits + f.fracBits) = ma at * <;>
      generalize b % 2 ^ (f.expBits + f.fracBits) = mb at * <;>
      generalize f.signBit a = sa at * <;> generalize f.signBit b = sb at * <;>
      cases sa <;> cases sb <;> simp <;> omega
  · -- finite, finite
    have xA := f.toExact_toRat_magN hf ha ea
    have xB := f.toExact_toRat_magN hf hb eb
    obtain ⟨k1, k2⟩ := key_cases (f.signBit a) (f.signBit b) _ _ _ _
      (f.magN_lt_iff (a % 2 ^ (f.expBits + f.fracBits)) (b % 2 ^ (f.expBits + f.fracBits)))
      (f.magN_eq_iff _ _) (f.magN_zero_iff _) (f.magN_zero_iff _)
    rw [← kA, ← kB] at k1 k2
    have lt_iff := pt_lt (a := (if f.signBit a then -(f.magN (a % 2 ^ (f.expBits + f.fracBits)) : Int)
        else (f.magN (a % 2 ^ (f.expBits + f.fracBits)) : Int)))
      (b := (if f.signBit b then -(f.magN (b % 2 ^ (f.expBits + f.fracBits)) : Int)
        else (f.magN (b % 2 ^ (f.expBits + f.fracBits)) : Int))) hq
    have eq_iff := pt_eq (a := (if f.signBit a then -(f.magN (a % 2 ^ (f.expBits + f.fracBits)) : Int)
        else (f.magN (a % 2 ^ (f.expBits + f.fracBits)) : Int)))
      (b := (if f.signBit b then -(f.magN (b % 2 ^ (f.expBits + f.fracBits)) : Int)
        else (f.magN (b % 2 ^ (f.expBits + f.fracBits)) : Int))) hq
    rw [← xA, ← xB] at lt_iff eq_iff
    have L : f.orderKey a < f.orderKey b ↔ (f.toExact a).toRat < (f.toExact b).toRat := k1.trans lt_iff.symm
    have E : f.orderKey a = f.orderKey b ↔ (f.toExact a).toRat = (f.toExact b).toRat := k2.trans eq_iff.symm
    apply rel_of <;> simp only [cmpRel, da, db]
    · rw [L]; by_cases h : (f.toExact a).toRat < (f.toExact b).toRat
      · simp [h]
      · by_cases h' : (f.toExact a).toRat = (f.toExact b).toRat <;> simp [h, h']
    · rw [E]
      by_cases h : (f.toExact a).toRat < (f.toExact b).toRat
      · simp [h]; grind
      · by_cases h' : (f.toExact a).toRat = (f.toExact b).toRat <;> simp [h, h']
    · split <;> (try split) <;> simp

/-- **`C.cond.fmt` meets `CompareSpec`** (generic in the format). -/
theorem compare_spec (hf : f.WF) (cond : BitVec 4) {a b : Nat} (ha : a < 2 ^ f.width)
    (hb : b < 2 ^ f.width) :
    f.CompareSpec cond a b
      (fpCompare cond (f.relation a b).unordered (f.relation a b).less (f.relation a b).equal,
        { invalid := fpCompareInvalid cond (f.relation a b).unordered (f.isSNaN a || f.isSNaN b) }) := by
  obtain ⟨hu, hl, he⟩ := f.relation_spec hf ha hb
  obtain ⟨t1, t2⟩ := condTable_formula cond (f.cmpRel a b)
  refine ⟨by rw [hu, hl, he]; exact t1, ?_, rfl, rfl, rfl, rfl⟩
  simp only [fpCompareInvalid, hu, t2, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    ← isSNaN_iff, ← isQNaN_iff]
  have hun : f.cmpRel a b = .un ↔ f.isNaN a = true ∨ f.isNaN b = true := by
    rcases f.classify hf a ha with ⟨na, -, da⟩ | ⟨na, -, -, da⟩ | ⟨na, -, -, da, -, -⟩ <;>
    rcases f.classify hf b hb with ⟨nb, -, db⟩ | ⟨nb, -, -, db⟩ | ⟨nb, -, -, db, -, -⟩ <;>
    simp only [cmpRel, da, db, na, nb] <;> (try split) <;> (try split) <;> simp
  rw [hun]
  have nq : ∀ x, f.isNaN x = true ↔ f.isSNaN x = true ∨ f.isQNaN x = true := fun x => by
    simp only [isSNaN, isQNaN, Bool.and_eq_true, beq_iff_eq]
    constructor
    · intro h
      have hlt : f.fracField x / 2 ^ (f.fracBits - 1) < 2 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        have e : 2 ^ (f.fracBits - 1) * 2 = 2 ^ f.fracBits := by
          rw [← Nat.pow_succ]; congr 1; have := hf.2; omega
        rw [Nat.mul_comm, e]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
      generalize f.fracField x / 2 ^ (f.fracBits - 1) = q at hlt ⊢
      rcases (by omega : q = 0 ∨ q = 1) with hq | hq <;> simp [h, hq]
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  rw [nq a, nq b]
  constructor
  · rintro ((h | h) | ⟨h3, (h | h) | (h | h)⟩) <;> simp_all
  · rintro (h | h | ⟨h3, h | h⟩) <;> simp_all

end Format

end Mips.Fp
