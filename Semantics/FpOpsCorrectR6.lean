import Semantics.FpOpsCorrectIEEE

/-!
# FpOpsCorrectR6 — the Release 6 non-fused FP operations against their reference definitions

The Release 6 operations `CMP.condn.fmt`, `MAX/MIN/MAXA/MINA.fmt`, `CLASS.fmt` and `RINT.fmt` of
`Semantics/FpOps.lean` (§10, §11) meet their reference definitions of `Semantics/FpOpsSpec.lean`
on **all** operands and every FCSR environment:

| model | reference | manual (MD00086 Vol II-A Rev 6.06) |
|---|---|---|
| `f32Cmp`/`f64Cmp` | `Format.CmpSpec` | CMP.condn.fmt p.136-140, Table 3.9 p.138-139 |
| `f32MinMax`/`f64MinMax` | `Format.MinMaxSpec` | MAX/MIN/MAXA/MINA.fmt p.262-265, Table 4.1 p.264-265 |
| `f32Class`/`f64Class` | `Format.ClassSpec` | CLASS.fmt p.132 |
| `f32Rint`/`f64Rint` | `Format.RintSpec` | RINT.fmt p.337 |

As for the arithmetic operations (`FpOpsCorrectIEEE.lean`), the operands of MAX/MIN/MAXA/MINA are
taken as the operation sees them, `Format.FlushedIn` under FCSR.FS (MD00082 Vol I-A Rev 6.01 Table
6.8, `FS`, p.93; no Inexact for the flushing of a comparison instruction, §6.7.2.4, p.102, Table 7.9,
p.110). RINT takes its operand as encoded: `RintSpec` itself states the flushing and the Inexact it
signals (§6.7.2.4, p.102). CLASS takes its operand as encoded ("not affected by the
flush-subnormal-to-zero mode FCSR.FS", p.132); `f32Cmp`/`f64Cmp` take no FCSR environment, so their
theorem is about the operands they are given.

The compare reuses the `C.cond.fmt` machinery of `FpOpsCorrectCompare.lean` (`relation_spec`: the
model's sign-magnitude order keys give `Format.cmpRel`); MAX/MIN also, plus the same fact for the
operands with the sign bit cleared (`magRel`); RINT reuses `roundToInt_cr` (correct rounding to the
integers, `FpOpsCorrectWord.lean`) and the rounding core's exactness on representable values
(`roundSpec_exact`).
-/

namespace Mips.Fp

/-! ## `CMP.condn.fmt` -/

/-- **Table 3.9 is the predicate formula of the Operation** (p.140): `condition ← cond4 xor ((cond2
and less) or (cond1 and equal) or (cond0 and unordered))`, and the "Invalid Operand Exception"
column is `cond3`. Checked on all 32 `condn` values and all four relations. -/
theorem cmpTable_formula : ∀ (condn : BitVec 5) (r : Format.Relation),
    cmpCondition condn (decide (r = .un)) (decide (r = .lt)) (decide (r = .eq)) = cmpHolds condn.toNat r ∧
    (cmpTable condn.toNat).2.2.2.2 = (condn.setWidth 4).getLsbD 3 := by
  intro c r; cases r <;> revert c <;> decide

namespace Format

variable (f : Format)

/-- **`CMP.condn.fmt` meets `CmpSpec`** (generic in the format). -/
theorem cmp_spec (hf : f.WF) (condn : BitVec 5) {a b : Nat} (ha : a < 2 ^ f.width)
    (hb : b < 2 ^ f.width) :
    f.CmpSpec condn a b
      (cmpCondition condn (f.relation a b).unordered (f.relation a b).less (f.relation a b).equal,
        { invalid := fpCompareInvalid (condn.setWidth 4) (f.relation a b).unordered
            (f.isSNaN a || f.isSNaN b) }) := by
  obtain ⟨hu, hl, he⟩ := f.relation_spec hf ha hb
  obtain ⟨t1, t2⟩ := cmpTable_formula condn (f.cmpRel a b)
  obtain ⟨-, t2'⟩ := condTable_formula (condn.setWidth 4) (f.cmpRel a b)
  obtain ⟨-, hinv, -⟩ := f.compare_spec hf (condn.setWidth 4) ha hb
  rw [t2', ← t2] at hinv
  exact ⟨by rw [hu, hl, he]; exact t1, hinv, rfl, rfl, rfl, rfl⟩

end Format

/-- **`CMP.condn.S`** for all 32 `condn` values and all operands. -/
theorem f32Cmp_spec (condn : BitVec 5) (a b : BitVec 32) :
    binary32.CmpSpec condn a.toNat b.toNat (f32Cmp condn a b) :=
  binary32.cmp_spec binary32_wf condn a.isLt b.isLt

/-- **`CMP.condn.D`**. -/
theorem f64Cmp_spec (condn : BitVec 5) (a b : BitVec 64) :
    binary64.CmpSpec condn a.toNat b.toNat (f64Cmp condn a b) :=
  binary64.cmp_spec binary64_wf condn a.isLt b.isLt

/-! ## `MAX.fmt`, `MIN.fmt`, `MAXA.fmt`, `MINA.fmt` -/

namespace Format

variable (f : Format)

/-- The operand with the sign bit cleared is the magnitude bits: a `width`-bit pattern, the same
class (NaN or not), order key the magnitude. -/
theorem absBits_facts {n : Nat} (hn : n < 2 ^ f.width) :
    f.signChanged true n = n % 2 ^ (f.expBits + f.fracBits) ∧
    f.signChanged true n < 2 ^ f.width ∧
    f.isNaN (f.signChanged true n) = f.isNaN n ∧
    f.orderKey (f.signChanged true n) = ((n % 2 ^ (f.expBits + f.fracBits) : Nat) : Int) := by
  obtain ⟨t, m, ht, hm, rfl⟩ := f.split_bits hn
  obtain ⟨e1, f1, s1, -⟩ := f.fields_split t m ht hm
  obtain ⟨e0, f0, s0, l0⟩ := f.fields_split 0 m (by omega) hm
  simp only [Nat.zero_mul, Nat.zero_add] at e0 f0 s0 l0
  have hmod : (t * 2 ^ (f.expBits + f.fracBits) + m) % 2 ^ (f.expBits + f.fracBits) = m := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]
  have hsc : f.signChanged true (t * 2 ^ (f.expBits + f.fracBits) + m) = m := by
    simp only [signChanged, signOf_eq, s1, ite_true]
    rcases (show t = 0 ∨ t = 1 by omega) with h | h <;> subst h <;> simp
  rw [hmod, hsc]
  refine ⟨rfl, l0, ?_, ?_⟩
  · simp only [isNaN, e0, f0, e1, f1]
  · simp only [orderKey, s0, Nat.mod_eq_of_lt hm]; rfl

/-- On non-NaN operands the model's order keys decide `cmpRel`. -/
theorem key_rel (hf : f.WF) {a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width)
    (na : f.isNaN a = false) (nb : f.isNaN b = false) :
    (f.orderKey a < f.orderKey b ↔ f.cmpRel a b = .lt) ∧
    (f.orderKey a = f.orderKey b ↔ f.cmpRel a b = .eq) ∧ f.cmpRel a b ≠ .un := by
  obtain ⟨hu, hl, he⟩ := f.relation_spec hf ha hb
  simp only [relation, na, nb, Bool.or_false, Bool.false_eq_true, ite_false] at hu hl he
  refine ⟨decide_eq_decide.1 hl, decide_eq_decide.1 he, fun h => ?_⟩
  simp [h] at hu

/-- The relation of the magnitudes, from the magnitude bits. -/
theorem mag_rel (hf : f.WF) {a b : Nat} (ha : a < 2 ^ f.width) (hb : b < 2 ^ f.width)
    (na : f.isNaN a = false) (nb : f.isNaN b = false) :
    (a % 2 ^ (f.expBits + f.fracBits) < b % 2 ^ (f.expBits + f.fracBits) ↔ f.magRel a b = .lt) ∧
    (a % 2 ^ (f.expBits + f.fracBits) = b % 2 ^ (f.expBits + f.fracBits) ↔ f.magRel a b = .eq) ∧
    f.magRel a b ≠ .un := by
  obtain ⟨-, la, nA, kA⟩ := f.absBits_facts ha
  obtain ⟨-, lb, nB, kB⟩ := f.absBits_facts hb
  obtain ⟨h1, h2, h3⟩ := f.key_rel hf la lb (nA.trans na) (nB.trans nb)
  rw [kA, kB] at h1 h2
  refine ⟨?_, ?_, h3⟩
  · exact Int.ofNat_lt.symm.trans h1
  · exact Int.ofNat_inj.symm.trans h2

theorem rel_gt_iff {r : Relation} (hu : r ≠ .un) : r = .gt ↔ ¬ r = .lt ∧ ¬ r = .eq := by
  cases r <;> simp_all

/-- **The model's numeric choice is `MinMaxPicksA`** on non-NaN operands. -/
theorem minMaxPickA_iff (hf : f.WF) (op : MinMaxOp) {a b : Nat} (ha : a < 2 ^ f.width)
    (hb : b < 2 ^ f.width) (na : f.isNaN a = false) (nb : f.isNaN b = false) :
    f.minMaxPickA op a b = true ↔ f.MinMaxPicksA op a b := by
  obtain ⟨l1, e1, -⟩ := f.key_rel hf ha hb na nb
  obtain ⟨l2, e2, -⟩ := f.key_rel hf hb ha nb na
  obtain ⟨m1, m2, m3⟩ := f.mag_rel hf ha hb na nb
  have mg := rel_gt_iff m3
  have sltA : f.SignedLt a b ↔ (f.orderKey a < f.orderKey b ∨
      (f.orderKey a = f.orderKey b ∧ f.signBit a = true ∧ f.signBit b = false)) := by
    simp only [SignedLt, signOf_eq, l1, e1]
  have sltB : f.SignedLt b a ↔ (f.orderKey b < f.orderKey a ∨
      (f.orderKey b = f.orderKey a ∧ f.signBit b = true ∧ f.signBit a = false)) := by
    simp only [SignedLt, signOf_eq, l2, e2]
  have ke : f.orderKey b = f.orderKey a ↔ f.orderKey a = f.orderKey b := eq_comm
  cases op <;>
    simp only [minMaxPickA, MinMaxPicksA, sltA, sltB, ke, mg, ← m1, ← m2, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] <;>
    generalize f.orderKey a = ka <;> generalize f.orderKey b = kb <;>
    generalize a % 2 ^ (f.expBits + f.fracBits) = ma <;>
    generalize b % 2 ^ (f.expBits + f.fracBits) = mb <;>
    cases f.signBit a <;> cases f.signBit b <;> simp <;> omega

theorem minMax_flags (op : MinMaxOp) (a b : Nat) :
    (f.minMax op a b).2 = { invalid := f.isSNaN a || f.isSNaN b } := by
  unfold minMax; split <;> (try split) <;> (try split) <;> rfl

/-- **MAX/MIN/MAXA/MINA meet `MinMaxSpec`** (generic in the format). -/
theorem minMax_spec (hf : f.WF) (op : MinMaxOp) {a b : Nat} (ha : a < 2 ^ f.width)
    (hb : b < 2 ^ f.width) : f.MinMaxSpec op a b (f.minMax op a b) := by
  have nf : ∀ x, ¬ f.IsNaN x → f.isNaN x = false := fun x h =>
    Bool.eq_false_iff.2 (fun h' => h ((f.isNaN_iff x).1 h'))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [minMax_flags]
    simp only [← isSNaN_iff]
    cases f.isSNaN a <;> cases f.isSNaN b <;> simp
  · intro hA hB
    simp [minMax, (f.isNaN_iff a).2 hA, (f.isNaN_iff b).2 hB]
  · intro hA hB
    simp [minMax, (f.isNaN_iff a).2 hA, nf b hB]
  · intro hA hB
    simp [minMax, nf a hA, (f.isNaN_iff b).2 hB]
  · intro hA hB
    have hp := f.minMaxPickA_iff hf op ha hb (nf a hA) (nf b hB)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp [minMax, nf a hA, nf b hB, hp.2 h]
    · have : f.minMaxPickA op a b = false := Bool.eq_false_iff.2 (fun h' => h (hp.1 h'))
      simp [minMax, nf a hA, nf b hB, this]

theorem minMax_lt (op : MinMaxOp) {a b : Nat} (ha : a < 2 ^ f.width)
    (hb : b < 2 ^ f.width) : (f.minMax op a b).1 < 2 ^ f.width := by
  unfold minMax; split <;> (try split) <;> (try split) <;> (try split) <;> assumption

end Format

/-- **`MAX/MIN/MAXA/MINA.S`** on all operands (flushed under FCSR.FS), every FCSR environment. -/
theorem f32MinMax_spec (op : Format.MinMaxOp) (e : Env) (a b : BitVec 32) :
    binary32.MinMaxSpec op (binary32.FlushedIn e.flush a.toNat) (binary32.FlushedIn e.flush b.toNat)
      ((f32MinMax op e a b).1.toNat, (f32MinMax op e a b).2) := by
  have ha := binary32.flushIn_lt e.flush a.isLt; have hb := binary32.flushIn_lt e.flush b.isLt
  simp only [f32MinMax, ← Format.flushIn_eq]
  rw [pair_toNat (w := 32) _ (binary32.minMax_lt op ha hb)]
  exact binary32.minMax_spec binary32_wf op ha hb

/-- **`MAX/MIN/MAXA/MINA.D`**. -/
theorem f64MinMax_spec (op : Format.MinMaxOp) (e : Env) (a b : BitVec 64) :
    binary64.MinMaxSpec op (binary64.FlushedIn e.flush a.toNat) (binary64.FlushedIn e.flush b.toNat)
      ((f64MinMax op e a b).1.toNat, (f64MinMax op e a b).2) := by
  have ha := binary64.flushIn_lt e.flush a.isLt; have hb := binary64.flushIn_lt e.flush b.isLt
  simp only [f64MinMax, ← Format.flushIn_eq]
  rw [pair_toNat (w := 64) _ (binary64.minMax_lt op ha hb)]
  exact binary64.minMax_spec binary64_wf op ha hb

/-! ## `CLASS.fmt` -/

namespace Format

variable (f : Format)

/-- **CLASS meets `ClassSpec`** (generic in the format). -/
theorem classMask_spec (hf : f.WF) {a : Nat} (ha : a < 2 ^ f.width) : f.ClassSpec a (f.classMask a) := by
  have hS := (signOp_cases f hf a).1
  rcases f.classify hf a ha with ⟨na, -, da⟩ | ⟨na, ia, -, da⟩ | ⟨na, ia, -, da, -, za⟩
  · by_cases hs : f.isSNaN a = true
    · simp [ClassSpec, classBit, da, classMask, hs, (f.isSNaN_iff a).1 hs]
    · have hq : f.isQNaN a = true := by
        cases h : f.isQNaN a
        · exact absurd ((f.isSNaN_iff a).2 (hS.2 ⟨na, h⟩)) hs
        · rfl
      have hs' : ¬ f.IsSNaN a := fun h => hs ((f.isSNaN_iff a).2 h)
      simp [ClassSpec, classBit, da, classMask, hs, hq, hs']
  · have h1 : f.isSNaN a = false := by simp [isSNaN, na]
    have h2 : f.isQNaN a = false := by simp [isQNaN, na]
    simp only [ClassSpec, classBit, da, classMask, h1, h2, ia, Bool.false_eq_true, ite_false, ite_true]
  · have h1 : f.isSNaN a = false := by simp [isSNaN, na]
    have h2 : f.isQNaN a = false := by simp [isQNaN, na]
    simp only [ClassSpec, classBit, da, classMask, h1, h2, ia, Bool.false_eq_true, ite_false]
    by_cases hz : f.isZero a = true
    · simp only [hz, ite_true, za.2 hz]
    · have hx : ¬ (f.toExact a).toRat = 0 := fun h => hz (za.1 h)
      have hz' : f.expField a = 0 → f.fracField a ≠ 0 := fun h h' => hz (by simp [isZero, h, h'])
      have hsub : f.isSubnormal a = decide (f.expOf a = 0) := by
        show f.isSubnormal a = decide (f.expField a = 0)
        unfold isSubnormal
        by_cases he : f.expField a = 0
        · simp [he, hz' he]
        · simp [he]
      simp only [hz, Bool.false_eq_true, ite_false, hx, hsub]
      by_cases he : f.expOf a = 0 <;> cases f.signBit a <;> simp [he] <;> rfl

theorem classMask_lt (a : Nat) : f.classMask a < 2 ^ 10 := by
  simp only [classMask]
  cases f.signBit a <;> split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    decide

end Format

/-- **`CLASS.S`** on every operand (taken as encoded: not affected by FCSR.FS). -/
theorem f32Class_spec (a : BitVec 32) : binary32.ClassSpec a.toNat (f32Class a).toNat := by
  simp only [f32Class]
  rw [toNat_ofNat_lt (Nat.lt_of_lt_of_le (binary32.classMask_lt _) (by decide))]
  exact binary32.classMask_spec binary32_wf a.isLt

/-- **`CLASS.D`**. -/
theorem f64Class_spec (a : BitVec 64) : binary64.ClassSpec a.toNat (f64Class a).toNat := by
  simp only [f64Class]
  rw [toNat_ofNat_lt (Nat.lt_of_lt_of_le (binary64.classMask_lt _) (by decide))]
  exact binary64.classMask_spec binary64_wf a.isLt

/-! ## `RINT.fmt` -/

theorem roundShift_le (rm : RoundingMode) (neg : Bool) (m k : Nat) :
    roundShift rm neg m k ≤ m / 2 ^ k + 1 := by
  cases rm <;> simp only [roundShift] <;> split <;> omega

/-- The shape of `roundToInt`: a magnitude `M` with the operand's sign; when the operand is not
already an integer, `M` is at most half the significand plus one. -/
theorem roundToInt_shape (rm : RoundingMode) (v : Exact) :
    ∃ M : Nat, roundToInt rm v = (if v.sign then -(M : Int) else (M : Int)) ∧
      (v.isIntegral = true ∨ M ≤ v.sig / 2 + 1) := by
  unfold roundToInt Exact.isIntegral
  rcases hv : v.exp with e | k <;> simp only
  · exact ⟨_, rfl, .inl trivial⟩
  · refine ⟨_, rfl, .inr ?_⟩
    have h2 : 2 ≤ 2 ^ (k + 1) := by
      have := Nat.pow_le_pow_right (n := 2) (by omega) (show 1 ≤ k + 1 by omega); simpa using this
    have hq : v.sig / 2 ^ (k + 1) ≤ v.sig / 2 := Nat.div_le_div_left h2 (by decide)
    have := roundShift_le rm v.sign v.sig (k + 1)
    omega

theorem natAbs_signed (s : Bool) (M : Nat) : (if s then -(M : Int) else (M : Int)).natAbs = M := by
  cases s <;> simp

theorem toRat_signed_int (s : Bool) (M : Nat) :
    Exact.toRat ⟨s, M, 0⟩ = (((if s then -(M : Int) else (M : Int)) : Int) : Rat) := by
  rw [Exact.toRat_mk]; cases s <;> simp

namespace Format

variable (f : Format)

theorem emin_nonpos (hf : f.WF) : f.emin ≤ 0 := by
  simp only [emin]
  have : 2 ≤ 2 ^ (f.expBits - 1) := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) (show 1 ≤ f.expBits - 1 by have := hf.1; omega)
    simpa using this
  omega

/-- A nonzero integer is not tiny. -/
theorem int_abs_ge (hf : f.WF) {i : Int} (hi : i ≠ 0) : (2 : Rat) ^ f.emin ≤ (i : Rat).abs := by
  have h1 : (2 : Rat) ^ f.emin ≤ 1 := by
    have := two_zpow_le (f.emin_nonpos hf); simpa using this
  have h2 : (1 : Rat) ≤ (i : Rat).abs := by
    rcases (by omega : 0 < i ∨ i < 0) with h | h
    · have : (1 : Rat) ≤ (i : Rat) := by exact_mod_cast (show (1 : Int) ≤ i by omega)
      simp only [Rat.abs]; split <;> grind
    · have : (i : Rat) ≤ -1 := by
        have := Rat.intCast_le_intCast.2 (show i ≤ -1 by omega); simpa using this
      simp only [Rat.abs]; split <;> grind
  exact Rat.le_trans h1 h2

theorem toExact_sign (n : Nat) : (f.toExact n).sign = f.signBit n := by
  simp only [toExact]; split <;> rfl

theorem toExact_sig_lt (n : Nat) : (f.toExact n).sig < 2 * 2 ^ f.fracBits := by
  have := Nat.mod_lt n (Nat.two_pow_pos f.fracBits)
  simp only [toExact, fracField]; split <;> simp only <;> omega

/-- The integer rounding of a finite value is a value of the format with the exponent range
unbounded above, within the finite range, and not tiny when nonzero. -/
theorem rint_bounds (hf : f.WF) (hcap : (f.fracBits : Int) ≤ f.emax) {a : Nat} {x : Rat}
    (va : f.value a = some x) (rm : RoundingMode) (M : Nat)
    (hM : roundToInt rm (f.toExact a) = (if (f.toExact a).sign then -(M : Int) else (M : Int)))
    (hcase : (f.toExact a).isIntegral = true ∨ M ≤ (f.toExact a).sig / 2 + 1) :
    f.Unbounded (roundToInt rm (f.toExact a) : Rat) ∧
    (roundToInt rm (f.toExact a) : Rat).abs ≤ f.maxValue := by
  have hx := value_toExact f va
  rcases hcase with hI | hB
  · rw [(isIntegral_iff rm _).1 hI, hx]
    exact ⟨representable_unbounded f ⟨a, va⟩, value_abs_le_max f hf va⟩
  · have hs := f.toExact_sig_lt a
    have hM2 : M ≤ 2 ^ f.fracBits := by
      have : (f.toExact a).sig / 2 < 2 ^ f.fracBits := by omega
      omega
    have hna : (roundToInt rm (f.toExact a)).natAbs = M := by rw [hM]; exact natAbs_signed _ _
    refine ⟨⟨roundToInt rm (f.toExact a), 0, ?_, ?_, by simp⟩, ?_⟩
    · rw [hna]; simp only [prec]
      have : 2 ^ f.fracBits < 2 ^ (f.fracBits + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    · show f.ulpMin ≤ 0
      have := f.emin_nonpos hf; simp only [ulpMin]; omega
    · have habs : (roundToInt rm (f.toExact a) : Rat).abs = (M : Rat) := by
        have h0 : (0 : Rat) ≤ (M : Rat) := Rat.natCast_nonneg
        rw [hM]
        cases (f.toExact a).sign <;>
          simp only [Bool.false_eq_true, ite_true, ite_false, Rat.intCast_neg, Rat.intCast_natCast,
            Rat.abs] <;> split <;> grind
      rw [habs]
      refine Rat.le_trans ?_ (Rat.le_trans (two_zpow_le hcap) (two_emax_le f))
      rw [two_zpow_nat]; exact_mod_cast hM2

/-- **RINT meets `RintSpec`** (generic in the format; `hcap`: integers up to `2^fracBits` are
finite, true of binary32 and binary64). -/
theorem rint_spec (hf : f.WF) (hcap : (f.fracBits : Int) ≤ f.emax) (e : Env) {a : Nat}
    (ha : a < 2 ^ f.width) : f.RintSpec e a (f.rint e a) := by
  have hM1 : 1 ≤ f.expMax := by
    simp only [expMax]; have := Nat.pow_le_pow_right (n := 2) (by omega) hf.1; simp at this; omega
  unfold RintSpec
  split
  · rename_i hfl
    obtain ⟨h1, h2, h3⟩ := hfl
    simp only [expOf, fracOf] at h2 h3
    have he : f.expField a = 0 := h2
    have hfr : f.fracField a ≠ 0 := h3
    have na : f.isNaN a = false := by simp [isNaN, he]; omega
    have ia : f.isInf a = false := by simp [isInf, he]; omega
    have iz : f.isZero a = false := by simp [isZero, he, hfr]
    have hs : f.isSubnormal a = true := by simp [isSubnormal, he, hfr]
    simp only [rint, na, ia, iz, h1, hs, Bool.or_self, Bool.and_self, Bool.false_eq_true, ite_false,
      ite_true]
    rw [zeroBits_eq, signOf_eq]; rfl
  rename_i hfl
  have hfl' : (e.flush && f.isSubnormal a) = false := by
    cases h : e.flush
    · rfl
    · simp only [Bool.true_and]
      simp only [isSubnormal, Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]
      by_cases h2 : f.expField a = 0
      · exact .inr (Classical.byContradiction fun h3 => hfl ⟨h, h2, h3⟩)
      · exact .inl h2
  rcases f.classify hf a ha with ⟨na, -, da⟩ | ⟨na, ia, -, da⟩ | ⟨na, ia, -, da, va, za⟩
  · simp only [da, rint, na, ite_true]
    exact f.nanResult_spec hf [a]
  · simp only [da, rint, na, ia, Bool.true_or, ite_true, Bool.false_eq_true, ite_false]
    rw [infBits_eq, ← f.eq_inf_of_isInf ha ia]; rfl
  · simp only [da]
    have hsv := f.toExact_sign a
    have hcr := roundToInt_cr e.rm (f.toExact a)
    -- the Inexact flag
    have hfl : ({ inexact := !(f.toExact a).isIntegral } : Flags) =
        (if ((roundToInt e.rm (f.toExact a) : Int) : Rat) = (f.toExact a).toRat then {}
          else { inexact := true }) := by
      have := isIntegral_iff e.rm (f.toExact a)
      cases h : (f.toExact a).isIntegral
      · have : ¬ ((roundToInt e.rm (f.toExact a) : Int) : Rat) = (f.toExact a).toRat := fun h' =>
          by simp [this.2 h'] at h
        simp [this]
      · simp [this.1 h]
    by_cases hz : f.isZero a = true
    · have hx0 := za.2 hz
      have hI : roundToInt e.rm (f.toExact a) = 0 := by
        rw [hx0] at hcr
        have := cr_self (S := IsInt) (E := IsEvenInt) ⟨0, by simp⟩ hcr
        exact_mod_cast this
      simp only [rint, na, ia, hz, Bool.or_true, Bool.false_eq_true, ite_false, ite_true]
      refine ⟨0, ?_, ?_, signOf_eq f a, ?_⟩
      · rw [hx0] at hcr ⊢; rw [hI] at hcr; exact hcr
      · rw [va, hx0]; simp
      · rw [hx0]; simp; rfl
    · simp only [rint, na, ia, hz, Bool.or_self, Bool.false_eq_true, ite_false, hfl']
      obtain ⟨M, hM, hcase⟩ := roundToInt_shape e.rm (f.toExact a)
      have hna : (roundToInt e.rm (f.toExact a)).natAbs = M := by rw [hM]; exact natAbs_signed _ _
      rw [hna, ← hsv]
      refine ⟨roundToInt e.rm (f.toExact a), hcr, ?_⟩
      by_cases hM0 : M = 0
      · have hI : roundToInt e.rm (f.toExact a) = 0 := by rw [hM, hM0]; cases (f.toExact a).sign <;> rfl
        rw [hM0, f.roundEnv_zero e _ rfl]
        refine ⟨?_, ?_, hfl⟩
        · rw [hI, ← zeroBits_eq]; simpa using f.zeroBits_value hf _
        · simp only; rw [← zeroBits_eq, zeroBits_signOf]
      · have hw : (⟨(f.toExact a).sign, M, 0⟩ : Exact).sig ≠ 0 := hM0
        have hsp := f.roundEnv_spec_rat hf e _ hw
        rw [toRat_signed_int, ← hM] at hsp
        have hI0 : roundToInt e.rm (f.toExact a) ≠ 0 := by
          rw [hM]; cases (f.toExact a).sign <;> simp <;> omega
        have hge := f.int_abs_ge hf hI0
        obtain ⟨-, hR⟩ := hsp
        have hnt : ¬ (e.flush = true ∧ f.TinyBefore (Cut.ofRat (roundToInt e.rm (f.toExact a) : Rat))) := by
          rintro ⟨-, t1, t2⟩
          simp only [Cut.ofRat] at t1 t2
          simp only [Rat.abs] at hge; split at hge <;> grind
        obtain ⟨R, hRs, hb, -⟩ := hR hnt
        obtain ⟨hunb, hmax⟩ := f.rint_bounds hf hcap va e.rm M hM hcase
        obtain ⟨-, hv, -, -⟩ := f.roundSpec_exact hRs hunb hmax hge
        obtain ⟨r, -, -, -, -, hsb, -⟩ := hRs
        refine ⟨by rw [hb]; exact hv, ?_, hfl⟩
        rw [hb]
        simp only [signOf]
        simp only [Cut.ofRat] at hsb
        rw [hM] at hsb hI0
        cases hs : (f.toExact a).sign <;> simp only [hs, Bool.false_eq_true, ite_true, ite_false] at hsb hI0 ⊢
        · have : ¬ (((M : Int) : Rat) ≤ 0) := by
            have : (0 : Int) < M := by omega
            exact fun h => by have := Rat.intCast_le_intCast.1 (show ((M : Int) : Rat) ≤ ((0 : Int) : Rat) by simpa using h); omega
          simp only [hsb, decide_eq_false_iff_not]; exact this
        · have : ((-(M : Int) : Int) : Rat) ≤ 0 := by
            have := Rat.intCast_le_intCast.2 (show -(M : Int) ≤ 0 by omega); simpa using this
          simp only [hsb, decide_eq_true_eq]; exact this

theorem rint_lt (hf : f.WF) (e : Env) {a : Nat} (ha : a < 2 ^ f.width) :
    (f.rint e a).1 < 2 ^ f.width := by
  unfold rint; split
  · exact f.nanResult_lt hf [a] (by simpa using ha)
  · split
    · exact ha
    · split
      · exact f.zero_lt _
      · exact f.roundEnv_lt hf e _

end Format

/-- **`RINT.S`** on all operands, every FCSR environment (FCSR.FS input flushing, with its Inexact, is
part of `RintSpec`). -/
theorem f32Rint_spec (e : Env) (a : BitVec 32) :
    binary32.RintSpec e a.toNat ((f32Rint e a).1.toNat, (f32Rint e a).2) := by
  simp only [f32Rint]
  rw [pair_toNat (w := 32) _ (binary32.rint_lt binary32_wf e a.isLt)]
  exact binary32.rint_spec binary32_wf (by decide) e a.isLt

/-- **`RINT.D`**. -/
theorem f64Rint_spec (e : Env) (a : BitVec 64) :
    binary64.RintSpec e a.toNat ((f64Rint e a).1.toNat, (f64Rint e a).2) := by
  simp only [f64Rint]
  rw [pair_toNat (w := 64) _ (binary64.rint_lt binary64_wf e a.isLt)]
  exact binary64.rint_spec binary64_wf (by decide) e a.isLt

end Mips.Fp
