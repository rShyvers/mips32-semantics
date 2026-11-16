import Semantics.FpOpsCorrectCompare
import Semantics.FpOpsCorrectFcsr

/-!
# FpOpsCorrectIEEE — the headline theorems on `BitVec`

Every FP operation of the model that `step` uses, on **all** operands and every FCSR environment,
meets its reference definition of `Semantics/FpOpsSpec.lean`:

| model | reference | manual |
|---|---|---|
| `f32Add`/`f64Add`, `f32Sub`/`f64Sub` | `Format.AddSpec` | ADD.fmt p.34, SUB.fmt p.389 |
| `f32Mul`/`f64Mul` | `Format.MulSpec` | MUL.fmt p.302 |
| `f32Div`/`f64Div` | `Format.DivSpec` | DIV.fmt p.170 |
| `f32Sqrt`/`f64Sqrt` | `Format.SqrtSpec` | SQRT.fmt p.382 |
| `f64ToF32` (CVT.S.D) | `Format.ConvertSpec` | CVT.S.fmt p.159 |
| `f32ToF64` (CVT.D.S) | `Format.WidenSpec` (exact) | CVT.D.fmt p.153 |
| `w32ToF32` (CVT.S.W) | `Format.FromIntSpec` | CVT.S.fmt p.159 |
| `w32ToF64F` (CVT.D.W) | `Format.ExactSpec` | CVT.D.fmt p.153 |
| `w64ToF32` (CVT.S.L), `w64ToF64` (CVT.D.L) | `Format.FromIntSpec` | CVT.S.fmt p.159, CVT.D.fmt p.153 |
| `f32ToW32`/`f64ToW32` | `Format.ToWordSpec` | CVT.W p.160, ROUND.W p.342, TRUNC.W p.441, CEIL.W p.128, FLOOR.W p.186 |
| `f32ToW64`/`f64ToW64` | `Format.ToLongSpec` | CVT.L p.154, ROUND.L p.341, TRUNC.L p.440, CEIL.L p.127, FLOOR.L p.185 |
| `f32Compare`/`f64Compare` | `Format.CompareSpec` | C.cond.fmt p.110-113 |
| `f32Abs`/`f64Abs`, `f32Neg`/`f64Neg` | `Format.SignOpSpec` | ABS.fmt p.32, NEG.fmt p.307 |
| `fpUpdate` | `FcsrSpec` | MD00082 §6.7.1 p.99; CheckFPException p.23 |

(Page numbers: MD00086 Vol II-A Rev 6.06, unless MD00082 Vol I-A Rev 6.01 is named.)

Every floating-point operand of an arithmetic operation or conversion is taken as the operation
sees it, `Format.FlushedIn` under FCSR.FS (MD00082 Vol I-A Rev 6.01 Table 6.8, `FS`, p.93: "every
input subnormal value is replaced with zero of the same sign"); `flushIn_eq` identifies the model's
`Format.flushIn` with it. The flush signals Inexact ("Flushing of subnormal input operands in all
instructions except comparisons causes Inexact exception to be signaled", §6.7.2.4, p.102): each
statement is wrapped in `Format.WithFlushInexact` (`flushFlags_inexact`, `withFlush_intro`). `ABS`/`NEG`
are non-arithmetic and take the operand as encoded.
-/

namespace Mips.Fp

theorem toNat_ofNat_lt {w n : Nat} (h : n < 2 ^ w) : (BitVec.ofNat w n).toNat = n := by
  simp [Nat.mod_eq_of_lt h]

theorem pair_toNat {w : Nat} (r : Nat × Flags) (h : r.1 < 2 ^ w) :
    ((BitVec.ofNat w r.1).toNat, r.2) = r := by
  rw [toNat_ofNat_lt h]

theorem width32 : binary32.width = 32 := rfl
theorem width64 : binary64.width = 64 := rfl

/-! ## Input flushing -/

/-- **The model's operand flushing is `FlushedIn`** (on every encoding). -/
theorem Format.flushIn_eq (f : Format) (fl : Bool) (n : Nat) : f.flushIn fl n = f.FlushedIn fl n := by
  unfold Format.flushIn Format.FlushedIn
  rw [Format.signOf_eq, Format.zeroBits_eq]
  split <;> split <;> first
    | rfl
    | (exfalso; simp_all [Format.isSubnormal, Format.expOf, Format.fracOf, Format.expField,
        Format.fracField])

theorem Format.flushIn_lt (f : Format) (fl : Bool) {n : Nat} (hn : n < 2 ^ f.width) :
    f.flushIn fl n < 2 ^ f.width := by
  simp only [Format.flushIn]; split
  · exact f.zero_lt _
  · exact hn

/-- **The model's flush flags are `FlushInexact`**: Inexact iff FS and some operand is subnormal. -/
theorem Format.flushFlags_inexact (f : Format) (fl : Bool) (ops : List Nat) :
    (f.flushFlags fl ops).inexact = decide (f.FlushInexact fl ops) := by
  cases fl
  · simp [Format.flushFlags, Format.FlushInexact]
  · simp only [Format.flushFlags, Bool.true_and]
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
    simp [Format.FlushInexact, Format.isSubnormal, Format.expOf, Format.fracOf, Format.expField,
      Format.fracField]

/-- **ORing the flush flags meets `WithFlushInexact`**, for any reference definition `P` met with the
operation's own flags `g`. -/
theorem Format.withFlush_intro {α : Type} (f : Format) (fl : Bool) (ops : List Nat)
    (P : α × Flags → Prop) (x : α) (g : Flags) (h : P (x, g)) :
    f.WithFlushInexact fl ops P (x, g.or (f.flushFlags fl ops)) := by
  refine ⟨g, h, ?_⟩
  rw [← Format.flushFlags_inexact]
  cases g; simp [Flags.or, Format.flushFlags]

/-- `withFlush` form of `withFlush_intro`. -/
theorem Format.withFlush_spec {α : Type} (f : Format) (fl : Bool) (ops : List Nat)
    (P : α × Flags → Prop) (r : α × Flags) (h : P r) :
    f.WithFlushInexact fl ops P (f.withFlush fl ops r) :=
  f.withFlush_intro fl ops P r.1 r.2 h

/-! ## ADD, SUB, MUL, DIV, SQRT -/

/-- **`ADD.S`** on all operands, every FCSR environment. -/
theorem f32Add_spec (e : Env) (a b : BitVec 32) :
    binary32.WithFlushInexact e.flush [a.toNat, b.toNat]
      (binary32.AddSpec e false (binary32.FlushedIn e.flush a.toNat) (binary32.FlushedIn e.flush b.toNat))
      ((f32Add e a b).1.toNat, (f32Add e a b).2) := by
  have ha := binary32.flushIn_lt e.flush a.isLt; have hb := binary32.flushIn_lt e.flush b.isLt
  simp only [f32Add, Format.withFlush, ← Format.flushIn_eq]
  rw [toNat_ofNat_lt (w := 32) (binary32.add_lt binary32_wf e ha hb)]
  exact binary32.withFlush_intro _ _ _ _ _ (binary32.add_spec binary32_wf e ha hb)

/-- **`SUB.S`**. -/
theorem f32Sub_spec (e : Env) (a b : BitVec 32) :
    binary32.WithFlushInexact e.flush [a.toNat, b.toNat]
      (binary32.AddSpec e true (binary32.FlushedIn e.flush a.toNat) (binary32.FlushedIn e.flush b.toNat))
      ((f32Sub e a b).1.toNat, (f32Sub e a b).2) := by
  have ha := binary32.flushIn_lt e.flush a.isLt; have hb := binary32.flushIn_lt e.flush b.isLt
  simp only [f32Sub, Format.withFlush, ← Format.flushIn_eq]
  rw [toNat_ofNat_lt (w := 32) (binary32.sub_lt binary32_wf e ha hb)]
  exact binary32.withFlush_intro _ _ _ _ _ (binary32.sub_spec binary32_wf e ha hb)

/-- **`MUL.S`**. -/
theorem f32Mul_spec (e : Env) (a b : BitVec 32) :
    binary32.WithFlushInexact e.flush [a.toNat, b.toNat]
      (binary32.MulSpec e (binary32.FlushedIn e.flush a.toNat) (binary32.FlushedIn e.flush b.toNat))
      ((f32Mul e a b).1.toNat, (f32Mul e a b).2) := by
  have ha := binary32.flushIn_lt e.flush a.isLt; have hb := binary32.flushIn_lt e.flush b.isLt
  simp only [f32Mul, Format.withFlush, ← Format.flushIn_eq]
  rw [toNat_ofNat_lt (w := 32) (binary32.mul_lt binary32_wf e ha hb)]
  exact binary32.withFlush_intro _ _ _ _ _ (binary32.mul_spec binary32_wf e ha hb)

/-- **`DIV.S`**. -/
theorem f32Div_spec (e : Env) (a b : BitVec 32) :
    binary32.WithFlushInexact e.flush [a.toNat, b.toNat]
      (binary32.DivSpec e (binary32.FlushedIn e.flush a.toNat) (binary32.FlushedIn e.flush b.toNat))
      ((f32Div e a b).1.toNat, (f32Div e a b).2) := by
  have ha := binary32.flushIn_lt e.flush a.isLt; have hb := binary32.flushIn_lt e.flush b.isLt
  simp only [f32Div, Format.withFlush, ← Format.flushIn_eq]
  rw [toNat_ofNat_lt (w := 32) (binary32.div_lt binary32_wf e ha hb)]
  exact binary32.withFlush_intro _ _ _ _ _ (binary32.div_spec binary32_wf e ha hb)

/-- **`SQRT.S`**. -/
theorem f32Sqrt_spec (e : Env) (a : BitVec 32) :
    binary32.WithFlushInexact e.flush [a.toNat]
      (binary32.SqrtSpec e (binary32.FlushedIn e.flush a.toNat))
      ((f32Sqrt e a).1.toNat, (f32Sqrt e a).2) := by
  have ha := binary32.flushIn_lt e.flush a.isLt
  simp only [f32Sqrt, Format.withFlush, ← Format.flushIn_eq]
  rw [toNat_ofNat_lt (w := 32) (binary32.sqrt_lt binary32_wf e ha)]
  exact binary32.withFlush_intro _ _ _ _ _ (binary32.sqrt_spec binary32_wf e ha)

/-- **`ADD.D`**. -/
theorem f64Add_spec (e : Env) (a b : BitVec 64) :
    binary64.WithFlushInexact e.flush [a.toNat, b.toNat]
      (binary64.AddSpec e false (binary64.FlushedIn e.flush a.toNat) (binary64.FlushedIn e.flush b.toNat))
      ((f64Add e a b).1.toNat, (f64Add e a b).2) := by
  have ha := binary64.flushIn_lt e.flush a.isLt; have hb := binary64.flushIn_lt e.flush b.isLt
  simp only [f64Add, Format.withFlush, ← Format.flushIn_eq]
  rw [toNat_ofNat_lt (w := 64) (binary64.add_lt binary64_wf e ha hb)]
  exact binary64.withFlush_intro _ _ _ _ _ (binary64.add_spec binary64_wf e ha hb)

/-- **`SUB.D`**. -/
theorem f64Sub_spec (e : Env) (a b : BitVec 64) :
    binary64.WithFlushInexact e.flush [a.toNat, b.toNat]
      (binary64.AddSpec e true (binary64.FlushedIn e.flush a.toNat) (binary64.FlushedIn e.flush b.toNat))
      ((f64Sub e a b).1.toNat, (f64Sub e a b).2) := by
  have ha := binary64.flushIn_lt e.flush a.isLt; have hb := binary64.flushIn_lt e.flush b.isLt
  simp only [f64Sub, Format.withFlush, ← Format.flushIn_eq]
  rw [toNat_ofNat_lt (w := 64) (binary64.sub_lt binary64_wf e ha hb)]
  exact binary64.withFlush_intro _ _ _ _ _ (binary64.sub_spec binary64_wf e ha hb)

/-- **`MUL.D`**. -/
theorem f64Mul_spec (e : Env) (a b : BitVec 64) :
    binary64.WithFlushInexact e.flush [a.toNat, b.toNat]
      (binary64.MulSpec e (binary64.FlushedIn e.flush a.toNat) (binary64.FlushedIn e.flush b.toNat))
      ((f64Mul e a b).1.toNat, (f64Mul e a b).2) := by
  have ha := binary64.flushIn_lt e.flush a.isLt; have hb := binary64.flushIn_lt e.flush b.isLt
  simp only [f64Mul, Format.withFlush, ← Format.flushIn_eq]
  rw [toNat_ofNat_lt (w := 64) (binary64.mul_lt binary64_wf e ha hb)]
  exact binary64.withFlush_intro _ _ _ _ _ (binary64.mul_spec binary64_wf e ha hb)

/-- **`DIV.D`**. -/
theorem f64Div_spec (e : Env) (a b : BitVec 64) :
    binary64.WithFlushInexact e.flush [a.toNat, b.toNat]
      (binary64.DivSpec e (binary64.FlushedIn e.flush a.toNat) (binary64.FlushedIn e.flush b.toNat))
      ((f64Div e a b).1.toNat, (f64Div e a b).2) := by
  have ha := binary64.flushIn_lt e.flush a.isLt; have hb := binary64.flushIn_lt e.flush b.isLt
  simp only [f64Div, Format.withFlush, ← Format.flushIn_eq]
  rw [toNat_ofNat_lt (w := 64) (binary64.div_lt binary64_wf e ha hb)]
  exact binary64.withFlush_intro _ _ _ _ _ (binary64.div_spec binary64_wf e ha hb)

/-- **`SQRT.D`**. -/
theorem f64Sqrt_spec (e : Env) (a : BitVec 64) :
    binary64.WithFlushInexact e.flush [a.toNat]
      (binary64.SqrtSpec e (binary64.FlushedIn e.flush a.toNat))
      ((f64Sqrt e a).1.toNat, (f64Sqrt e a).2) := by
  have ha := binary64.flushIn_lt e.flush a.isLt
  simp only [f64Sqrt, Format.withFlush, ← Format.flushIn_eq]
  rw [toNat_ofNat_lt (w := 64) (binary64.sqrt_lt binary64_wf e ha)]
  exact binary64.withFlush_intro _ _ _ _ _ (binary64.sqrt_spec binary64_wf e ha)

/-! ## Conversions -/

theorem convertNaN_lt (src dst : Format) (hd : dst.WF) (a : Nat) :
    (Format.convertNaN src dst a).1 < 2 ^ dst.width := by
  unfold Format.convertNaN
  dsimp only
  rw [dst.quiet_eq_passedNaN hd]
  apply dst.passedNaN_lt hd
  have hF : src.fracField a < 2 ^ src.fracBits := Nat.mod_lt _ (Nat.two_pow_pos _)
  apply dst.pack_lt _ _ _ dst.expMax_lt
  split
  · calc src.fracField a * 2 ^ (dst.fracBits - src.fracBits)
        < 2 ^ src.fracBits * 2 ^ (dst.fracBits - src.fracBits) :=
          Nat.mul_lt_mul_of_pos_right hF (Nat.two_pow_pos _)
      _ = 2 ^ dst.fracBits := by rw [← Nat.pow_add]; congr 1; omega
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hF (Nat.pow_le_pow_right (by omega) (by omega))

theorem convert_lt (src dst : Format) (hd : dst.WF) (e : Env) (a : Nat) :
    (Format.convert src dst e a).1 < 2 ^ dst.width := by
  unfold Format.convert
  split
  · exact convertNaN_lt src dst hd a
  · split
    · exact dst.inf_lt _
    · exact dst.roundEnv_lt hd _ _

/-- **`CVT.S.D`** on every operand, every FCSR environment. -/
theorem f64ToF32_spec (e : Env) (x : BitVec 64) :
    binary64.WithFlushInexact e.flush [x.toNat]
      (Format.ConvertSpec binary64 binary32 e (binary64.FlushedIn e.flush x.toNat))
      ((f64ToF32 e x).1.toNat, (f64ToF32 e x).2) := by
  have hx := binary64.flushIn_lt e.flush x.isLt
  simp only [f64ToF32, Format.withFlush, ← Format.flushIn_eq]
  rw [toNat_ofNat_lt (w := 32) (convert_lt binary64 binary32 binary32_wf e _)]
  exact binary64.withFlush_intro _ _ _ _ _
    (Format.convert_spec binary64 binary32 binary64_wf binary32_wf e hx)

theorem max32_le_max64 : binary32.maxValue ≤ binary64.maxValue :=
  Rat.le_trans (Rat.le_of_lt (maxValue_lt binary32))
    (Rat.le_trans (two_zpow_le (by decide)) (two_emax_le binary64))

/-- **`CVT.D.S`** on every operand: exact (no exception) for a finite operand. -/
theorem f32ToF64_spec (fl : Bool) (x : BitVec 32) :
    binary32.WithFlushInexact fl [x.toNat]
      (Format.WidenSpec binary32 binary64 (binary32.FlushedIn fl x.toNat))
      ((f32ToF64 fl x).1.toNat, (f32ToF64 fl x).2) := by
  have hx := binary32.flushIn_lt fl x.isLt
  simp only [f32ToF64, Format.withFlush, ← Format.flushIn_eq]
  rw [toNat_ofNat_lt (w := 64) (convert_lt binary32 binary64 binary64_wf _ _)]
  exact binary32.withFlush_intro _ _ _ _ _
    (Format.convert_exact binary32 binary64 binary32_wf binary64_wf (by decide) (by decide)
      max32_le_max64 (by decide) hx)

/-- **`CVT.S.W`** on every word, every FCSR environment. -/
theorem w32ToF32_spec (e : Env) (x : BitVec 32) :
    binary32.FromIntSpec e x.toInt ((w32ToF32 e x).1.toNat, (w32ToF32 e x).2) := by
  simp only [w32ToF32]
  have hlt : (binary32.ofInt e x.toInt).1 < 2 ^ 32 := binary32.roundEnv_lt binary32_wf e _
  rw [pair_toNat (w := 32) _ hlt]
  exact binary32.ofInt_spec binary32_wf e x.toInt

/-- **`CVT.S.L`** on every longword, every FCSR environment. -/
theorem w64ToF32_spec (e : Env) (x : BitVec 64) :
    binary32.FromIntSpec e x.toInt ((w64ToF32 e x).1.toNat, (w64ToF32 e x).2) := by
  simp only [w64ToF32]
  have hlt : (binary32.ofInt e x.toInt).1 < 2 ^ 32 := binary32.roundEnv_lt binary32_wf e _
  rw [pair_toNat (w := 32) _ hlt]
  exact binary32.ofInt_spec binary32_wf e x.toInt

/-- **`CVT.D.L`** on every longword, every FCSR environment. -/
theorem w64ToF64_spec (e : Env) (x : BitVec 64) :
    binary64.FromIntSpec e x.toInt ((w64ToF64 e x).1.toNat, (w64ToF64 e x).2) := by
  simp only [w64ToF64]
  have hlt : (binary64.ofInt e x.toInt).1 < 2 ^ 64 := binary64.roundEnv_lt binary64_wf e _
  rw [pair_toNat (w := 64) _ hlt]
  exact binary64.ofInt_spec binary64_wf e x.toInt

theorem int_abs_bounds (i : Int) (hi : i ≠ 0) (hlo : -2 ^ 31 ≤ i) (hhi : i < 2 ^ 31) :
    (1 : Rat) ≤ (i : Rat).abs ∧ (i : Rat).abs ≤ (2 : Rat) ^ 31 := by
  have c1 : 0 < i → (1 : Rat) ≤ (i : Rat) := fun h => by exact_mod_cast (show (1 : Int) ≤ i by omega)
  have c2 : i < 0 → (1 : Rat) ≤ -(i : Rat) := fun h => by
    have := Rat.intCast_le_intCast.2 (show (1 : Int) ≤ -i by omega)
    rw [Rat.intCast_neg] at this; exact_mod_cast this
  have c3 : (i : Rat) ≤ (2 : Rat) ^ 31 := by
    have := Rat.intCast_le_intCast.2 (show i ≤ (2 : Int) ^ 31 by omega); rwa [rat_int_two_pow] at this
  have c4 : -(i : Rat) ≤ (2 : Rat) ^ 31 := by
    have := Rat.intCast_le_intCast.2 (show -i ≤ (2 : Int) ^ 31 by omega)
    rwa [rat_int_two_pow, Rat.intCast_neg] at this
  generalize (2 : Rat) ^ 31 = T at c3 c4 ⊢
  simp only [Rat.abs]
  rcases (by omega : 0 < i ∨ i < 0) with h | h
  · have := c1 h; split <;> constructor <;> grind
  · have := c2 h; split <;> constructor <;> grind

/-- `CVT.D.W` at the `Nat` level: the RN rounding of a word integer is exact. -/
theorem ofInt64_exact (i : Int) (hlo : -2 ^ 31 ≤ i) (hhi : i < 2 ^ 31) :
    binary64.ExactSpec (decide (i < 0)) i ((binary64.ofInt Env.RN i).1, Flags.none) := by
  have hs := binary64.ofInt_spec binary64_wf Env.RN i
  simp only [Format.FromIntSpec] at hs
  by_cases hi : i = 0
  · subst hi
    simp only [ite_true] at hs
    refine ⟨?_, ?_, rfl⟩ <;> simp only [hs]
    · exact binary64.zeroBits_value binary64_wf _
    · exact binary64.zeroBits_signOf _
  · simp only [hi, ite_false] at hs
    obtain ⟨-, hR⟩ := hs
    obtain ⟨R, hRs, hb, -⟩ := hR (by simp [Env.RN])
    obtain ⟨habs1, habs2⟩ := int_abs_bounds i hi hlo hhi
    have hunb : binary64.Unbounded (i : Rat) := by
      refine ⟨i, 0, ?_, by decide, by simp⟩
      have e : (2 : Int) ^ 31 = 2147483648 := by decide
      have h1 := hlo; have h2 := hhi
      rw [e] at h1 h2
      have : i.natAbs ≤ 2147483648 := by
        have hn := Int.natAbs_eq i
        generalize i.natAbs = n at hn
        rcases hn with h | h <;> omega
      exact Nat.lt_of_le_of_lt this (by decide)
    have hmax : (i : Rat).abs ≤ binary64.maxValue := by
      refine Rat.le_trans habs2 (Rat.le_trans ?_ (two_emax_le binary64))
      rw [← Rat.zpow_natCast]; exact two_zpow_le (by decide)
    have hmin : (2 : Rat) ^ binary64.emin ≤ (i : Rat).abs :=
      Rat.le_trans (by rw [show (1 : Rat) = (2 : Rat) ^ (0 : Int) by simp]; exact two_zpow_le (by decide)) habs1
    obtain ⟨-, hv, -, -⟩ := binary64.roundSpec_exact hRs hunb hmax hmin
    obtain ⟨r, -, -, -, -, hsb, -⟩ := hRs
    refine ⟨by rw [hb]; exact hv, ?_, rfl⟩
    show decide _ = decide _
    rw [hb]
    apply decide_eq_decide.2
    rw [hsb]
    simp only [Cut.ofRat]
    constructor
    · intro h
      have := Rat.intCast_le_intCast.1 (show (i : Rat) ≤ ((0 : Int) : Rat) by simpa using h); omega
    · intro h
      have := Rat.intCast_le_intCast.2 (show i ≤ 0 by omega); simpa using this

/-- **`CVT.D.W`** on every word: exact, no exception (`+0` for `0`). -/
theorem w32ToF64_spec (x : BitVec 32) :
    binary64.ExactSpec (decide (x.toInt < 0)) x.toInt ((w32ToF64F x).1.toNat, (w32ToF64F x).2) := by
  simp only [w32ToF64F, w32ToF64]
  have hlt : (binary64.ofInt Env.RN x.toInt).1 < 2 ^ 64 := binary64.roundEnv_lt binary64_wf Env.RN _
  rw [toNat_ofNat_lt hlt]
  exact ofInt64_exact x.toInt (BitVec.le_toInt x) BitVec.toInt_lt

/-- **`CVT.W.S`, `ROUND/TRUNC/CEIL/FLOOR.W.S`** in every direction, on every operand. -/
theorem f32ToW32_spec (rm : RoundingMode) (fl : Bool) (x : BitVec 32) :
    binary32.WithFlushInexact fl [x.toNat] (binary32.ToWordSpec rm (binary32.FlushedIn fl x.toNat)) (f32ToW32 rm fl x) := by
  rw [← Format.flushIn_eq]
  exact binary32.withFlush_spec _ _ _ _ (binary32.toW32_spec binary32_wf rm (binary32.flushIn_lt fl x.isLt))

/-- **`CVT.W.D`, `ROUND/TRUNC/CEIL/FLOOR.W.D`**. -/
theorem f64ToW32_spec (rm : RoundingMode) (fl : Bool) (x : BitVec 64) :
    binary64.WithFlushInexact fl [x.toNat] (binary64.ToWordSpec rm (binary64.FlushedIn fl x.toNat)) (f64ToW32 rm fl x) := by
  rw [← Format.flushIn_eq]
  exact binary64.withFlush_spec _ _ _ _ (binary64.toW32_spec binary64_wf rm (binary64.flushIn_lt fl x.isLt))

/-- **`CVT.L.S`, `ROUND/TRUNC/CEIL/FLOOR.L.S`** in every direction, on every operand. -/
theorem f32ToW64_spec (rm : RoundingMode) (fl : Bool) (x : BitVec 32) :
    binary32.WithFlushInexact fl [x.toNat] (binary32.ToLongSpec rm (binary32.FlushedIn fl x.toNat)) (f32ToW64 rm fl x) := by
  rw [← Format.flushIn_eq]
  exact binary32.withFlush_spec _ _ _ _ (binary32.toW64_spec binary32_wf rm (binary32.flushIn_lt fl x.isLt))

/-- **`CVT.L.D`, `ROUND/TRUNC/CEIL/FLOOR.L.D`**. -/
theorem f64ToW64_spec (rm : RoundingMode) (fl : Bool) (x : BitVec 64) :
    binary64.WithFlushInexact fl [x.toNat] (binary64.ToLongSpec rm (binary64.FlushedIn fl x.toNat)) (f64ToW64 rm fl x) := by
  rw [← Format.flushIn_eq]
  exact binary64.withFlush_spec _ _ _ _ (binary64.toW64_spec binary64_wf rm (binary64.flushIn_lt fl x.isLt))

/-! ## Compares -/

/-- **`C.cond.S`** for all 16 conditions and all operands. -/
theorem f32Compare_spec (cond : BitVec 4) (a b : BitVec 32) :
    binary32.CompareSpec cond a.toNat b.toNat (f32Compare cond a b) :=
  binary32.compare_spec binary32_wf cond a.isLt b.isLt

/-- **`C.cond.D`**. -/
theorem f64Compare_spec (cond : BitVec 4) (a b : BitVec 64) :
    binary64.CompareSpec cond a.toNat b.toNat (f64Compare cond a b) :=
  binary64.compare_spec binary64_wf cond a.isLt b.isLt

/-! ## ABS, NEG -/

theorem and_top {n k : Nat} (hn : n < 2 * 2 ^ k) :
    n &&& (2 ^ k - 1) = if n / 2 ^ k % 2 = 1 then n - 2 ^ k else n := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have hd := Nat.div_add_mod n (2 ^ k)
  have hq : n / 2 ^ k < 2 := by rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega
  have hr := Nat.mod_lt n (Nat.two_pow_pos k)
  generalize n / 2 ^ k = q at *
  generalize n % 2 ^ k = r at *
  generalize 2 ^ k = P at *
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> simp at * <;> omega

theorem xor_top {n k : Nat} (hn : n < 2 * 2 ^ k) :
    n ^^^ 2 ^ k = if n / 2 ^ k % 2 = 1 then n - 2 ^ k else n + 2 ^ k := by
  have hd := Nat.div_add_mod (n ^^^ 2 ^ k) (2 ^ k)
  rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow, Nat.div_self (Nat.two_pow_pos _), Nat.mod_self,
    Nat.xor_zero] at hd
  have hd' := Nat.div_add_mod n (2 ^ k)
  have hq : n / 2 ^ k < 2 := by rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega
  have hr := Nat.mod_lt n (Nat.two_pow_pos k)
  generalize n ^^^ 2 ^ k = X at *
  generalize n / 2 ^ k = q at *
  generalize n % 2 ^ k = r at *
  generalize 2 ^ k = P at *
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> simp at * <;> omega

theorem signChanged32 (clear : Bool) (x : BitVec 32) :
    binary32.signChanged clear x.toNat =
      if clear then (x &&& 0x7FFFFFFF#32).toNat else (x ^^^ 0x80000000#32).toNat := by
  have hx : x.toNat < 2 * 2 ^ 31 := x.isLt
  simp only [Format.signChanged, Format.signOf]
  cases clear <;> simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.toNat_and, BitVec.toNat_xor]
  · rw [show (0x80000000#32).toNat = 2 ^ 31 by rfl, xor_top hx]
    simp only [show binary32.expBits + binary32.fracBits = 31 by rfl]; split <;> simp_all
  · rw [show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 by rfl, and_top hx]
    simp only [show binary32.expBits + binary32.fracBits = 31 by rfl]; split <;> simp_all

theorem signChanged64 (clear : Bool) (x : BitVec 64) :
    binary64.signChanged clear x.toNat =
      if clear then (x &&& 0x7FFFFFFFFFFFFFFF#64).toNat else (x ^^^ 0x8000000000000000#64).toNat := by
  have hx : x.toNat < 2 * 2 ^ 63 := x.isLt
  simp only [Format.signChanged, Format.signOf]
  cases clear <;> simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.toNat_and, BitVec.toNat_xor]
  · rw [show (0x8000000000000000#64).toNat = 2 ^ 63 by rfl, xor_top hx]
    simp only [show binary64.expBits + binary64.fracBits = 63 by rfl]; split <;> simp_all
  · rw [show (0x7FFFFFFFFFFFFFFF#64).toNat = 2 ^ 63 - 1 by rfl, and_top hx]
    simp only [show binary64.expBits + binary64.fracBits = 63 by rfl]; split <;> simp_all

theorem signOp_cases (f : Format) (hf : f.WF) (a : Nat) :
    (f.IsSNaN a ↔ f.isNaN a = true ∧ f.isQNaN a = false) ∧ (f.IsQNaN a ↔ f.isQNaN a = true) := by
  refine ⟨?_, (f.isQNaN_iff a).symm⟩
  have hq : f.fracOf a / 2 ^ (f.fracBits - 1) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    have e : 2 ^ (f.fracBits - 1) * 2 = 2 ^ f.fracBits := by
      rw [← Nat.pow_succ]; congr 1; have := hf.2; omega
    rw [Nat.mul_comm, e]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have e1 : f.isQNaN a = false ↔ ¬ (f.IsNaN a ∧ f.fracOf a / 2 ^ (f.fracBits - 1) = 1) := by
    rw [← Bool.not_eq_true, f.isQNaN_iff]; rfl
  rw [e1, f.isNaN_iff]; unfold Format.IsSNaN
  generalize f.fracOf a / 2 ^ (f.fracBits - 1) = q at *
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun ⟨_, h⟩ => by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, Classical.byContradiction fun h => h2 ⟨h1, by omega⟩⟩

/-- **`ABS.S`** (`FCSR.ABS2008 = 1`: non-arithmetic, the sign bit cleared). -/
theorem f32Abs_spec (x : BitVec 32) : binary32.SignOpSpec true x.toNat (f32Abs x).toNat := by
  simp only [Format.SignOpSpec, signChanged32, ite_true, f32Abs]

/-- **`NEG.S`** (`FCSR.ABS2008 = 1`: non-arithmetic, the sign bit flipped). -/
theorem f32Neg_spec (x : BitVec 32) : binary32.SignOpSpec false x.toNat (f32Neg x).toNat := by
  simp only [Format.SignOpSpec, signChanged32, Bool.false_eq_true, ite_false, f32Neg]

/-- **`ABS.D`**. -/
theorem f64Abs_spec (x : BitVec 64) : binary64.SignOpSpec true x.toNat (f64Abs x).toNat := by
  simp only [Format.SignOpSpec, signChanged64, ite_true, f64Abs]

/-- **`NEG.D`**. -/
theorem f64Neg_spec (x : BitVec 64) : binary64.SignOpSpec false x.toNat (f64Neg x).toNat := by
  simp only [Format.SignOpSpec, signChanged64, Bool.false_eq_true, ite_false, f64Neg]

end Mips.Fp
