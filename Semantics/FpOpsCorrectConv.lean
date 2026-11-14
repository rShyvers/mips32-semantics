import Semantics.FpOpsCorrectWord
import Semantics.FpOpsCorrectRsqrtAux

/-!
# FpOpsCorrectConv — conversions between formats and from words

`Format.convert` (`CVT.S.D`, `CVT.D.S`) meets `Format.ConvertSpec`; the widening `CVT.D.S` and
`CVT.D.W` are exact (`Format.ExactSpec`, MD00086 Vol II-A Rev 6.06 CVT.D.fmt p.153: "If fmt is S or
W, then the operation is always exact"); `Format.ofInt` (`CVT.S.W`) meets `Format.FromIntSpec`.
-/

namespace Mips.Fp

/-! ## A representable value rounds to itself, exactly -/

theorem grid_mono {p p' : Nat} {P P' : Int → Prop} (hp : p ≤ p') (hP : ∀ e, P e → P' e) {x : Rat}
    (h : Grid p P x) : Grid p' P' x := by
  obtain ⟨m, e, hm, he, hx⟩ := h
  exact ⟨m, e, Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hp), hP e he, hx⟩

namespace Format

variable (f : Format)

/-- If `x` is a value of the format with the exponent range unbounded above, within the finite
range and not tiny, every rounding outcome for `x` is exact: no overflow, the value `x`, not
inexact, not tiny. -/
theorem roundSpec_exact {rm : RoundingMode} {x : Rat} {R : Rounded}
    (h : f.RoundSpec rm (Cut.ofRat x) R) (hx : f.Unbounded x) (hmax : x.abs ≤ f.maxValue)
    (hmin : (2 : Rat) ^ f.emin ≤ x.abs) :
    R.overflow = false ∧ f.value R.bits = some x ∧ R.inexact = false ∧ R.tiny = false := by
  obtain ⟨r, hcr, hov, hval, -, -, hinex, htiny⟩ := h
  have hr := cr_self hx hcr
  subst hr
  have ho : R.overflow = false := by
    cases h : R.overflow
    · rfl
    · have := hov.1 h; grind
  refine ⟨ho, hval ho, ?_, ?_⟩
  · cases h : R.inexact
    · rfl
    · exact absurd ⟨Rat.le_refl, Rat.le_refl⟩ (hinex.1 h)
  · cases h : R.tiny
    · rfl
    · obtain ⟨u, hu, hlt⟩ := htiny.1 h
      have hxr : f.UnboundedRange r := by
        obtain ⟨m, e, hm, -, he⟩ := hx; exact ⟨m, e, hm, trivial, he⟩
      have := cr_self hxr hu
      subst this; grind

theorem zeroBits_value (hf : f.WF) (s : Bool) : f.value (f.zeroBits s) = some 0 := by
  have hM : 0 < f.expMax := by
    simp only [expMax]; have := Nat.pow_le_pow_right (n := 2) (by omega) hf.1; simp at this; omega
  rw [zeroBits_eq]; simp only [zero]; rw [f.value_pack s 0 0 hM (Nat.two_pow_pos _)]; simp

theorem zeroBits_signOf (s : Bool) : f.signOf (f.zeroBits s) = s := by
  rw [zeroBits_eq, signOf_eq]; simp only [zero]
  obtain ⟨-, -, h3, -⟩ := f.pack_fields s 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  simp only [signBit, h3]; cases s <;> rfl

theorem signaled_none {R : Rounded} {fl : Flags} (h : Signaled {} R fl) (ho : R.overflow = false)
    (hi : R.inexact = false) (ht : R.tiny = false) : fl = {} := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [ho] at h3; rw [ht] at h4; rw [hi, ho] at h5
  cases fl; simp_all

/-! ## `CVT.S.D`, `CVT.D.S`: between formats -/

theorem convertNaN_qnan (src dst : Format) (hs : src.WF) (hd : dst.WF) {a : Nat}
    (hq : src.IsQNaN a) : dst.IsQNaN (convertNaN src dst a).1 ∧ (convertNaN src dst a).2 = {} := by
  have hns : src.isSNaN a = false := by
    cases h : src.isSNaN a
    · rfl
    · have := (src.isSNaN_iff a).1 h; have := hq.2; have := this; simp_all [IsSNaN]
  have hfr : src.fracOf a < 2 ^ (src.fracBits - 1) := by
    have := hq.2
    have h2 : 2 ^ src.fracBits = 2 ^ (src.fracBits - 1) * 2 := by
      rw [← Nat.pow_succ]; congr 1; have := hs.2; omega
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).1 this
  have hne : src.fracOf a ≠ 0 := hq.1.2
  have hd2 := hd.2
  simp only [convertNaN, hns, Bool.false_eq_true, ite_false]
  generalize hF : (if src.fracBits ≤ dst.fracBits then src.fracField a * 2 ^ (dst.fracBits - src.fracBits)
    else src.fracField a / 2 ^ (src.fracBits - dst.fracBits)) = F
  have hFlt : F < 2 ^ (dst.fracBits - 1) := by
    rw [← hF]; simp only [fracOf] at hfr; split
    · rename_i hle
      calc src.fracField a * 2 ^ (dst.fracBits - src.fracBits)
          < 2 ^ (src.fracBits - 1) * 2 ^ (dst.fracBits - src.fracBits) :=
            Nat.mul_lt_mul_of_pos_right hfr (Nat.two_pow_pos _)
        _ = 2 ^ (dst.fracBits - 1) := by rw [← Nat.pow_add]; congr 1; have := hs.2; omega
    · rename_i hle
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
      calc src.fracField a < 2 ^ (src.fracBits - 1) := hfr
        _ = 2 ^ (dst.fracBits - 1 + (src.fracBits - dst.fracBits)) := by congr 1; omega
  split
  · exact ⟨dst.newQNaN_eq ▸ dst.newQNaN_isQNaN hd, rfl⟩
  · rename_i hF0
    have hlt : F < 2 ^ dst.fracBits :=
      Nat.lt_of_lt_of_le hFlt (Nat.pow_le_pow_right (by omega) (by omega))
    obtain ⟨e1, e2, -, -⟩ := dst.pack_fields (src.signBit a) dst.expMax F dst.expMax_lt hlt
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
    · simp only [expOf]; exact e1
    · simp only [fracOf, e2]; exact hF0
    · simp only [fracOf, e2]; exact Nat.div_eq_of_lt hFlt

/-- **`ConvertFmt` between formats meets `ConvertSpec`** for every `src.width`-bit operand. -/
theorem convert_spec (src dst : Format) (hs : src.WF) (hd : dst.WF) (e : Env) {a : Nat}
    (ha : a < 2 ^ src.width) : ConvertSpec src dst e a (convert src dst e a) := by
  rcases src.classify hs a ha with ⟨na, -, da⟩ | ⟨na, ia, -, da⟩ | ⟨na, ia, -, da, -, za⟩
  · simp only [ConvertSpec, da, convert, na, ite_true]
    refine ⟨fun hsn => ?_, fun hq => convertNaN_qnan src dst hs hd hq⟩
    simp [convertNaN, (src.isSNaN_iff a).2 hsn, invalidResult_eq]
  · simp [ConvertSpec, da, convert, na, ia, infBits_eq, flags_none]
  · simp only [ConvertSpec, da, convert, na, ia, Bool.false_eq_true, ite_false]
    by_cases hx : (src.toExact a).toRat = 0
    · simp only [hx, ite_true]
      have h0 := (toRat_eq_zero_iff _).1 hx
      rw [dst.roundEnv_zero e _ h0, zeroBits_eq]
      simp only [toExact]; split <;> rfl
    · simp only [hx, ite_false]
      exact dst.roundEnv_spec_rat hd e _ (exact_sig_ne_zero hx)

/-- The value of a finite encoding of a small format is a value of a larger format with the
exponent range unbounded above. -/
theorem value_unbounded_of (src dst : Format) (hp : src.prec ≤ dst.prec)
    (hu : dst.ulpMin ≤ src.ulpMin) {a : Nat} {x : Rat} (h : src.value a = some x) : dst.Unbounded x :=
  grid_mono hp (fun _ he => Int.le_trans hu he) (representable_unbounded src ⟨a, h⟩)

theorem abs_ge_of_value (src : Format) {a : Nat} {x : Rat} (h : src.value a = some x) (hx : x ≠ 0) :
    (2 : Rat) ^ src.qMin ≤ x.abs := by
  rcases rat_lt_or_le 0 x with hp | hn
  · have := value_pos_ge src h hp
    simp only [Rat.abs]; split <;> grind
  · have hn' : 0 < -x := by grind
    have := value_pos_ge src (negBits_value src h) hn'
    simp only [Rat.abs]; split <;> grind

/-- **A widening conversion is exact**: for formats with `src.prec ≤ dst.prec`, every finite `src`
value within `dst`'s finite range and above its tiny range rounds (RN, no flush) to itself with no
exception. -/
theorem convert_exact (src dst : Format) (hs : src.WF) (hd : dst.WF)
    (hp : src.prec ≤ dst.prec) (hu : dst.ulpMin ≤ src.ulpMin)
    (hmax : src.maxValue ≤ dst.maxValue) (hmin : dst.emin ≤ src.qMin) {a : Nat}
    (ha : a < 2 ^ src.width) : WidenSpec src dst a (convert src dst Env.RN a) := by
  have hc := convert_spec src dst hs hd Env.RN ha
  rcases src.classify hs a ha with ⟨-, -, da⟩ | ⟨-, -, -, da⟩ | ⟨-, -, -, da, va, -⟩
  · simp only [ConvertSpec, da] at hc; simp only [WidenSpec, da]; exact hc
  · simp only [ConvertSpec, da] at hc; simp only [WidenSpec, da]; exact hc
  · simp only [ConvertSpec, da] at hc; simp only [WidenSpec, da, ExactSpec]
    generalize (src.toExact a).toRat = x at hc va
    by_cases hx : x = 0
    · simp only [hx, ite_true] at hc
      subst hx
      rw [hc]
      exact ⟨dst.zeroBits_value hd _, dst.zeroBits_signOf _, rfl⟩
    · simp only [hx, ite_false] at hc
      obtain ⟨-, hR⟩ := hc
      obtain ⟨R, hRs, hb, hsig⟩ := hR (by simp [Env.RN])
      have habs := value_abs_le_max src hs va
      have hge := abs_ge_of_value src va hx
      obtain ⟨ho, hv, hi, ht⟩ := dst.roundSpec_exact hRs (value_unbounded_of src dst hp hu va)
        (Rat.le_trans habs hmax) (Rat.le_trans (two_zpow_le hmin) hge)
      have hsg := hRs
      obtain ⟨r, hcr, -, -, -, hsb, -⟩ := hsg
      refine ⟨by rw [hb]; exact hv, ?_, signaled_none hsig ho hi ht⟩
      rw [hb]
      have hsx : (src.toExact a).sign = src.signBit a := by simp only [toExact]; split <;> rfl
      have := exact_sign_iff (src.toExact a) (src.toExact_sig_ne_zero va hx)
      rw [value_toExact src va, hsx] at this
      simp only [signOf]
      have hsb' := hsb
      simp only [Cut.ofRat] at hsb'
      cases h : src.signBit a <;> simp_all <;> grind

/-! ## `CVT.S.W`, `CVT.D.W`: from a word -/

theorem int_exact_toRat (i : Int) : (Exact.toRat ⟨decide (i < 0), i.natAbs, 0⟩) = i := by
  simp only [Exact.toRat, Rat.zpow_zero, Rat.mul_one]
  by_cases h : i < 0
  · simp only [h, decide_true, ite_true]
    have : (i.natAbs : Int) = -i := by omega
    rw [show ((i.natAbs : Nat) : Rat) = ((i.natAbs : Int) : Rat) from rfl, this]; push_cast; grind
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, Rat.one_mul]
    have : (i.natAbs : Int) = i := by omega
    rw [show ((i.natAbs : Nat) : Rat) = ((i.natAbs : Int) : Rat) from rfl, this]

/-- **`CVT.S.W` / `CVT.D.W` (rounded)** meet `FromIntSpec`. -/
theorem ofInt_spec (hf : f.WF) (e : Env) (i : Int) : f.FromIntSpec e i (f.ofInt e i) := by
  simp only [FromIntSpec, ofInt]
  by_cases hi : i = 0
  · subst hi; simp only [ite_true]
    rw [f.roundEnv_zero e _ rfl, zeroBits_eq]; rfl
  · simp only [hi, ite_false]
    have := f.roundEnv_spec_rat hf e ⟨decide (i < 0), i.natAbs, 0⟩ (by simp; omega)
    rw [int_exact_toRat] at this; exact this

end Format

end Mips.Fp
