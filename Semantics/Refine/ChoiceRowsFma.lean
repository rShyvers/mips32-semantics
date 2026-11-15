import Semantics.Refine.ChoiceRowsFp

/-!
# Refine.ChoiceRowsFma — `C.cond.D`, `MADD/MSUB/NMADD/NMSUB.D` rows are real choices (wave 9)

* `C.cond.D` with an odd register the other operand does not absorb (`Manual.CmpAbsorbs`): a signaling
  NaN read raises Invalid Operation; a quiet NaN read (`cond3 = 0`) or `+1.0` (`cond3 = 1`) does not.
* `NMADD.D`/`NMSUB.D` (`fd` even): with the quiet NaN `QA64` read from every odd register, the value
  negated is a quiet NaN (`NR_q`), and the readings `A`/`B` of `Oracle.absNegNaN` differ in Invalid
  Operation; with no odd register the row's own condition says the sum is a quiet NaN.
* `MADD.D`/`MSUB.D` (`fd` even, outside `Manual.MaddAbsorbs`), by cases:
  (a) `fs` odd, (b) `fs` even not a quiet NaN and `ft` odd: two quiet NaNs read are delivered;
  (c) `fs` even a quiet NaN, `ft` and `fr` odd: the add raises Invalid for a signaling NaN read only;
  (d) `fs` even a quiet NaN, `ft` odd, `fr` even: with the Invalid enable set, a signaling NaN read traps
  in the multiply; otherwise (`fr` not a signaling NaN) it shows as Cause.V of the instruction (Wave 12a:
  Cause is the union of the operations' conditions);
  (e) `fs`, `ft` even, `fr` odd: as a binary add (`dist_right`).
-/

namespace Refine

open Manual

/-- `runp` with `FPResult` kept as one `if` on `trapC` (the FCSR algebra of `ChoiceFp`). -/
macro "runp_fe_simp" : tactic => `(tactic| simp only [bind, Pseudo.get, Pseudo.oracle, ValueFPR64, StoreFPR64,
    FPResult_eq, FPCheck_eq, trapC_fpc, fpf_fpc, fpc_fpc, FP32RegistersMode, beq_self_eq_true, ↓reduceIte, ctxOf, wo, sigRI, resolve, RunP_ok, RunP_sig,
    NotCpU, ne_eq, reduceCtorEq, not_false_eq_true, implies_true, Bool.false_eq_true, IEEE.mulD, IEEE.addD,
    IEEE.subD, IEEE.negD, IEEE.signOpD, env_fpf, trapC_fpf, pure, *])

macro "runp_fe" : tactic => `(tactic| (
  runp_fe_simp
  repeat' (case_ite <;> (try runp_fe_simp))
  all_goals (simp_all [CEof, bit6_fpf, bit16_fpf, PairV, FPRPair, update, fin32_ne_succ, split64,
    QA64_q, QB64_q, QA64_s, QB64_s, QA64_n, SN64_s, SN64_q, SN64_n, Mips.Fp.Flags.invalidOnly,
    Mips.Fp.Flags.none, IEEE.addD, IEEE.subD, IEEE.mulD, mul_qnan_left, add_qnan_left, sub_qnan_left,
    nr_qnan_left, nr_right_q, Mips.Fp.Flags.or])))

section
set_option linter.unusedSimpArgs false

/-! ## `C.cond.D` -/

theorem rw_cCondD (cond cc fs ft : W32) (a : Arch) (h : ConsultsOracle (.cCondD cond cc fs ft) a = true) :
    RowWitness (.cCondD cond cc fs ft) a := by
  simp only [ConsultsOracle, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', CmpAbsorbs,
    Bool.or_eq_false_iff, Bool.and_eq_false_iff, OddFPR, FPRPair] at h
  by_cases h3 : bit cond 3 = true
  · rcases h with (⟨hs, ht⟩ | ⟨⟨hs, ht⟩, hy1, hy2⟩) | ⟨⟨hs, ht⟩, hy1, hy2⟩ <;>
    · (try simp only [h3, Bool.true_and] at hy2)
      refine row_b16 rfl { rd := SN64 } { rd := One64 } (fun _ => ?_) (fun _ => ?_) <;>
        simp only [Ops.C_cond_D] <;> runp_fp
  · simp only [Bool.not_eq_true] at h3
    rcases h with (⟨hs, ht⟩ | ⟨⟨hs, ht⟩, hy1, hy2⟩) | ⟨⟨hs, ht⟩, hy1, hy2⟩ <;>
    · refine row_b16 rfl { rd := SN64 } { rd := QA64 } (fun _ => ?_) (fun _ => ?_) <;>
        simp only [Ops.C_cond_D] <;> runp_fp

/-! ## `NMADD.D`, `NMSUB.D` -/

/-- The value read from register `r` under the witness oracle reading `QA64`. -/
def rdQ (a : Arch) (r : W32) : BitVec 64 := if OddFPR r = true then QA64 else FPRPair a r

theorem rdQ_nan (a : Arch) (r : W32) (h : OddFPR r = true) : Mips.Fp.isNaN64 (rdQ a r) = true := by
  simp [rdQ, h, QA64_n]

theorem nmadd_q (a : Arch) (fr fs ft : W32)
    (h : (OddFPR fr || OddFPR fs || OddFPR ft ||
      Mips.Fp.isQNaN64 (IEEE.addD a (FPRPair a fr) (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).1).1) = true) :
    Mips.Fp.isQNaN64 (IEEE.addD a (rdQ a fr) (IEEE.mulD a (rdQ a fs) (rdQ a ft)).1).1 = true := by
  simp only [Bool.or_eq_true, IEEE.addD, IEEE.subD, IEEE.mulD] at h ⊢
  rcases h with ((hr | hs) | ht) | hq
  · exact add_q _ _ _ (by simp [rdQ_nan a fr hr])
  · exact add_q _ _ _ (by simp [qnan64_nan _ (mul_q (IEEE.env a) (rdQ a fs) (rdQ a ft) (by simp [rdQ_nan a fs hs]))])
  · exact add_q _ _ _ (by simp [qnan64_nan _ (mul_q (IEEE.env a) (rdQ a fs) (rdQ a ft) (by simp [rdQ_nan a ft ht]))])
  · by_cases hr : OddFPR fr = true
    · exact add_q _ _ _ (by simp [rdQ_nan a fr hr])
    by_cases hs : OddFPR fs = true
    · exact add_q _ _ _ (by simp [qnan64_nan _ (mul_q (IEEE.env a) (rdQ a fs) (rdQ a ft) (by simp [rdQ_nan a fs hs]))])
    by_cases ht : OddFPR ft = true
    · exact add_q _ _ _ (by simp [qnan64_nan _ (mul_q (IEEE.env a) (rdQ a fs) (rdQ a ft) (by simp [rdQ_nan a ft ht]))])
    simp only [Bool.not_eq_true] at hr hs ht
    simpa [rdQ, hr, hs, ht] using hq

theorem nmsub_q (a : Arch) (fr fs ft : W32)
    (h : (OddFPR fr || OddFPR fs || OddFPR ft ||
      Mips.Fp.isQNaN64 (IEEE.subD a (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).1 (FPRPair a fr)).1) = true) :
    Mips.Fp.isQNaN64 (IEEE.subD a (IEEE.mulD a (rdQ a fs) (rdQ a ft)).1 (rdQ a fr)).1 = true := by
  simp only [Bool.or_eq_true, IEEE.addD, IEEE.subD, IEEE.mulD] at h ⊢
  rcases h with ((hr | hs) | ht) | hq
  · exact sub_q _ _ _ (by simp [rdQ_nan a fr hr])
  · exact sub_q _ _ _ (by simp [qnan64_nan _ (mul_q (IEEE.env a) (rdQ a fs) (rdQ a ft) (by simp [rdQ_nan a fs hs]))])
  · exact sub_q _ _ _ (by simp [qnan64_nan _ (mul_q (IEEE.env a) (rdQ a fs) (rdQ a ft) (by simp [rdQ_nan a ft ht]))])
  · by_cases hr : OddFPR fr = true
    · exact sub_q _ _ _ (by simp [rdQ_nan a fr hr])
    by_cases hs : OddFPR fs = true
    · exact sub_q _ _ _ (by simp [qnan64_nan _ (mul_q (IEEE.env a) (rdQ a fs) (rdQ a ft) (by simp [rdQ_nan a fs hs]))])
    by_cases ht : OddFPR ft = true
    · exact sub_q _ _ _ (by simp [qnan64_nan _ (mul_q (IEEE.env a) (rdQ a fs) (rdQ a ft) (by simp [rdQ_nan a ft ht]))])
    simp only [Bool.not_eq_true] at hr hs ht
    simpa [rdQ, hr, hs, ht] using hq

set_option maxHeartbeats 1000000 in
theorem rw_nmaddD (fd fr fs ft : W32) (a : Arch) (h : ConsultsOracle (.nmaddD fd fr fs ft) a = true) :
    RowWitness (.nmaddD fd fr fs ft) a := by
  simp only [ConsultsOracle] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.NMADD_D]; runp
  have hq := nmadd_q a fr fs ft (by simp only [Bool.or_eq_true] at h ⊢; simp_all)
  have hs := qnan64_not_snan _ hq
  simp only [OddFPR, Bool.not_eq_true] at hd
  simp only [rdQ, OddFPR, FPRPair, IEEE.addD, IEEE.subD, IEEE.mulD] at hq hs
  exact row_AA'D rfl QA64 fd (IEEE.addD a (rdQ a fr) (IEEE.mulD a (rdQ a fs) (rdQ a ft)).1).1
    (fun _ => by simp only [Ops.NMADD_D, rdQ, OddFPR]; runp_fe) (fun _ => by simp only [Ops.NMADD_D, rdQ, OddFPR]; runp_fe)

set_option maxHeartbeats 1000000 in
theorem rw_nmsubD (fd fr fs ft : W32) (a : Arch) (h : ConsultsOracle (.nmsubD fd fr fs ft) a = true) :
    RowWitness (.nmsubD fd fr fs ft) a := by
  simp only [ConsultsOracle] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.NMSUB_D]; runp
  have hq := nmsub_q a fr fs ft (by simp only [Bool.or_eq_true] at h ⊢; simp_all)
  have hs := qnan64_not_snan _ hq
  simp only [OddFPR, Bool.not_eq_true] at hd
  simp only [rdQ, OddFPR, FPRPair, IEEE.addD, IEEE.subD, IEEE.mulD] at hq hs
  exact row_AA'D rfl QA64 fd (IEEE.subD a (IEEE.mulD a (rdQ a fs) (rdQ a ft)).1 (rdQ a fr)).1
    (fun _ => by simp only [Ops.NMSUB_D, rdQ, OddFPR]; runp_fe) (fun _ => by simp only [Ops.NMSUB_D, rdQ, OddFPR]; runp_fe)

end

/-! ## `MADD.D`, `MSUB.D` -/

theorem obs_bit6 (x y : Arch) (hx : bit x.FCSR 6 = true) (hy : bit y.FCSR 6 = false) : Obs x ≠ Obs y := by
  intro he; have := congrArg (fun o => o.2.2.2.2.1) he; simp only [Obs] at this; rw [this] at hx
  rw [hx] at hy; cases hy

/-- Two results that differ in value or Invalid still differ after the union with conditions `m`
without Invalid. -/
theorem dist_or (m : Mips.Fp.Flags) (hm : m.invalid = false) {r₁ r₂ : BitVec 64 × Mips.Fp.Flags}
    (hd : Dist r₁ r₂) : Dist (r₁.1, m.or r₁.2) (r₂.1, m.or r₂.2) := by
  rcases hd with h | h
  · exact .inl h
  · exact .inr (by simpa [Mips.Fp.Flags.or, hm] using h)

/-- Outside `MaddAbsorbs`, with `fs` even holding a quiet NaN, `ft` odd and `fr` even. -/
theorem not_absorbs (a : Arch) (fr fs ft : W32) (h : MaddAbsorbs a fr fs ft = false) (hs : OddFPR fs = false)
    (ht : OddFPR ft = true) (hr : OddFPR fr = false) (hx : Mips.Fp.isQNaN64 (FPRPair a fs) = true) :
    bit a.FCSR 11 = true ∨ Mips.Fp.isSNaN64 (FPRPair a fr) = false := by
  simp only [MaddAbsorbs, hs, ht, hr, hx, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
    Bool.or_false, Bool.and_eq_false_iff, Bool.not_eq_false'] at h
  exact h

section
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

theorem rw_maddD (fd fr fs ft : W32) (a : Arch) (h : ConsultsOracle (.maddD fd fr fs ft) a = true) :
    RowWitness (.maddD fd fr fs ft) a := by
  simp only [ConsultsOracle, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.MADD_D]; runp
  obtain ⟨hodd, hna⟩ := h.resolve_left hd
  simp only [OddFPR, Bool.not_eq_true] at hd
  by_cases hs : OddFPR fs = true
  · -- (a) `fs` odd: two quiet NaNs read are delivered
    simp only [OddFPR] at hs
    exact row_of rfl { rd := QA64 } { rd := QB64 } (fun x => FPRPair x fd = QA64) (fun x => FPRPair x fd = QB64)
      (obs_pair fd _ _ QA64_ne_QB64) (fun _ => by simp only [Ops.MADD_D]; runp_fe)
      (fun _ => by simp only [Ops.MADD_D]; runp_fe)
  simp only [Bool.not_eq_true] at hs
  by_cases ht : OddFPR ft = true
  · by_cases hx : Mips.Fp.isQNaN64 (FPRPair a fs) = true
    · by_cases hr : OddFPR fr = true
      · -- (c) the add raises Invalid for a signaling NaN read only
        simp only [OddFPR] at hr ht hs; simp only [FPRPair] at hx
        exact row_b16 rfl { rd := SN64 } { rd := QA64 } (fun _ => by simp only [Ops.MADD_D]; runp_fe)
          (fun _ => by simp only [Ops.MADD_D]; runp_fe)
      · simp only [Bool.not_eq_true] at hr
        rcases not_absorbs a fr fs ft hna hs ht hr hx with h11 | hz
        · -- (d) with the Invalid enable: the signaling NaN read traps in the multiply
          have hen := trapC_en _ h11
          simp only [OddFPR] at hr ht hs; simp only [FPRPair] at hx
          exact row_of rfl { rd := SN64 } { rd := QA64 } (fun _ => False) (fun _ => True)
            (fun _ _ hx => hx.elim) (fun _ => by simp only [Ops.MADD_D]; runp_fe)
            (fun _ => by simp only [Ops.MADD_D]; runp_fe)
        · -- (d) without it (and `fr` not a signaling NaN): the signaling NaN read shows in the
          -- instruction's Cause (bit 16, the union of the operations' conditions); the quiet one not
          simp only [OddFPR] at hr ht hs; simp only [FPRPair] at hx hz
          exact row_b16 rfl { rd := SN64 } { rd := QA64 } (fun _ => by simp only [Ops.MADD_D]; runp_fe)
            (fun _ => by simp only [Ops.MADD_D]; runp_fe)
    · -- (b) `fs` not a quiet NaN: the quiet NaN read is delivered
      simp only [OddFPR] at ht; simp only [FPRPair, Bool.not_eq_true] at hx
      have hm1 := mul_right_q (IEEE.env a) _ QA64 hx QA64_q
      have hm2 := mul_right_q (IEEE.env a) _ QB64 hx QB64_q
      exact row_of rfl { rd := QA64 } { rd := QB64 } (fun x => FPRPair x fd = QA64) (fun x => FPRPair x fd = QB64)
        (obs_pair fd _ _ QA64_ne_QB64) (fun _ => by simp only [Ops.MADD_D]; runp_fe)
        (fun _ => by simp only [Ops.MADD_D]; runp_fe)
  · -- (e) `fs`, `ft` even, `fr` odd, the multiply not Invalid (outside `MaddAbsorbs`): as a binary
    -- operation on the product, the instruction's Cause being the union with the multiply's
    have hr : OddFPR fr = true := by simp_all
    have hm : (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).2.invalid = false := by
      simp only [Bool.not_eq_true] at ht
      simpa [MaddAbsorbs, hs, ht, hr] using hna
    simp only [OddFPR, Bool.not_eq_true] at hr ht hs
    exact row_dist rfl fd
      ((IEEE.addD a (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).1 SN64).1,
        (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).2.or (IEEE.addD a (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).1 SN64).2)
      ((IEEE.addD a (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).1 QA64).1,
        (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).2.or (IEEE.addD a (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).1 QA64).2)
      (dist_or _ hm (dr_add (IEEE.env a) _)) (fun _ => by simp only [Ops.MADD_D]; runp_fe)
      (fun _ => by simp only [Ops.MADD_D]; runp_fe)

theorem rw_msubD (fd fr fs ft : W32) (a : Arch) (h : ConsultsOracle (.msubD fd fr fs ft) a = true) :
    RowWitness (.msubD fd fr fs ft) a := by
  simp only [ConsultsOracle, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.MSUB_D]; runp
  obtain ⟨hodd, hna⟩ := h.resolve_left hd
  simp only [OddFPR, Bool.not_eq_true] at hd
  by_cases hs : OddFPR fs = true
  · -- (a) `fs` odd: two quiet NaNs read are delivered
    simp only [OddFPR] at hs
    exact row_of rfl { rd := QA64 } { rd := QB64 } (fun x => FPRPair x fd = QA64) (fun x => FPRPair x fd = QB64)
      (obs_pair fd _ _ QA64_ne_QB64) (fun _ => by simp only [Ops.MSUB_D]; runp_fe)
      (fun _ => by simp only [Ops.MSUB_D]; runp_fe)
  simp only [Bool.not_eq_true] at hs
  by_cases ht : OddFPR ft = true
  · by_cases hx : Mips.Fp.isQNaN64 (FPRPair a fs) = true
    · by_cases hr : OddFPR fr = true
      · -- (c) the add raises Invalid for a signaling NaN read only
        simp only [OddFPR] at hr ht hs; simp only [FPRPair] at hx
        exact row_b16 rfl { rd := SN64 } { rd := QA64 } (fun _ => by simp only [Ops.MSUB_D]; runp_fe)
          (fun _ => by simp only [Ops.MSUB_D]; runp_fe)
      · simp only [Bool.not_eq_true] at hr
        rcases not_absorbs a fr fs ft hna hs ht hr hx with h11 | hz
        · -- (d) with the Invalid enable: the signaling NaN read traps in the multiply
          have hen := trapC_en _ h11
          simp only [OddFPR] at hr ht hs; simp only [FPRPair] at hx
          exact row_of rfl { rd := SN64 } { rd := QA64 } (fun _ => False) (fun _ => True)
            (fun _ _ hx => hx.elim) (fun _ => by simp only [Ops.MSUB_D]; runp_fe)
            (fun _ => by simp only [Ops.MSUB_D]; runp_fe)
        · -- (d) without it (and `fr` not a signaling NaN): the signaling NaN read shows in the
          -- instruction's Cause (bit 16, the union of the operations' conditions); the quiet one not
          simp only [OddFPR] at hr ht hs; simp only [FPRPair] at hx hz
          exact row_b16 rfl { rd := SN64 } { rd := QA64 } (fun _ => by simp only [Ops.MSUB_D]; runp_fe)
            (fun _ => by simp only [Ops.MSUB_D]; runp_fe)
    · -- (b) `fs` not a quiet NaN: the quiet NaN read is delivered
      simp only [OddFPR] at ht; simp only [FPRPair, Bool.not_eq_true] at hx
      have hm1 := mul_right_q (IEEE.env a) _ QA64 hx QA64_q
      have hm2 := mul_right_q (IEEE.env a) _ QB64 hx QB64_q
      exact row_of rfl { rd := QA64 } { rd := QB64 } (fun x => FPRPair x fd = QA64) (fun x => FPRPair x fd = QB64)
        (obs_pair fd _ _ QA64_ne_QB64) (fun _ => by simp only [Ops.MSUB_D]; runp_fe)
        (fun _ => by simp only [Ops.MSUB_D]; runp_fe)
  · -- (e) `fs`, `ft` even, `fr` odd, the multiply not Invalid (outside `MaddAbsorbs`): as a binary
    -- operation on the product, the instruction's Cause being the union with the multiply's
    have hr : OddFPR fr = true := by simp_all
    have hm : (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).2.invalid = false := by
      simp only [Bool.not_eq_true] at ht
      simpa [MaddAbsorbs, hs, ht, hr] using hna
    simp only [OddFPR, Bool.not_eq_true] at hr ht hs
    exact row_dist rfl fd
      ((IEEE.subD a (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).1 SN64).1,
        (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).2.or (IEEE.subD a (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).1 SN64).2)
      ((IEEE.subD a (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).1 QA64).1,
        (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).2.or (IEEE.subD a (IEEE.mulD a (FPRPair a fs) (FPRPair a ft)).1 QA64).2)
      (dist_or _ hm (dr_sub (IEEE.env a) _)) (fun _ => by simp only [Ops.MSUB_D]; runp_fe)
      (fun _ => by simp only [Ops.MSUB_D]; runp_fe)

end

end Refine
