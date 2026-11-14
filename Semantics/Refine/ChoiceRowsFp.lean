import Semantics.Refine.ChoiceRows

/-!
# Refine.ChoiceRowsFp — the FP rows of `ConsultsOracle` are real choices (wave 9)

* a double written to an odd `fd` (`StoreFPR` UNPREDICTABLE): the witness oracle signals Reserved
  Instruction;
* `ABS.fmt`/`NEG.fmt` of a quiet NaN, `NMADD.fmt`/`NMSUB.fmt` with a quiet NaN sum, and every `D`
  operation of `ABS`/`NEG`/`NMADD`/`NMSUB` reading an odd register (the witness reads the quiet NaN
  `QA64`, so the value negated is a quiet NaN): the readings `A` and `B` of `Oracle.absNegNaN` differ
  in Invalid Operation (`FCSR.Cause.V`, bit 16, or a trap);
* `ADD/SUB/MUL/DIV.D` reading an odd register: a signaling NaN and a quiet NaN read differ in the
  result or in Invalid Operation (`dist_left`, `dist_right`, `dist_both`);
* `SQRT/RECIP/RSQRT.D`, `CVT.S.D` reading an odd register: Invalid Operation for the signaling NaN
  only; `ROUND/TRUNC/CEIL/FLOOR/CVT.W.D`: `+1.0` and `+4.0` give the words 1 and 4; `MOV.D`, the
  conditional moves: the value read is the value written;
* `CVT.D.S`/`CVT.S.D` of a quiet NaN: two quiet NaNs;
* `C.cond.D` with an odd register not absorbed by the other operand: Invalid Operation for a
  signaling NaN read and not for a quiet NaN (`cond3 = 0`) or `+1.0` (`cond3 = 1`) read;
* `MADD.D`/`MSUB.D` outside `MaddAbsorbs`: the cases of `rw_maddD`.
-/

namespace Refine

open Manual

theorem lt_24_add (n : Nat) : (16 < 24 + n) = True := by simp; omega

theorem fin32_ne_succ (x : Fin 32) : (x = x + 1) = False := by
  apply propext; constructor
  · intro h; have := congrArg Fin.val h; rw [Fin.val_add] at this; omega
  · intro h; exact h.elim

theorem split64 (v : BitVec 64) : v.extractLsb' 32 32 ++ v.extractLsb' 0 32 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split <;> simp_all <;> congr 1 <;> omega

/-- The double `fd` names after the Operation (`FPRPair`), and Invalid Operation in `FCSR.Cause`. -/
def PairV (fd : W32) (r : BitVec 64 × Mips.Fp.Flags) (x : Arch) : Prop :=
  FPRPair x fd = r.1 ∧ bit x.FCSR 16 = r.2.invalid

theorem obs_pairV (fd : W32) (r₁ r₂ : BitVec 64 × Mips.Fp.Flags) (hd : Dist r₁ r₂) (x y : Arch)
    (hx : PairV fd r₁ x) (hy : PairV fd r₂ y) : Obs x ≠ Obs y := by
  intro he
  have h1 := congrArg (fun o => o.2.2.2.1) he
  have h2 := congrArg (fun o => o.2.2.2.2.1) he
  simp only [Obs] at h1 h2
  rcases hd with hd | hd
  · apply hd; rw [← hx.1, ← hy.1]; simp only [FPRPair, h1]
  · apply hd; rw [← hx.2, ← hy.2, h2]

theorem obs_bit16 (x y : Arch) (hx : bit x.FCSR 16 = true) (hy : bit y.FCSR 16 = false) : Obs x ≠ Obs y := by
  intro he; have := congrArg (fun o => o.2.2.2.2.1) he; simp only [Obs] at this; rw [this] at hx
  rw [hx] at hy; cases hy
theorem obs_pair (fd : W32) (v₁ v₂ : BitVec 64) (hv : v₁ ≠ v₂) (x y : Arch) (hx : FPRPair x fd = v₁)
    (hy : FPRPair y fd = v₂) : Obs x ≠ Obs y := by
  intro he; have := congrArg (fun o => o.2.2.2.1) he; simp only [Obs] at this
  apply hv; rw [← hx, ← hy]; simp only [FPRPair, this]
theorem obs_fpr (r : W32) (v₁ v₂ : W32) (hv : v₁ ≠ v₂) (x y : Arch) (hx : x.FPR (reg r) = v₁)
    (hy : y.FPR (reg r) = v₂) : Obs x ≠ Obs y := by
  intro he; have := congrArg (fun o => o.2.2.2.1 (reg r)) he; simp only [Obs] at this
  rw [hx, hy] at this; exact hv this

/-- `runp` closing paths that store a double to an even register. -/
macro "runp_fp" : tactic => `(tactic| (
  runp_simp
  (try simp only [addS_fpResult, subS_fpResult, addD_fpResult, subD_fpResult])
  repeat' (case_ite <;> (try runp_simp) <;> (try simp only [addS_fpResult, subS_fpResult, addD_fpResult, subD_fpResult]))
  all_goals (simp_all [CEof, bit, toBits_b4', Mips.Fp.Flags.invalidOnly, Mips.Fp.Flags.none,
    BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, PairV, FPRPair, update,
    fin32_ne_succ, split64, addS_fpResult, subS_fpResult, addD_fpResult, subD_fpResult, IEEE.sqrtD,
    sqrt_SN, sqrt_QA, sqrt_QA1, div1_SN, div1_QA, modelImpl, Mips.Fp.Flags.or, cvtSD_SN, IEEE.cvtSD,
    IEEE.cvtDS, SN64_q, QA64_q, IEEE.toWordD, toW_one, toW_four, IEEE.absD, IEEE.negD, IEEE.signOpD,
    QA64_s, IEEE.absS, IEEE.negS, IEEE.signOpS, IEEE.isSNaND, IEEE.isQNaND, One64_s, One64_q, SN64_s,
    lt_24_add])))

/-- The reading `A` and `B` of a quiet NaN differ in Invalid Operation. -/
theorem row_AB {ins : Instruction} {a : Arch} {O : Pseudo Unit} (hO : Operation ins = some O) (rd : BitVec 64)
    (h : ∀ ce r, RunP a (fun x => bit x.FCSR 16 = (r != .B))
      (O (ctxOf modelImpl (wo { rd := rd, anr := r } ce)) { arch := a })) : RowWitness ins a :=
  row_of hO { rd := rd, anr := .A } { rd := rd, anr := .B } _ _
    (fun x y hx hy => obs_bit16 x y (hx.trans (by decide)) (hy.trans (by decide))) (fun ce => h ce .A)
    (fun ce => h ce .B)

section
set_option linter.unusedSimpArgs false

theorem qnan32_not_snan (x : W32) (h : Mips.Fp.isQNaN32 x = true) : Mips.Fp.isSNaN32 x = false := by
  revert h; simp only [Mips.Fp.isQNaN32, Mips.Fp.isSNaN32, Mips.Fp.Format.isQNaN, Mips.Fp.Format.isSNaN]
  generalize Mips.Fp.binary32.isNaN _ = b; generalize Mips.Fp.binary32.fracField _ / _ = n
  cases b <;> simp; omega

theorem rw_absS (fd fs : W32) (a : Arch) (h : ConsultsOracle (.absS fd fs) a = true) : RowWitness (.absS fd fs) a := by
  simp only [ConsultsOracle] at h
  have hs := qnan32_not_snan _ h
  exact row_AB rfl QA64 fun _ r => by
    simp only [Ops.ABS_S, IEEE.absS, IEEE.signOpS, h, hs]; cases r <;> runp
theorem rw_negS (fd fs : W32) (a : Arch) (h : ConsultsOracle (.negS fd fs) a = true) : RowWitness (.negS fd fs) a := by
  simp only [ConsultsOracle] at h
  have hs := qnan32_not_snan _ h
  exact row_AB rfl QA64 fun _ r => by
    simp only [Ops.NEG_S, IEEE.negS, IEEE.signOpS, h, hs]; cases r <;> runp

end

/-! ## Binary `D` operations reading an odd register -/

theorem row_dist {ins : Instruction} {a : Arch} {O : Pseudo Unit} (hO : Operation ins = some O) (fd : W32)
    (r₁ r₂ : BitVec 64 × Mips.Fp.Flags) (hd : Dist r₁ r₂)
    (h₁ : ∀ ce, RunP a (PairV fd r₁) (O (ctxOf modelImpl (wo { rd := SN64 } ce)) { arch := a }))
    (h₂ : ∀ ce, RunP a (PairV fd r₂) (O (ctxOf modelImpl (wo { rd := QA64 } ce)) { arch := a })) :
    RowWitness ins a :=
  row_of hO _ _ _ _ (obs_pairV fd r₁ r₂ hd) h₁ h₂

theorem dl_add (e : Mips.Fp.Env) (y : BitVec 64) : Dist (Mips.Fp.f64Add e SN64 y) (Mips.Fp.f64Add e QA64 y) := by
  rw [add_nan _ _ _ (by simp [SN64_n]), add_nan _ _ _ (by simp [QA64_n])]; exact dist_left y
theorem dr_add (e : Mips.Fp.Env) (x : BitVec 64) : Dist (Mips.Fp.f64Add e x SN64) (Mips.Fp.f64Add e x QA64) := by
  rw [add_nan _ _ _ (by simp [SN64_n]), add_nan _ _ _ (by simp [QA64_n])]; exact dist_right x
theorem db_add (e : Mips.Fp.Env) : Dist (Mips.Fp.f64Add e SN64 SN64) (Mips.Fp.f64Add e QA64 QA64) := by
  rw [add_nan _ _ _ (by simp [SN64_n]), add_nan _ _ _ (by simp [QA64_n])]; exact dist_both

theorem dl_sub (e : Mips.Fp.Env) (y : BitVec 64) : Dist (Mips.Fp.f64Sub e SN64 y) (Mips.Fp.f64Sub e QA64 y) := by
  rw [sub_nan _ _ _ (by simp [SN64_n]), sub_nan _ _ _ (by simp [QA64_n])]; exact dist_left y
theorem dr_sub (e : Mips.Fp.Env) (x : BitVec 64) : Dist (Mips.Fp.f64Sub e x SN64) (Mips.Fp.f64Sub e x QA64) := by
  rw [sub_nan _ _ _ (by simp [SN64_n]), sub_nan _ _ _ (by simp [QA64_n])]; exact dist_right x
theorem db_sub (e : Mips.Fp.Env) : Dist (Mips.Fp.f64Sub e SN64 SN64) (Mips.Fp.f64Sub e QA64 QA64) := by
  rw [sub_nan _ _ _ (by simp [SN64_n]), sub_nan _ _ _ (by simp [QA64_n])]; exact dist_both

theorem dl_mul (e : Mips.Fp.Env) (y : BitVec 64) : Dist (Mips.Fp.f64Mul e SN64 y) (Mips.Fp.f64Mul e QA64 y) := by
  rw [mul_nan _ _ _ (by simp [SN64_n]), mul_nan _ _ _ (by simp [QA64_n])]; exact dist_left y
theorem dr_mul (e : Mips.Fp.Env) (x : BitVec 64) : Dist (Mips.Fp.f64Mul e x SN64) (Mips.Fp.f64Mul e x QA64) := by
  rw [mul_nan _ _ _ (by simp [SN64_n]), mul_nan _ _ _ (by simp [QA64_n])]; exact dist_right x
theorem db_mul (e : Mips.Fp.Env) : Dist (Mips.Fp.f64Mul e SN64 SN64) (Mips.Fp.f64Mul e QA64 QA64) := by
  rw [mul_nan _ _ _ (by simp [SN64_n]), mul_nan _ _ _ (by simp [QA64_n])]; exact dist_both

theorem dl_div (e : Mips.Fp.Env) (y : BitVec 64) : Dist (Mips.Fp.f64Div e SN64 y) (Mips.Fp.f64Div e QA64 y) := by
  rw [div_nan _ _ _ (by simp [SN64_n]), div_nan _ _ _ (by simp [QA64_n])]; exact dist_left y
theorem dr_div (e : Mips.Fp.Env) (x : BitVec 64) : Dist (Mips.Fp.f64Div e x SN64) (Mips.Fp.f64Div e x QA64) := by
  rw [div_nan _ _ _ (by simp [SN64_n]), div_nan _ _ _ (by simp [QA64_n])]; exact dist_right x
theorem db_div (e : Mips.Fp.Env) : Dist (Mips.Fp.f64Div e SN64 SN64) (Mips.Fp.f64Div e QA64 QA64) := by
  rw [div_nan _ _ _ (by simp [SN64_n]), div_nan _ _ _ (by simp [QA64_n])]; exact dist_both

section
set_option linter.unusedSimpArgs false

theorem rw_addD (fd fs ft : W32) (a : Arch) (h : ConsultsOracle (.addD fd fs ft) a = true) :
    RowWitness (.addD fd fs ft) a := by
  simp only [ConsultsOracle, Bool.or_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.ADD_D]; runp
  have h' : OddFPR fs = true ∨ OddFPR ft = true := h.elim id (fun h => absurd h hd)
  simp only [OddFPR, Bool.not_eq_true] at hd h'
  by_cases hs : bit (BitVec.ofNat 5 (reg fs).val) 0 = true <;> by_cases ht : bit (BitVec.ofNat 5 (reg ft).val) 0 = true
  · exact row_dist rfl fd (IEEE.addD a SN64 SN64) (IEEE.addD a QA64 QA64) (db_add (IEEE.env a)) (fun _ => by simp only [Ops.ADD_D]; runp_fp) (fun _ => by simp only [Ops.ADD_D]; runp_fp)
  · simp only [Bool.not_eq_true] at ht
    exact row_dist rfl fd (IEEE.addD a SN64 (FPRPair a ft)) (IEEE.addD a QA64 (FPRPair a ft))
      (dl_add (IEEE.env a) (FPRPair a ft)) (fun _ => by simp only [Ops.ADD_D]; runp_fp)
      (fun _ => by simp only [Ops.ADD_D]; runp_fp)
  · simp only [Bool.not_eq_true] at hs
    exact row_dist rfl fd (IEEE.addD a (FPRPair a fs) SN64) (IEEE.addD a (FPRPair a fs) QA64)
      (dr_add (IEEE.env a) (FPRPair a fs)) (fun _ => by simp only [Ops.ADD_D]; runp_fp)
      (fun _ => by simp only [Ops.ADD_D]; runp_fp)
  · simp_all

theorem rw_subD (fd fs ft : W32) (a : Arch) (h : ConsultsOracle (.subD fd fs ft) a = true) :
    RowWitness (.subD fd fs ft) a := by
  simp only [ConsultsOracle, Bool.or_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.SUB_D]; runp
  have h' : OddFPR fs = true ∨ OddFPR ft = true := h.elim id (fun h => absurd h hd)
  simp only [OddFPR, Bool.not_eq_true] at hd h'
  by_cases hs : bit (BitVec.ofNat 5 (reg fs).val) 0 = true <;> by_cases ht : bit (BitVec.ofNat 5 (reg ft).val) 0 = true
  · exact row_dist rfl fd (IEEE.subD a SN64 SN64) (IEEE.subD a QA64 QA64) (db_sub (IEEE.env a)) (fun _ => by simp only [Ops.SUB_D]; runp_fp) (fun _ => by simp only [Ops.SUB_D]; runp_fp)
  · simp only [Bool.not_eq_true] at ht
    exact row_dist rfl fd (IEEE.subD a SN64 (FPRPair a ft)) (IEEE.subD a QA64 (FPRPair a ft))
      (dl_sub (IEEE.env a) (FPRPair a ft)) (fun _ => by simp only [Ops.SUB_D]; runp_fp)
      (fun _ => by simp only [Ops.SUB_D]; runp_fp)
  · simp only [Bool.not_eq_true] at hs
    exact row_dist rfl fd (IEEE.subD a (FPRPair a fs) SN64) (IEEE.subD a (FPRPair a fs) QA64)
      (dr_sub (IEEE.env a) (FPRPair a fs)) (fun _ => by simp only [Ops.SUB_D]; runp_fp)
      (fun _ => by simp only [Ops.SUB_D]; runp_fp)
  · simp_all

theorem rw_mulD (fd fs ft : W32) (a : Arch) (h : ConsultsOracle (.mulD fd fs ft) a = true) :
    RowWitness (.mulD fd fs ft) a := by
  simp only [ConsultsOracle, Bool.or_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.MUL_D]; runp
  have h' : OddFPR fs = true ∨ OddFPR ft = true := h.elim id (fun h => absurd h hd)
  simp only [OddFPR, Bool.not_eq_true] at hd h'
  by_cases hs : bit (BitVec.ofNat 5 (reg fs).val) 0 = true <;> by_cases ht : bit (BitVec.ofNat 5 (reg ft).val) 0 = true
  · exact row_dist rfl fd (IEEE.mulD a SN64 SN64) (IEEE.mulD a QA64 QA64) (db_mul (IEEE.env a)) (fun _ => by simp only [Ops.MUL_D]; runp_fp) (fun _ => by simp only [Ops.MUL_D]; runp_fp)
  · simp only [Bool.not_eq_true] at ht
    exact row_dist rfl fd (IEEE.mulD a SN64 (FPRPair a ft)) (IEEE.mulD a QA64 (FPRPair a ft))
      (dl_mul (IEEE.env a) (FPRPair a ft)) (fun _ => by simp only [Ops.MUL_D]; runp_fp)
      (fun _ => by simp only [Ops.MUL_D]; runp_fp)
  · simp only [Bool.not_eq_true] at hs
    exact row_dist rfl fd (IEEE.mulD a (FPRPair a fs) SN64) (IEEE.mulD a (FPRPair a fs) QA64)
      (dr_mul (IEEE.env a) (FPRPair a fs)) (fun _ => by simp only [Ops.MUL_D]; runp_fp)
      (fun _ => by simp only [Ops.MUL_D]; runp_fp)
  · simp_all

theorem rw_divD (fd fs ft : W32) (a : Arch) (h : ConsultsOracle (.divD fd fs ft) a = true) :
    RowWitness (.divD fd fs ft) a := by
  simp only [ConsultsOracle, Bool.or_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.DIV_D]; runp
  have h' : OddFPR fs = true ∨ OddFPR ft = true := h.elim id (fun h => absurd h hd)
  simp only [OddFPR, Bool.not_eq_true] at hd h'
  by_cases hs : bit (BitVec.ofNat 5 (reg fs).val) 0 = true <;> by_cases ht : bit (BitVec.ofNat 5 (reg ft).val) 0 = true
  · exact row_dist rfl fd (IEEE.divD a SN64 SN64) (IEEE.divD a QA64 QA64) (db_div (IEEE.env a)) (fun _ => by simp only [Ops.DIV_D]; runp_fp) (fun _ => by simp only [Ops.DIV_D]; runp_fp)
  · simp only [Bool.not_eq_true] at ht
    exact row_dist rfl fd (IEEE.divD a SN64 (FPRPair a ft)) (IEEE.divD a QA64 (FPRPair a ft))
      (dl_div (IEEE.env a) (FPRPair a ft)) (fun _ => by simp only [Ops.DIV_D]; runp_fp)
      (fun _ => by simp only [Ops.DIV_D]; runp_fp)
  · simp only [Bool.not_eq_true] at hs
    exact row_dist rfl fd (IEEE.divD a (FPRPair a fs) SN64) (IEEE.divD a (FPRPair a fs) QA64)
      (dr_div (IEEE.env a) (FPRPair a fs)) (fun _ => by simp only [Ops.DIV_D]; runp_fp)
      (fun _ => by simp only [Ops.DIV_D]; runp_fp)
  · simp_all

end

/-! ## Unary `D` operations, conversions, moves -/

theorem row_b16 {ins : Instruction} {a : Arch} {O : Pseudo Unit} (hO : Operation ins = some O) (p₁ p₂ : WP)
    (h₁ : ∀ ce, RunP a (fun x => bit x.FCSR 16 = true) (O (ctxOf modelImpl (wo p₁ ce)) { arch := a }))
    (h₂ : ∀ ce, RunP a (fun x => bit x.FCSR 16 = false) (O (ctxOf modelImpl (wo p₂ ce)) { arch := a })) :
    RowWitness ins a :=
  row_of hO p₁ p₂ _ _ obs_bit16 h₁ h₂

section
set_option linter.unusedSimpArgs false

theorem rw_sqrtD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.sqrtD fd fs) a = true) :
    RowWitness (.sqrtD fd fs) a := by
  simp only [ConsultsOracle, Bool.or_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.SQRT_D]; runp
  have hs : OddFPR fs = true := h.elim id (fun h => absurd h hd)
  simp only [OddFPR, Bool.not_eq_true] at hd hs
  exact row_b16 rfl { rd := SN64 } { rd := QA64 } (fun _ => by simp only [Ops.SQRT_D]; runp_fp)
    (fun _ => by simp only [Ops.SQRT_D]; runp_fp)

theorem rw_recipD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.recipD fd fs) a = true) :
    RowWitness (.recipD fd fs) a := by
  simp only [ConsultsOracle, Bool.or_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.RECIP_D]; runp
  have hs : OddFPR fs = true := h.elim id (fun h => absurd h hd)
  simp only [OddFPR, Bool.not_eq_true] at hd hs
  exact row_b16 rfl { rd := SN64 } { rd := QA64 } (fun _ => by simp only [Ops.RECIP_D]; runp_fp)
    (fun _ => by simp only [Ops.RECIP_D]; runp_fp)

theorem rw_rsqrtD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.rsqrtD fd fs) a = true) :
    RowWitness (.rsqrtD fd fs) a := by
  simp only [ConsultsOracle, Bool.or_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.RSQRT_D]; runp
  have hs : OddFPR fs = true := h.elim id (fun h => absurd h hd)
  simp only [OddFPR, Bool.not_eq_true] at hd hs
  exact row_b16 rfl { rd := SN64 } { rd := QA64 } (fun _ => by simp only [Ops.RSQRT_D]; runp_fp)
    (fun _ => by simp only [Ops.RSQRT_D]; runp_fp)

theorem rw_movD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.movD fd fs) a = true) :
    RowWitness (.movD fd fs) a := by
  simp only [ConsultsOracle, Bool.or_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.MOV_D]; runp
  have hs : OddFPR fs = true := h.elim id (fun h => absurd h hd)
  simp only [OddFPR, Bool.not_eq_true] at hd hs
  exact row_of rfl { rd := QA64 } { rd := QB64 } (fun x => FPRPair x fd = QA64) (fun x => FPRPair x fd = QB64)
    (obs_pair fd _ _ QA64_ne_QB64) (fun _ => by simp only [Ops.MOV_D]; runp_fp)
    (fun _ => by simp only [Ops.MOV_D]; runp_fp)

theorem rw_roundWD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.roundWD fd fs) a = true) :
    RowWitness (.roundWD fd fs) a := by
  simp only [ConsultsOracle, OddFPR] at h
  exact row_of rfl { rd := One64 } { rd := Four64 } (fun x => x.FPR (reg fd) = 1#32) (fun x => x.FPR (reg fd) = 4#32)
    (obs_fpr fd _ _ (by decide)) (fun _ => by simp only [Ops.ROUND_W_D]; runp_fp)
    (fun _ => by simp only [Ops.ROUND_W_D]; runp_fp)

theorem rw_truncWD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.truncWD fd fs) a = true) :
    RowWitness (.truncWD fd fs) a := by
  simp only [ConsultsOracle, OddFPR] at h
  exact row_of rfl { rd := One64 } { rd := Four64 } (fun x => x.FPR (reg fd) = 1#32) (fun x => x.FPR (reg fd) = 4#32)
    (obs_fpr fd _ _ (by decide)) (fun _ => by simp only [Ops.TRUNC_W_D]; runp_fp)
    (fun _ => by simp only [Ops.TRUNC_W_D]; runp_fp)

theorem rw_ceilWD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.ceilWD fd fs) a = true) :
    RowWitness (.ceilWD fd fs) a := by
  simp only [ConsultsOracle, OddFPR] at h
  exact row_of rfl { rd := One64 } { rd := Four64 } (fun x => x.FPR (reg fd) = 1#32) (fun x => x.FPR (reg fd) = 4#32)
    (obs_fpr fd _ _ (by decide)) (fun _ => by simp only [Ops.CEIL_W_D]; runp_fp)
    (fun _ => by simp only [Ops.CEIL_W_D]; runp_fp)

theorem rw_floorWD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.floorWD fd fs) a = true) :
    RowWitness (.floorWD fd fs) a := by
  simp only [ConsultsOracle, OddFPR] at h
  exact row_of rfl { rd := One64 } { rd := Four64 } (fun x => x.FPR (reg fd) = 1#32) (fun x => x.FPR (reg fd) = 4#32)
    (obs_fpr fd _ _ (by decide)) (fun _ => by simp only [Ops.FLOOR_W_D]; runp_fp)
    (fun _ => by simp only [Ops.FLOOR_W_D]; runp_fp)

theorem rw_cvtWD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.cvtWD fd fs) a = true) :
    RowWitness (.cvtWD fd fs) a := by
  simp only [ConsultsOracle, OddFPR] at h
  exact row_of rfl { rd := One64 } { rd := Four64 } (fun x => x.FPR (reg fd) = 1#32) (fun x => x.FPR (reg fd) = 4#32)
    (obs_fpr fd _ _ (by decide)) (fun _ => by simp only [Ops.CVT_W_D]; runp_fp)
    (fun _ => by simp only [Ops.CVT_W_D]; runp_fp)

theorem rw_cvtSD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.cvtSD fd fs) a = true) :
    RowWitness (.cvtSD fd fs) a := by
  simp only [ConsultsOracle, Bool.or_eq_true] at h
  by_cases ho : OddFPR fs = true
  · simp only [OddFPR] at ho
    exact row_b16 rfl { rd := SN64 } { rd := QA64 } (fun _ => by simp only [Ops.CVT_S_D]; runp_fp)
      (fun _ => by simp only [Ops.CVT_S_D]; runp_fp)
  · have hq := h.resolve_left ho
    simp only [OddFPR, Bool.not_eq_true] at ho
    simp only [FPRPair] at hq
    have hs := qnan64_not_snan _ hq
    exact row_of rfl { qs := true } { qs := false } (fun x => x.FPR (reg fd) = QA32) (fun x => x.FPR (reg fd) = QB32)
      (obs_fpr fd _ _ QA32_ne_QB32) (fun _ => by simp only [Ops.CVT_S_D]; runp_fp)
      (fun _ => by simp only [Ops.CVT_S_D]; runp_fp)

theorem rw_cvtDS (fd fs : W32) (a : Arch) (h : ConsultsOracle (.cvtDS fd fs) a = true) :
    RowWitness (.cvtDS fd fs) a := by
  simp only [ConsultsOracle, Bool.or_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.CVT_D_S]; runp
  have hq := h.resolve_left hd
  simp only [OddFPR, Bool.not_eq_true] at hd
  exact row_of rfl { qd := true } { qd := false } (fun x => FPRPair x fd = QA64) (fun x => FPRPair x fd = QB64)
    (obs_pair fd _ _ QA64_ne_QB64) (fun _ => by simp only [Ops.CVT_D_S]; runp_fp)
    (fun _ => by simp only [Ops.CVT_D_S]; runp_fp)

theorem rw_cvtDW (fd fs : W32) (a : Arch) (h : ConsultsOracle (.cvtDW fd fs) a = true) :
    RowWitness (.cvtDW fd fs) a := by
  simp only [ConsultsOracle, OddFPR] at h
  exact row_sig rfl fun _ => by simp only [Ops.CVT_D_W]; runp

theorem rw_movfD (fd fs cc : W32) (a : Arch) (h : ConsultsOracle (.movfD fd fs cc) a = true) :
    RowWitness (.movfD fd fs cc) a := by
  simp only [ConsultsOracle, Bool.or_eq_true, Bool.and_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.MOVF_D]; runp
  obtain ⟨hc, hs⟩ := h.resolve_left hd
  simp only [OddFPR, Bool.not_eq_true, FPCC] at hd hs hc
  exact row_of rfl { rd := QA64 } { rd := QB64 } (fun x => FPRPair x fd = QA64) (fun x => FPRPair x fd = QB64)
    (obs_pair fd _ _ QA64_ne_QB64) (fun _ => by simp only [Ops.MOVF_D]; runp_fp)
    (fun _ => by simp only [Ops.MOVF_D]; runp_fp)

theorem rw_movtD (fd fs cc : W32) (a : Arch) (h : ConsultsOracle (.movtD fd fs cc) a = true) :
    RowWitness (.movtD fd fs cc) a := by
  simp only [ConsultsOracle, Bool.or_eq_true, Bool.and_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.MOVT_D]; runp
  obtain ⟨hc, hs⟩ := h.resolve_left hd
  simp only [OddFPR, Bool.not_eq_true, FPCC] at hd hs hc
  exact row_of rfl { rd := QA64 } { rd := QB64 } (fun x => FPRPair x fd = QA64) (fun x => FPRPair x fd = QB64)
    (obs_pair fd _ _ QA64_ne_QB64) (fun _ => by simp only [Ops.MOVT_D]; runp_fp)
    (fun _ => by simp only [Ops.MOVT_D]; runp_fp)

theorem rw_movnD (fd fs rt : W32) (a : Arch) (h : ConsultsOracle (.movnD fd fs rt) a = true) :
    RowWitness (.movnD fd fs rt) a := by
  simp only [ConsultsOracle, Bool.or_eq_true, Bool.and_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.MOVN_D]; runp
  obtain ⟨hc, hs⟩ := h.resolve_left hd
  simp only [OddFPR, Bool.not_eq_true, FPCC] at hd hs hc
  exact row_of rfl { rd := QA64 } { rd := QB64 } (fun x => FPRPair x fd = QA64) (fun x => FPRPair x fd = QB64)
    (obs_pair fd _ _ QA64_ne_QB64) (fun _ => by simp only [Ops.MOVN_D]; runp_fp)
    (fun _ => by simp only [Ops.MOVN_D]; runp_fp)

theorem rw_movzD (fd fs rt : W32) (a : Arch) (h : ConsultsOracle (.movzD fd fs rt) a = true) :
    RowWitness (.movzD fd fs rt) a := by
  simp only [ConsultsOracle, Bool.or_eq_true, Bool.and_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.MOVZ_D]; runp
  obtain ⟨hc, hs⟩ := h.resolve_left hd
  simp only [OddFPR, Bool.not_eq_true, FPCC] at hd hs hc
  exact row_of rfl { rd := QA64 } { rd := QB64 } (fun x => FPRPair x fd = QA64) (fun x => FPRPair x fd = QB64)
    (obs_pair fd _ _ QA64_ne_QB64) (fun _ => by simp only [Ops.MOVZ_D]; runp_fp)
    (fun _ => by simp only [Ops.MOVZ_D]; runp_fp)

theorem rw_absD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.absD fd fs) a = true) : RowWitness (.absD fd fs) a := by
  simp only [ConsultsOracle, Bool.or_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.ABS_D]; runp
  simp only [OddFPR, Bool.not_eq_true] at hd
  by_cases ho : OddFPR fs = true
  · simp only [OddFPR] at ho
    exact row_AB rfl QA64 fun _ r => by simp only [Ops.ABS_D]; cases r <;> runp_fp
  · have hq : Mips.Fp.isQNaN64 (FPRPair a fs) = true := by simp only [OddFPR] at h ho; simp_all
    simp only [OddFPR, Bool.not_eq_true] at ho; simp only [FPRPair] at hq
    have hs := qnan64_not_snan _ hq
    exact row_AB rfl QA64 fun _ r => by simp only [Ops.ABS_D]; cases r <;> runp_fp
theorem rw_negD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.negD fd fs) a = true) : RowWitness (.negD fd fs) a := by
  simp only [ConsultsOracle, Bool.or_eq_true] at h
  by_cases hd : OddFPR fd = true
  · simp only [OddFPR] at hd; exact row_sig rfl fun _ => by simp only [Ops.NEG_D]; runp
  simp only [OddFPR, Bool.not_eq_true] at hd
  by_cases ho : OddFPR fs = true
  · simp only [OddFPR] at ho
    exact row_AB rfl QA64 fun _ r => by simp only [Ops.NEG_D]; cases r <;> runp_fp
  · have hq : Mips.Fp.isQNaN64 (FPRPair a fs) = true := by simp only [OddFPR] at h ho; simp_all
    simp only [OddFPR, Bool.not_eq_true] at ho; simp only [FPRPair] at hq
    have hs := qnan64_not_snan _ hq
    exact row_AB rfl QA64 fun _ r => by simp only [Ops.NEG_D]; cases r <;> runp_fp

theorem rw_nmaddS (fd fr fs ft : W32) (a : Arch) (h : ConsultsOracle (.nmaddS fd fr fs ft) a = true) :
    RowWitness (.nmaddS fd fr fs ft) a := by
  simp only [ConsultsOracle] at h
  have hs := qnan32_not_snan _ h
  exact row_AB rfl QA64 fun _ r => by simp only [Ops.NMADD_S]; cases r <;> runp_fp
theorem rw_nmsubS (fd fr fs ft : W32) (a : Arch) (h : ConsultsOracle (.nmsubS fd fr fs ft) a = true) :
    RowWitness (.nmsubS fd fr fs ft) a := by
  simp only [ConsultsOracle] at h
  have hs := qnan32_not_snan _ h
  exact row_AB rfl QA64 fun _ r => by simp only [Ops.NMSUB_S]; cases r <;> runp_fp

end

end Refine
