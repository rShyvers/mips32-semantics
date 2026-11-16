import Semantics.Refine.ChoiceRows

/-!
# Refine.ChoiceRowsFp — the FP rows of `ConsultsOracle` are real choices (wave 9; R6-5)

* every Operation that stores a 32-bit result into a 64-bit FPR (`StoreFPR(fpr, S/W, ...)`): the upper
  half of the FPR is UNPREDICTABLE (MD00082 Vol I-A Rev 6.01 §6.6.2, p.98; `Oracle.fprUpper`); the
  witness oracles give the upper halves 0 and 1 (`row_upper`);
* `CVT.D.S` of a quiet NaN: two quiet NaNs (`Oracle.cvtQNaNToD`).

(R6-5: the 64-bit FPU of Release 6 removed the odd-register rows of the 32-bit FPU, and
`FCSR.ABS2008 = 1` the `ABS`/`NEG` QNaN reading; the former rows `ADD/SUB/MUL/DIV/SQRT/RECIP/RSQRT/
MOV/ABS/NEG.D`, `CVT.D.W` are no rows any more, their `rw_<ctor>` is the contradiction of the
hypothesis. The helpers of the removed rows — `PairV`, `obs_pairV`, `obs_pair`, `row_AB`, `row_AA'S`,
`row_AA'D`, `row_dist`, `row_b16`, `dl_*`/`dr_*`/`db_*` — were removed with them. Release 6 also removed
the rows of `NMADD`/`NMSUB`, `C.cond.D`, `MADD.D`/`MSUB.D` and the FP conditional moves.)
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

theorem obs_bit16 (x y : Arch) (hx : bit x.FCSR 16 = true) (hy : bit y.FCSR 16 = false) : Obs x ≠ Obs y := by
  intro he; have := congrArg (fun o => o.2.2.2.1) he; simp only [Obs] at this; rw [this] at hx
  rw [hx] at hy; cases hy

/-- Two states with different values in `FPR[r]` differ in `Obs`. -/
theorem obs_fpr (r : W32) (v₁ v₂ : BitVec 64) (hv : v₁ ≠ v₂) (x y : Arch) (hx : x.FPR (reg r) = v₁)
    (hy : y.FPR (reg r) = v₂) : Obs x ≠ Obs y := by
  intro he; have := congrArg (fun o => o.2.2.1 (reg r)) he; simp only [Obs] at this
  rw [hx, hy] at this; exact hv this

/-- Two states with different upper halves of `FPR[r]` differ in `Obs`. -/
theorem obs_upper (r : W32) (x y : Arch) (hx : (x.FPR (reg r)).extractLsb' 32 32 = 0#32)
    (hy : (y.FPR (reg r)).extractLsb' 32 32 = 1#32) : Obs x ≠ Obs y := by
  intro he; have := congrArg (fun o => o.2.2.1 (reg r)) he; simp only [Obs] at this
  rw [this, hy] at hx; cases hx

/-- **A row of a 32-bit FPR result**: the witness oracles' upper halves 0 and 1 reach `FPR[fd]`. -/
theorem row_upper {ins : Instruction} {a : Arch} {O : Pseudo Unit} (hO : Operation ins = some O) (fd : W32)
    (h : ∀ ce up, RunP a (fun x => (x.FPR (reg fd)).extractLsb' 32 32 = up)
      (O (ctxOf modelImpl (wo { up := up } ce)) { arch := a })) : RowWitness ins a :=
  row_of hO { up := 0#32 } { up := 1#32 } _ _ (obs_upper fd) (fun ce => h ce 0#32) (fun ce => h ce 1#32)

theorem update_hi (f : Fin 32 → BitVec 64) (r : Fin 32) (u v : W32) :
    ((update f r (u ++ v)) r).extractLsb' 32 32 = u := by
  simp only [update, ite_true]; exact BitVec.extractLsb'_append_eq_left

/-- `runp` for the rows of a 32-bit FPR result. -/
macro "runp_up" : tactic => `(tactic| (
  runp_simp
  repeat' (case_ite <;> (try runp_simp))
  all_goals (simp_all [CEof, bit, update_hi, update, hi_append, Mips.Fp.Flags.invalidOnly, Mips.Fp.Flags.none])))

theorem qnan32_not_snan (x : W32) (h : Mips.Fp.isQNaN32 x = true) : Mips.Fp.isSNaN32 x = false := by
  revert h; simp only [Mips.Fp.isQNaN32, Mips.Fp.isSNaN32, Mips.Fp.Format.isQNaN, Mips.Fp.Format.isSNaN]
  generalize Mips.Fp.binary32.isNaN _ = b; generalize Mips.Fp.binary32.fracField _ / _ = n
  cases b <;> simp; omega

section
set_option linter.unusedSimpArgs false

/-! ## The 32-bit FPR results (`fprUpper`) -/

theorem rw_lwc1 (base ft off : W32) (a : Arch) (_h : ConsultsOracle (.lwc1 base ft off) a = true) :
    RowWitness (.lwc1 base ft off) a :=
  row_upper rfl ft fun _ _ => by simp only [Ops.LWC1]; runp_up
theorem rw_mtc1 (rt fs : W32) (a : Arch) (_h : ConsultsOracle (.mtc1 rt fs) a = true) :
    RowWitness (.mtc1 rt fs) a :=
  row_upper rfl fs fun _ _ => by simp only [Ops.MTC1]; runp_up
theorem rw_movS (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.movS fd fs) a = true) :
    RowWitness (.movS fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.MOV_S]; runp_up
theorem rw_absS (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.absS fd fs) a = true) :
    RowWitness (.absS fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.ABS_S]; runp_up
theorem rw_negS (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.negS fd fs) a = true) :
    RowWitness (.negS fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.NEG_S]; runp_up
theorem rw_addS (fd fs ft : W32) (a : Arch) (_h : ConsultsOracle (.addS fd fs ft) a = true) :
    RowWitness (.addS fd fs ft) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.ADD_S]; runp_up
theorem rw_subS (fd fs ft : W32) (a : Arch) (_h : ConsultsOracle (.subS fd fs ft) a = true) :
    RowWitness (.subS fd fs ft) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.SUB_S]; runp_up
theorem rw_mulS (fd fs ft : W32) (a : Arch) (_h : ConsultsOracle (.mulS fd fs ft) a = true) :
    RowWitness (.mulS fd fs ft) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.MUL_S]; runp_up
theorem rw_divS (fd fs ft : W32) (a : Arch) (_h : ConsultsOracle (.divS fd fs ft) a = true) :
    RowWitness (.divS fd fs ft) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.DIV_S]; runp_up
theorem rw_sqrtS (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.sqrtS fd fs) a = true) :
    RowWitness (.sqrtS fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.SQRT_S]; runp_up
theorem rw_recipS (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.recipS fd fs) a = true) :
    RowWitness (.recipS fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.RECIP_S]; runp_up
theorem rw_rsqrtS (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.rsqrtS fd fs) a = true) :
    RowWitness (.rsqrtS fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.RSQRT_S]; runp_up
theorem rw_roundWS (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.roundWS fd fs) a = true) :
    RowWitness (.roundWS fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.ROUND_W_S]; runp_up
theorem rw_truncWS (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.truncWS fd fs) a = true) :
    RowWitness (.truncWS fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.TRUNC_W_S]; runp_up
theorem rw_ceilWS (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.ceilWS fd fs) a = true) :
    RowWitness (.ceilWS fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.CEIL_W_S]; runp_up
theorem rw_floorWS (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.floorWS fd fs) a = true) :
    RowWitness (.floorWS fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.FLOOR_W_S]; runp_up
theorem rw_cvtWS (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.cvtWS fd fs) a = true) :
    RowWitness (.cvtWS fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.CVT_W_S]; runp_up
theorem rw_roundWD (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.roundWD fd fs) a = true) :
    RowWitness (.roundWD fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.ROUND_W_D]; runp_up
theorem rw_truncWD (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.truncWD fd fs) a = true) :
    RowWitness (.truncWD fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.TRUNC_W_D]; runp_up
theorem rw_ceilWD (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.ceilWD fd fs) a = true) :
    RowWitness (.ceilWD fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.CEIL_W_D]; runp_up
theorem rw_floorWD (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.floorWD fd fs) a = true) :
    RowWitness (.floorWD fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.FLOOR_W_D]; runp_up
theorem rw_cvtWD (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.cvtWD fd fs) a = true) :
    RowWitness (.cvtWD fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.CVT_W_D]; runp_up
theorem rw_cvtSD (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.cvtSD fd fs) a = true) :
    RowWitness (.cvtSD fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.CVT_S_D]; runp_up
theorem rw_cvtSW (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.cvtSW fd fs) a = true) :
    RowWitness (.cvtSW fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.CVT_S_W]; runp_up
theorem rw_cvtSL (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.cvtSL fd fs) a = true) :
    RowWitness (.cvtSL fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.CVT_S_L]; runp_up
-- The 32-bit results of the Release 6 FP instructions
theorem rw_cmpS (cond fd fs ft : W32) (a : Arch) (_h : ConsultsOracle (.cmpS cond fd fs ft) a = true) :
    RowWitness (.cmpS cond fd fs ft) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.CMP_S]; runp_up
theorem rw_selS (fd fs ft : W32) (a : Arch) (_h : ConsultsOracle (.selS fd fs ft) a = true) :
    RowWitness (.selS fd fs ft) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.SEL_S]; runp_up
theorem rw_seleqzS (fd fs ft : W32) (a : Arch) (_h : ConsultsOracle (.seleqzS fd fs ft) a = true) :
    RowWitness (.seleqzS fd fs ft) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.SELEQZ_S]; runp_up
theorem rw_selnezS (fd fs ft : W32) (a : Arch) (_h : ConsultsOracle (.selnezS fd fs ft) a = true) :
    RowWitness (.selnezS fd fs ft) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.SELNEZ_S]; runp_up
theorem rw_maddfS (fd fs ft : W32) (a : Arch) (_h : ConsultsOracle (.maddfS fd fs ft) a = true) :
    RowWitness (.maddfS fd fs ft) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.MADDF_S]; runp_up
theorem rw_msubfS (fd fs ft : W32) (a : Arch) (_h : ConsultsOracle (.msubfS fd fs ft) a = true) :
    RowWitness (.msubfS fd fs ft) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.MADDF_S]; runp_up
theorem rw_maxS (fd fs ft : W32) (a : Arch) (_h : ConsultsOracle (.maxS fd fs ft) a = true) :
    RowWitness (.maxS fd fs ft) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.MINMAX_S]; runp_up
theorem rw_minS (fd fs ft : W32) (a : Arch) (_h : ConsultsOracle (.minS fd fs ft) a = true) :
    RowWitness (.minS fd fs ft) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.MINMAX_S]; runp_up
theorem rw_maxaS (fd fs ft : W32) (a : Arch) (_h : ConsultsOracle (.maxaS fd fs ft) a = true) :
    RowWitness (.maxaS fd fs ft) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.MINMAX_S]; runp_up
theorem rw_minaS (fd fs ft : W32) (a : Arch) (_h : ConsultsOracle (.minaS fd fs ft) a = true) :
    RowWitness (.minaS fd fs ft) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.MINMAX_S]; runp_up
theorem rw_classS (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.classS fd fs) a = true) :
    RowWitness (.classS fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.CLASS_S]; runp_up
theorem rw_rintS (fd fs : W32) (a : Arch) (_h : ConsultsOracle (.rintS fd fs) a = true) :
    RowWitness (.rintS fd fs) a :=
  row_upper rfl fd fun _ _ => by simp only [Ops.RINT_S]; runp_up

/-! ## `CVT.D.S` of a quiet NaN -/

theorem rw_cvtDS (fd fs : W32) (a : Arch) (h : ConsultsOracle (.cvtDS fd fs) a = true) :
    RowWitness (.cvtDS fd fs) a := by
  simp only [ConsultsOracle] at h
  exact row_of rfl { qd := true } { qd := false } (fun x => x.FPR (reg fd) = QA64) (fun x => x.FPR (reg fd) = QB64)
    (obs_fpr fd _ _ QA64_ne_QB64) (fun _ => by simp only [Ops.CVT_D_S, IEEE.cvtDS]; runp_up)
    (fun _ => by simp only [Ops.CVT_D_S, IEEE.cvtDS]; runp_up)

/-! ## The former rows of the 32-bit FPU (no row since R6-5) -/

theorem rw_addD (fd fs ft : W32) (a : Arch) (h : ConsultsOracle (.addD fd fs ft) a = true) :
    RowWitness (.addD fd fs ft) a := by
  simp [ConsultsOracle] at h
theorem rw_subD (fd fs ft : W32) (a : Arch) (h : ConsultsOracle (.subD fd fs ft) a = true) :
    RowWitness (.subD fd fs ft) a := by
  simp [ConsultsOracle] at h
theorem rw_mulD (fd fs ft : W32) (a : Arch) (h : ConsultsOracle (.mulD fd fs ft) a = true) :
    RowWitness (.mulD fd fs ft) a := by
  simp [ConsultsOracle] at h
theorem rw_divD (fd fs ft : W32) (a : Arch) (h : ConsultsOracle (.divD fd fs ft) a = true) :
    RowWitness (.divD fd fs ft) a := by
  simp [ConsultsOracle] at h
theorem rw_sqrtD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.sqrtD fd fs) a = true) :
    RowWitness (.sqrtD fd fs) a := by
  simp [ConsultsOracle] at h
theorem rw_recipD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.recipD fd fs) a = true) :
    RowWitness (.recipD fd fs) a := by
  simp [ConsultsOracle] at h
theorem rw_rsqrtD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.rsqrtD fd fs) a = true) :
    RowWitness (.rsqrtD fd fs) a := by
  simp [ConsultsOracle] at h
theorem rw_movD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.movD fd fs) a = true) :
    RowWitness (.movD fd fs) a := by
  simp [ConsultsOracle] at h
theorem rw_absD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.absD fd fs) a = true) :
    RowWitness (.absD fd fs) a := by
  simp [ConsultsOracle] at h
theorem rw_negD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.negD fd fs) a = true) :
    RowWitness (.negD fd fs) a := by
  simp [ConsultsOracle] at h
theorem rw_cvtDW (fd fs : W32) (a : Arch) (h : ConsultsOracle (.cvtDW fd fs) a = true) :
    RowWitness (.cvtDW fd fs) a := by
  simp [ConsultsOracle] at h

end

end Refine
