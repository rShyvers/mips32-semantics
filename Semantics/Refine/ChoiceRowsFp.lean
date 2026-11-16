import Semantics.Refine.ChoiceRows

/-!
# Refine.ChoiceRowsFp — the FP rows of `ConsultsOracle` are real choices (wave 9; R6-5)

* every Operation that stores a 32-bit result into a 64-bit FPR (`StoreFPR(fpr, S/W, ...)`): the upper
  half of the FPR is UNPREDICTABLE (MD00082 Vol I-A Rev 6.01 §6.6.2, p.98; `Oracle.fprUpper`); the
  witness oracles give the upper halves 0 and 1 (`row_upper`, applied per constructor by `fpr32_row`
  in `consults_row`);
* `CVT.D.S` of a quiet NaN: two quiet NaNs (`Oracle.cvtQNaNToD`).

(R6-5: the 64-bit FPU of Release 6 removed the odd-register rows of the 32-bit FPU, and
`FCSR.ABS2008 = 1` the `ABS`/`NEG` QNaN reading; the former rows `ADD/SUB/MUL/DIV/SQRT/RECIP/RSQRT/
MOV/ABS/NEG.D`, `CVT.D.W` are no rows any more (`consults_row` closes them from the hypothesis). The helpers of the removed rows — `PairV`, `obs_pairV`, `obs_pair`, `row_AB`, `row_AA'S`,
`row_AA'D`, `row_dist`, `row_b16`, `dl_*`/`dr_*`/`db_*` — were removed with them. Release 6 also removed
the rows of `NMADD`/`NMSUB`, `C.cond.D`, `MADD.D`/`MSUB.D` and the FP conditional moves.)
-/

namespace Refine

open Manual

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

section
set_option linter.unusedSimpArgs false

/-! ## The 32-bit FPR results (`fprUpper`) -/

/-- **`fpr32_row fd`**: the row of an Operation that stores a 32-bit result into `FPR[fd]` (the goal is
`RowWitness ins a` for one of the `fprUpper` constructors of `ConsultsOracle`). It applies `row_upper`
with destination `fd`, unfolds the Operation (one `simp only` set covering all of them) and runs
`runp_up` on both witness oracles; it fails if `fd` is not the register the Operation writes. -/
macro "fpr32_row " fd:term : tactic => `(tactic| exact row_upper rfl $fd fun _ _ => by
  simp only [Ops.LWC1, Ops.MTC1, Ops.MOV_S, Ops.ABS_S, Ops.NEG_S, Ops.ADD_S, Ops.SUB_S, Ops.MUL_S,
    Ops.DIV_S, Ops.SQRT_S, Ops.RECIP_S, Ops.RSQRT_S, Ops.ROUND_W_S, Ops.TRUNC_W_S, Ops.CEIL_W_S,
    Ops.FLOOR_W_S, Ops.CVT_W_S, Ops.ROUND_W_D, Ops.TRUNC_W_D, Ops.CEIL_W_D, Ops.FLOOR_W_D, Ops.CVT_W_D,
    Ops.CVT_S_D, Ops.CVT_S_W, Ops.CVT_S_L, Ops.CMP_S, Ops.SEL_S, Ops.SELEQZ_S, Ops.SELNEZ_S,
    Ops.MADDF_S, Ops.MINMAX_S, Ops.CLASS_S, Ops.RINT_S]
  runp_up)

/-! ## `CVT.D.S` of a quiet NaN -/

theorem rw_cvtDS (fd fs : W32) (a : Arch) (h : ConsultsOracle (.cvtDS fd fs) a = true) :
    RowWitness (.cvtDS fd fs) a := by
  simp only [ConsultsOracle] at h
  exact row_of rfl { qd := true } { qd := false } (fun x => x.FPR (reg fd) = QA64) (fun x => x.FPR (reg fd) = QB64)
    (obs_fpr fd _ _ QA64_ne_QB64) (fun _ => by simp only [Ops.CVT_D_S, IEEE.cvtDS]; runp_up)
    (fun _ => by simp only [Ops.CVT_D_S, IEEE.cvtDS]; runp_up)

end

end Refine
