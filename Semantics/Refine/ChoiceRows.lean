import Semantics.Refine.ChoiceWitness

/-!
# Refine.ChoiceRows — the rows of `ConsultsOracle` are real choices (integer, memory, control)

For each row, two witness oracles (`wo`) and two properties of the completed state, and the proof
that the Operation run under each oracle signals an exception other than Coprocessor Unusable or
completes with its property (`RunP`, proved by unfolding the Operation and splitting its `if`s:
`runp`). The FP rows are in `Refine/ChoiceRowsFp.lean`; `consults_row` (`Refine/ChoiceExact.lean`)
collects them.

* loads with `LLbit = 1`: `loadClearsLL` true / false leaves `LLbit` 0 / 1 (MD00086 Vol II-A Rev 6.06,
  SC, p.347-348);
* stores with `LLbit = 1`: `storeClearsLL` true / false, the same;
* the UNPREDICTABLE / UNDEFINED operations (`CTC1`, `MFC0`/`MTC0`, `EXT`/`INS`, `JALR` with
  `rs = rd`): the witness oracle
  signals Reserved Instruction, so both runs signal and the two `Cause.CE` values tell them apart.
(the odd-register rows of `MFHC1`/`MTHC1`/`LDC1`/`SDC1` went with the 32-bit FPU; `LDC1`/`SDC1`
are `LLbit` rows, `MFHC1`/`MTHC1`/`MFC0`/`CFC1` no rows (`consults_row` closes them from the
hypothesis); `LWC1` is a row of the 32-bit FPR results, `Refine/ChoiceRowsFp.lean`. The compact
branch-and-link rows share one arm of `consults_row`.)
-/

namespace Refine

open Manual

theorem RunP_ok (a : Arch) (P : Arch → Prop) (f : Frame) :
    RunP a P (.ok (), f) ↔ P f.arch ∧ CEof f.arch = CEof a := Iff.rfl
theorem RunP_sig (a : Arch) (P : Arch → Prop) (e : Exception) (f : Frame) :
    RunP a P (.signal e, f) ↔ NotCpU e := Iff.rfl

theorem toBits_b4' (f : Mips.Fp.Flags) : f.toBits[4] = f.invalid := by
  obtain ⟨a, b, c, d, e⟩ := f; cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

/-- Unfold an Operation run under a witness oracle into its paths. -/
macro "runp_simp" : tactic => `(tactic| simp only [bind, GPR, Pseudo.get, AddressTranslation, setGPR, pure,
    ite_app2, Pseudo.oracle, Pseudo.impl, SignalException, LoadMemory, StoreMemory, ValueFPR64,
    StoreFPR64, ValueFPR32, StoreFPR32, Pseudo.modify, resolve, unpredictableOr, FPResult, CheckFPException,
    wo, ctxOf, sigRI, RunP_ok, RunP_sig, NotCpU, ne_eq, reduceCtorEq,
    not_false_eq_true, implies_true, ↓reduceIte, Bool.false_eq_true, CEof_writeGPR, writeGPR_LLbit,
    and_true, true_and, FP32RegistersMode, beq_self_eq_true, *])

/-- Prove a `RunP` goal: unfold, split every `if`, close each path. -/
macro "runp" : tactic => `(tactic| (
  runp_simp
  repeat' (case_ite <;> (try runp_simp))
  all_goals (simp_all [CEof, bit, toBits_b4', Mips.Fp.Flags.invalidOnly, Mips.Fp.Flags.none,
    BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth])))

/-! ## Assembling a row -/

theorem row_of {ins : Instruction} {a : Arch} {O : Pseudo Unit} (hO : Operation ins = some O)
    (p₁ p₂ : WP) (P₁ P₂ : Arch → Prop) (hobs : ∀ x y, P₁ x → P₂ y → Obs x ≠ Obs y)
    (h₁ : ∀ ce, RunP a P₁ (O (ctxOf modelImpl (wo p₁ ce)) { arch := a }))
    (h₂ : ∀ ce, RunP a P₂ (O (ctxOf modelImpl (wo p₂ ce)) { arch := a })) : RowWitness ins a :=
  ⟨p₁, p₂, P₁, P₂, hobs, fun op ce hop => by
    rw [hO, Option.some.injEq] at hop; subst hop; exact ⟨h₁ ce, h₂ ce⟩⟩

/-- A row where the witness oracle makes the Operation signal. -/
theorem row_sig {ins : Instruction} {a : Arch} {O : Pseudo Unit} (hO : Operation ins = some O)
    (h : ∀ ce, RunP a (fun _ => False) (O (ctxOf modelImpl (wo {} ce)) { arch := a })) : RowWitness ins a :=
  row_of hO {} {} _ _ (fun _ _ hx => hx.elim) h h

theorem obs_LL (x y : Arch) (hx : x.LLbit = !true) (hy : y.LLbit = !false) : Obs x ≠ Obs y := by
  intro he; have := congrArg (·.1) he; simp_all [Obs]
theorem obs_GPR (r : Fin 32) (v₁ v₂ : W32) (hv : v₁ ≠ v₂) (x y : Arch) (hx : x.GPR r = v₁) (hy : y.GPR r = v₂) :
    Obs x ≠ Obs y := by
  intro he; have := congrArg (fun o => o.2.1 r) he; simp only [Obs] at this; rw [hx, hy] at this; exact hv this

/-! ## Loads and stores while `LLbit = 1` -/

/-- A load row: `loadClearsLL` true / false. -/
theorem row_load {ins : Instruction} {a : Arch} {O : Pseudo Unit} (hO : Operation ins = some O)
    (h : ∀ ce lc, RunP a (fun x => x.LLbit = !lc) (O (ctxOf modelImpl (wo { lc := lc } ce)) { arch := a })) :
    RowWitness ins a :=
  row_of hO { lc := true } { lc := false } _ _ obs_LL (fun ce => h ce true) (fun ce => h ce false)

/-- A store row: `storeClearsLL` true / false. -/
theorem row_store {ins : Instruction} {a : Arch} {O : Pseudo Unit} (hO : Operation ins = some O)
    (h : ∀ ce sc, RunP a (fun x => x.LLbit = !sc) (O (ctxOf modelImpl (wo { sc := sc } ce)) { arch := a })) :
    RowWitness ins a :=
  row_of hO { sc := true } { sc := false } _ _ obs_LL (fun ce => h ce true) (fun ce => h ce false)

section
set_option linter.unusedSimpArgs false
variable (base rt off : W32) (a : Arch) (h : a.LLbit = true)
include h

theorem rw_lb : RowWitness (.lb base rt off) a := row_load rfl fun _ _ => by simp only [Ops.LB]; runp
theorem rw_lbu : RowWitness (.lbu base rt off) a := row_load rfl fun _ _ => by simp only [Ops.LBU]; runp
theorem rw_lh : RowWitness (.lh base rt off) a := row_load rfl fun _ _ => by simp only [Ops.LH]; runp
theorem rw_lhu : RowWitness (.lhu base rt off) a := row_load rfl fun _ _ => by simp only [Ops.LHU]; runp
theorem rw_lw : RowWitness (.lw base rt off) a := row_load rfl fun _ _ => by simp only [Ops.LW]; runp
theorem rw_sb : RowWitness (.sb base rt off) a := row_store rfl fun _ _ => by simp only [Ops.SB]; runp
theorem rw_sh : RowWitness (.sh base rt off) a := row_store rfl fun _ _ => by simp only [Ops.SH]; runp
theorem rw_sw : RowWitness (.sw base rt off) a := row_store rfl fun _ _ => by simp only [Ops.SW]; runp
theorem rw_swc1 : RowWitness (.swc1 base rt off) a := row_store rfl fun _ _ => by simp only [Ops.SWC1]; runp

end

/-! ## UNPREDICTABLE values: `GPR[rt]` -/

section
set_option linter.unusedSimpArgs false

end

/-! ## Release 6: `LWPC` while `LLbit = 1`; `DIV`/`MOD`/`DIVU`/`MODU` by zero with `rd ≠ 0`

`LWPC` is a load (`loadClearsLL`). A zero divisor writes `divByZero` to `GPR[rd]`: the witness
oracles give 0 and 1. -/

section
set_option linter.unusedSimpArgs false

theorem rw_lwpc (rs off : W32) (a : Arch) (h : ConsultsOracle (.lwpc rs off) a = true) :
    RowWitness (.lwpc rs off) a := by
  have hl : a.LLbit = true := h
  exact row_load rfl fun _ _ => by simp only [Ops.LWPC, bind, PC]; runp

/-- A division row: the two witness values of `divByZero` reach `GPR[rd]`. -/
theorem row_div {ins : Instruction} {a : Arch} {O : Pseudo Unit} (hO : Operation ins = some O)
    (rd : W32)
    (h : ∀ ce dz, RunP a (fun x => x.GPR (reg rd) = dz) (O (ctxOf modelImpl (wo { dz := dz } ce)) { arch := a })) :
    RowWitness ins a :=
  row_of hO { dz := 0#32 } { dz := 1#32 } _ _ (fun x y => obs_GPR _ _ _ (by decide) x y)
    (fun ce => h ce 0#32) (fun ce => h ce 1#32)

theorem rw_div (rs rt rd : W32) (a : Arch) (h : ConsultsOracle (.div rs rt rd) a = true) :
    RowWitness (.div rs rt rd) a := by
  simp only [ConsultsOracle, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨hz, hrd⟩ := h
  have hw := fun (x : Arch) (v : W32) => writeGPR_GPR x (reg rd) v hrd
  exact row_div rfl rd fun _ _ => by simp only [Ops.DIV, Ops.divResult]; runp
theorem rw_mod (rs rt rd : W32) (a : Arch) (h : ConsultsOracle (.mod rs rt rd) a = true) :
    RowWitness (.mod rs rt rd) a := by
  simp only [ConsultsOracle, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨hz, hrd⟩ := h
  have hw := fun (x : Arch) (v : W32) => writeGPR_GPR x (reg rd) v hrd
  exact row_div rfl rd fun _ _ => by simp only [Ops.MOD, Ops.divResult]; runp
theorem rw_divu (rs rt rd : W32) (a : Arch) (h : ConsultsOracle (.divu rs rt rd) a = true) :
    RowWitness (.divu rs rt rd) a := by
  simp only [ConsultsOracle, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨hz, hrd⟩ := h
  have hw := fun (x : Arch) (v : W32) => writeGPR_GPR x (reg rd) v hrd
  exact row_div rfl rd fun _ _ => by simp only [Ops.DIVU, Ops.divResult]; runp
theorem rw_modu (rs rt rd : W32) (a : Arch) (h : ConsultsOracle (.modu rs rt rd) a = true) :
    RowWitness (.modu rs rt rd) a := by
  simp only [ConsultsOracle, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨hz, hrd⟩ := h
  have hw := fun (x : Arch) (v : W32) => writeGPR_GPR x (reg rd) v hrd
  exact row_div rfl rd fun _ _ => by simp only [Ops.MODU, Ops.divResult]; runp

end

/-! ## Operations the witness oracle resolves as an exception -/

section
set_option linter.unusedSimpArgs false

theorem rw_ctc1 (rt fs : W32) (a : Arch) (h : ConsultsOracle (.ctc1 rt fs) a = true) : RowWitness (.ctc1 rt fs) a := by
  simp only [ConsultsOracle, CTC1Unpredictable] at h
  exact row_sig rfl fun _ => by simp only [Ops.CTC1]; runp
theorem rw_mtc0 (rt rd sel : W32) (a : Arch) (h : ConsultsOracle (.mtc0 rt rd sel) a = true) :
    RowWitness (.mtc0 rt rd sel) a := by
  simp only [ConsultsOracle] at h
  exact row_sig rfl fun _ => by
    simp only [Ops.MTC0]; runp <;> simp_all [IsCoprocessorRegisterImplemented]
theorem rw_ext (rt rs pos size : W32) (a : Arch) (h : ConsultsOracle (.ext rt rs pos size) a = true) :
    RowWitness (.ext rt rs pos size) a := by
  simp only [ConsultsOracle, decide_eq_true_eq] at h
  exact row_sig rfl fun _ => by simp only [Ops.EXT]; runp
theorem rw_ins (rt rs pos size : W32) (a : Arch) (h : ConsultsOracle (.ins rt rs pos size) a = true) :
    RowWitness (.ins rt rs pos size) a := by
  simp only [ConsultsOracle, decide_eq_true_eq] at h
  exact row_sig rfl fun _ => by simp only [Ops.INS]; runp
theorem rw_jalr (rs rd : W32) (a : Arch) (h : ConsultsOracle (.jalr rs rd) a = true) : RowWitness (.jalr rs rd) a := by
  simp only [ConsultsOracle, beq_iff_eq] at h
  exact row_sig rfl fun _ => by simp only [Ops.JALR]; runp
theorem rw_jalrHb (rs rd : W32) (a : Arch) (h : ConsultsOracle (.jalrHb rs rd) a = true) :
    RowWitness (.jalrHb rs rd) a := by
  simp only [ConsultsOracle, beq_iff_eq] at h
  exact row_sig rfl fun _ => by simp only [Ops.JALR_HB]; runp

theorem rw_ldc1 (base ft off : W32) (a : Arch) (h : ConsultsOracle (.ldc1 base ft off) a = true) :
    RowWitness (.ldc1 base ft off) a := by
  have hl : a.LLbit = true := h
  exact row_load rfl fun _ _ => by simp only [Ops.LDC1]; runp
end

/-! ## `SDC1` while `LLbit = 1` -/

section
set_option linter.unusedSimpArgs false

theorem rw_sdc1 (base ft off : W32) (a : Arch) (h : ConsultsOracle (.sdc1 base ft off) a = true) :
    RowWitness (.sdc1 base ft off) a := by
  have hl : a.LLbit = true := h
  exact row_store rfl fun _ _ => by simp only [Ops.SDC1]; runp

end

end Refine
