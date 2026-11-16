import Semantics.Refine.ChoiceWitness

/-!
# Refine.ChoiceRows — the rows of `ConsultsOracle` are real choices (integer, memory, control; wave 9)

For each row, two witness oracles (`wo`) and two properties of the completed state, and the proof
that the Operation run under each oracle signals an exception other than Coprocessor Unusable or
completes with its property (`RunP`, proved by unfolding the Operation and splitting its `if`s:
`runp`). The FP rows are in `Refine/ChoiceRowsFp.lean`; `consults_row` (`Refine/ChoiceExact.lean`)
collects them.

* loads with `LLbit = 1`: `loadClearsLL` true / false leaves `LLbit` 0 / 1 (MD00086 Vol II-A Rev 6.06,
  SC, p.347-348);
* stores with `LLbit = 1`: `storeClearsLL` true / false, the same;
* `CFC1` of a missing register with `rt ≠ 0`: two `GPR[rt]` values; `MFHC1` of an odd register with
  `rt ≠ 0`: two `GPR[rt]` values;
* `SDC1` of an odd register with `LLbit = 0`: two stored doublewords (all zeros, all ones);
* the UNPREDICTABLE / UNDEFINED operations (`CTC1`, `MFC0`/`MTC0`, `EXT`/`INS`, `JALR` with
  `rs = rd`, `MTHC1`/`LDC1` of an odd register): the witness oracle
  signals Reserved Instruction, so both runs signal and the two `Cause.CE` values tell them apart.
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
theorem obs_Mem (q : PAddr) (b₁ b₂ : UInt8) (hv : b₁ ≠ b₂) (x y : Arch) (hx : x.Mem q = b₁) (hy : y.Mem q = b₂) :
    Obs x ≠ Obs y := by
  intro he; have := congrArg (fun o => o.2.2.2.2 q) he; simp only [Obs] at this; rw [hx, hy] at this; exact hv this

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
theorem rw_lwc1 : RowWitness (.lwc1 base rt off) a := row_load rfl fun _ _ => by simp only [Ops.LWC1]; runp
theorem rw_sb : RowWitness (.sb base rt off) a := row_store rfl fun _ _ => by simp only [Ops.SB]; runp
theorem rw_sh : RowWitness (.sh base rt off) a := row_store rfl fun _ _ => by simp only [Ops.SH]; runp
theorem rw_sw : RowWitness (.sw base rt off) a := row_store rfl fun _ _ => by simp only [Ops.SW]; runp
theorem rw_swc1 : RowWitness (.swc1 base rt off) a := row_store rfl fun _ _ => by simp only [Ops.SWC1]; runp

end

/-! ## UNPREDICTABLE values: `GPR[rt]` -/

section
set_option linter.unusedSimpArgs false

theorem rw_cfc1 (rt fs : W32) (a : Arch) (h : ConsultsOracle (.cfc1 rt fs) a = true) : RowWitness (.cfc1 rt fs) a := by
  simp only [ConsultsOracle, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h0, h25⟩, h26⟩, h28⟩, h31⟩, hrt⟩ := h
  have hw := fun (x : Arch) (v : W32) => writeGPR_GPR x (reg rt) v hrt
  exact row_of rfl { cf := 0#32 } { cf := 1#32 } (fun x => x.GPR (reg rt) = 0#32) (fun x => x.GPR (reg rt) = 1#32)
    (fun x y => obs_GPR _ _ _ (by decide) x y) (fun _ => by simp only [Ops.CFC1]; runp)
    (fun _ => by simp only [Ops.CFC1]; runp)

theorem rw_mfhc1 (rt fs : W32) (a : Arch) (h : ConsultsOracle (.mfhc1 rt fs) a = true) :
    RowWitness (.mfhc1 rt fs) a := by
  simp only [ConsultsOracle, Bool.and_eq_true, OddFPR, bne_iff_ne, ne_eq] at h
  obtain ⟨hodd, hrt⟩ := h
  have hw := fun (x : Arch) (v : W32) => writeGPR_GPR x (reg rt) v hrt
  exact row_of rfl { rd := 0#64 } { rd := BitVec.allOnes 64 } (fun x => x.GPR (reg rt) = 0#32)
    (fun x => x.GPR (reg rt) = BitVec.allOnes 32)
    (fun x y => obs_GPR _ _ _ (by decide) x y) (fun _ => by simp only [Ops.MFHC1]; runp <;> decide)
    (fun _ => by simp only [Ops.MFHC1]; runp <;> decide)

end

/-! ## Operations the witness oracle resolves as an exception -/

section
set_option linter.unusedSimpArgs false

theorem rw_ctc1 (rt fs : W32) (a : Arch) (h : ConsultsOracle (.ctc1 rt fs) a = true) : RowWitness (.ctc1 rt fs) a := by
  simp only [ConsultsOracle, CTC1Unpredictable] at h
  exact row_sig rfl fun _ => by simp only [Ops.CTC1]; runp
theorem rw_mfc0 (rt rd sel : W32) (a : Arch) (h : ConsultsOracle (.mfc0 rt rd sel) a = true) :
    RowWitness (.mfc0 rt rd sel) a := by
  simp only [ConsultsOracle] at h
  exact row_sig rfl fun _ => by simp only [Ops.MFC0]; runp
theorem rw_mtc0 (rt rd sel : W32) (a : Arch) (h : ConsultsOracle (.mtc0 rt rd sel) a = true) :
    RowWitness (.mtc0 rt rd sel) a := by
  simp only [ConsultsOracle] at h
  exact row_sig rfl fun _ => by simp only [Ops.MTC0]; runp
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
theorem rw_mthc1 (rt fs : W32) (a : Arch) (h : ConsultsOracle (.mthc1 rt fs) a = true) : RowWitness (.mthc1 rt fs) a := by
  simp only [ConsultsOracle, OddFPR] at h
  exact row_sig rfl fun _ => by simp only [Ops.MTHC1]; runp

theorem rw_ldc1 (base ft off : W32) (a : Arch) (h : ConsultsOracle (.ldc1 base ft off) a = true) :
    RowWitness (.ldc1 base ft off) a := by
  simp only [ConsultsOracle, Bool.or_eq_true] at h
  by_cases ho : OddFPR ft = true
  · simp only [OddFPR] at ho
    exact row_sig rfl fun _ => by simp only [Ops.LDC1]; runp
  · have hl : a.LLbit = true := h.resolve_right ho
    simp only [OddFPR, Bool.not_eq_true] at ho
    exact row_load rfl fun _ _ => by simp only [Ops.LDC1]; runp
end

/-! ## `SDC1` of an odd register: the stored doubleword -/

theorem laneByte_of (w : W32) (c : BitVec 8) (h : ∀ s, s < 25 → BitVec.extractLsb' s 8 w = c) (k : Nat) :
    laneByte w k = ⟨c⟩ := by
  unfold laneByte
  have hk : laneShift k < 25 := by
    unfold laneShift; simp only [BigEndianMem, Bool.false_eq_true, ↓reduceIte]
    have := Nat.mod_lt k (show 4 > 0 by omega); omega
  rw [h _ hk]

theorem foldl_keep (base : PAddr) (w : W32) (b : UInt8) (hb : ∀ k, laneByte w k = b) (ls : List Nat) :
    ∀ (m : PAddr → UInt8) (q : PAddr), m q = b →
      ls.foldl (fun m l => updMem m (base + BitVec.ofNat 32 l) (laneByte w l)) m q = b := by
  induction ls with
  | nil => intro m q h; exact h
  | cons l ls ih =>
    intro m q h
    simp only [List.foldl_cons]
    exact ih _ _ (by simp only [updMem, hb]; split <;> simp_all)

theorem foldl_lane (base : PAddr) (w : W32) (b : UInt8) (hb : ∀ k, laneByte w k = b) (ls : List Nat) :
    ∀ (m : PAddr → UInt8) (l : Nat), l ∈ ls →
      ls.foldl (fun m l => updMem m (base + BitVec.ofNat 32 l) (laneByte w l)) m (base + BitVec.ofNat 32 l) = b := by
  induction ls with
  | nil => intro m l h; cases h
  | cons l0 ls ih =>
    intro m l h
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact foldl_keep base w b hb ls _ _ (by simp [updMem, hb])
    · exact ih _ l h

theorem storedLanes_ne (p : Nat) : ∃ l, l ∈ storedLanes p 3 := ⟨p, by simp [storedLanes]⟩

/-- The lanes the last word store of `SDC1` writes, at `q`, all hold `b`. -/
def LastStore (q : PAddr) (b : UInt8) (x : Arch) : Prop :=
  ∀ l ∈ storedLanes (q &&& 3#32).toNat WORD, x.Mem ((q &&& ~~~3#32) + BitVec.ofNat 32 l) = b

theorem obs_lastStore (q : PAddr) (x y : Arch) (hx : LastStore q 0 x) (hy : LastStore q 255 y) : Obs x ≠ Obs y := by
  obtain ⟨l, hl⟩ := storedLanes_ne (q &&& 3#32).toNat
  exact obs_Mem _ 0 255 (by decide) x y (hx l hl) (hy l hl)

theorem lb_zero (k : Nat) : laneByte (BitVec.extractLsb' 32 32 (0#64)) k = 0 :=
  laneByte_of _ 0#8 (by decide) k
theorem lb_zero' (k : Nat) : laneByte (BitVec.extractLsb' 0 32 (0#64)) k = 0 :=
  laneByte_of _ 0#8 (by decide) k
theorem lb_ones (k : Nat) : laneByte (BitVec.extractLsb' 32 32 (BitVec.allOnes 64)) k = 255 :=
  laneByte_of _ 255#8 (by decide) k
theorem lb_ones' (k : Nat) : laneByte (BitVec.extractLsb' 0 32 (BitVec.allOnes 64)) k = 255 :=
  laneByte_of _ 255#8 (by decide) k

/-- `runp` without closing the completed paths. -/
macro "runp_core" : tactic => `(tactic| (
  runp_simp
  repeat' (case_ite <;> (try runp_simp))
  all_goals (first | (simp_all [CEof]; done) | skip)))

/-- The physical address of the second word an `SDC1` with effective address `v` stores
(SDC1, Operation, p.362: `paddr ← paddr xor ((BigEndianCPU xor ReverseEndian) || 0^2)`, then
`paddr xor 0b100`). -/
def sdQ (a : Arch) (v : W32) : PAddr :=
  FixedMapping (StatusERL a) (memory_address v) ^^^
    ((BitVec.ofBool (BigEndianCPU a ^^ ReverseEndian a) ++ 0#2 : BitVec 3).setWidth 32) ^^^ 0b100#32

section
set_option linter.unusedSimpArgs false

theorem rw_sdc1 (base ft off : W32) (a : Arch) (h : ConsultsOracle (.sdc1 base ft off) a = true) :
    RowWitness (.sdc1 base ft off) a := by
  simp only [ConsultsOracle, Bool.or_eq_true] at h
  by_cases hl : a.LLbit = true
  · exact row_store rfl fun _ _ => by simp only [Ops.SDC1]; runp
  · have ho := h.resolve_left hl
    simp only [OddFPR] at ho
    simp only [Bool.not_eq_true] at hl
    refine row_of rfl { rd := 0#64 } { rd := BitVec.allOnes 64 }
      (LastStore (sdQ a (sign_extend (imm16 off) + readGPR a (reg base))) 0)
      (LastStore (sdQ a (sign_extend (imm16 off) + readGPR a (reg base))) 255)
      (fun x y => obs_lastStore _ x y) (fun _ => ?_) (fun _ => ?_) <;> simp only [Ops.SDC1] <;> runp_core
    · exact ⟨fun l hl => foldl_lane _ _ _ lb_zero _ _ _ hl, rfl⟩
    · exact ⟨fun l hl => foldl_lane _ _ _ lb_ones _ _ _ hl, rfl⟩

end

end Refine
