import Semantics.Refine.ChoiceFp

/-!
# Refine.ChoicePoints — the Operations are oracle-free where `ConsultsOracle` says so

`operation_choiceFree`: when `Manual.ConsultsOracle ins a = false`, the Operation of `ins` run from `a`
gives the same result (value, exception and state) under any two oracles. For the constructors
whose Operation reads no oracle field this is definitional (`rfl`); for those that read one the
proof (`ofree`) unfolds the Operation, splits on the conditions it tests (`case_ite`), rewrites the
oracle-reading primitives to their oracle-free form under the hypotheses (`LoadMemory_free`,
`StoreMemory_free` while `LLbit = 0`, `cvtDS_free` away from a quiet NaN), and closes with `rfl`.
Every Operation that stores a 32-bit result into an FPR reads `fprUpper` and is always a row
(the hypothesis is the contradiction `true = false`). The constructors whose proof differs have their
own `cf_<ctor>`, which `operation_choiceFree` picks by name (`apply_ctor_lemma`): `LL` and `SC` set
`LLbit` after their memory access, so their `loadClearsLL`/`storeClearsLL` choice never shows
(`LoadMemory_any`, `StoreMemory_any`); `CFC1`/`CTC1` case on the control register; the divisions
write the oracle's value only to `GPR[0]` (`cf_divResult`).
-/

namespace Refine

open Manual

open Lean Meta Elab Tactic in
/-- Case on the condition of the first `if` of the goal that is not under a binder. -/
elab "case_ite" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some e := t.find? (fun e => (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) &&
      !(e.getArg! 1).hasLooseBVars) | throwError "case_ite: no closed if"
  let s ← g.byCases (e.getArg! 1) `hc
  replaceMainGoal [s.1.mvarId, s.2.mvarId]

theorem arch_LLbit_false (a : Arch) (h : a.LLbit = false) : { a with LLbit := false } = a := by
  cases a; simp_all

theorem LoadMemory_free (cca : BitVec 3) (n : Nat) (pa va : W32) (iord : IorD) (c : Ctx) (f : Frame)
    (h : f.arch.LLbit = false) :
    LoadMemory cca n pa va iord c f = (.ok (MemElemAt f.arch.Mem pa), f) := by
  obtain ⟨a, p, d⟩ := f
  simp only at h
  simp only [LoadMemory, bind, Pseudo.get, Pseudo.oracle, Pseudo.modify]
  split
  · simp only [arch_LLbit_false a h]; rfl
  · rfl

theorem StoreMemory_free (cca : BitVec 3) (n : Nat) (m pa va : W32) (c : Ctx) (f : Frame)
    (h : f.arch.LLbit = false) :
    StoreMemory cca n m pa va c f = (.ok (), { f with arch := { f.arch with
      Mem := (storedLanes (pa &&& 3#32).toNat n).foldl
        (fun mm l => updMem mm ((pa &&& ~~~3#32) + BitVec.ofNat 32 l) (laneByte m l)) f.arch.Mem,
      LLbit := false } }) := by
  obtain ⟨a, p, d⟩ := f
  simp only at h
  simp only [StoreMemory, bind, Pseudo.oracle, Pseudo.modify, h, ite_self]

theorem cvtDS_free (q : W32 → BitVec 64) (a : Arch) (x : W32) (h : Mips.Fp.isQNaN32 x = false) :
    IEEE.cvtDS q a x = Mips.Fp.f32ToF64 (FCSR_FS a) x := by
  simp only [IEEE.cvtDS, h, Bool.false_eq_true, ite_false]
theorem cvtSD_free (q : BitVec 64 → W32) (a : Arch) (x : BitVec 64) (h : Mips.Fp.isQNaN64 x = false) :
    IEEE.cvtSD q a x = Mips.Fp.f64ToF32 (IEEE.env a) x := by
  simp only [IEEE.cvtSD, h, Bool.false_eq_true, ite_false]

theorem fcsr_flags_keep (F : W32) (x : BitVec 5) :
    let G := F &&& ~~~(63#32 <<< 12) ||| BitVec.setWidth 32 x <<< 12 ||| BitVec.setWidth 32 x <<< 2
    G.extractLsb' 0 2 = F.extractLsb' 0 2 ∧ G.extractLsb' 7 5 = F.extractLsb' 7 5 ∧
      G.getLsbD 24 = F.getLsbD 24 := by
  refine ⟨?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> simp
  · simp

/-- `FPResult` without a trap leaves the FP environment (`RM`, `Enables`, `FS`) as it was. -/
theorem env_fpResult (a : Arch) (x : BitVec 5) :
    IEEE.env { a with FCSR :=
      a.FCSR &&& ~~~(63#32 <<< 12) ||| BitVec.setWidth 32 x <<< 12 ||| BitVec.setWidth 32 x <<< 2 } = IEEE.env a := by
  obtain ⟨h1, h2, h3⟩ := fcsr_flags_keep a.FCSR x
  simp only [IEEE.env, FCSR_RM, FCSR_Enables, FCSR_FS, bit, h1, h2, h3]

theorem addS_fpResult (a : Arch) (x : BitVec 5) (u v : W32) :
    IEEE.addS { a with FCSR :=
      a.FCSR &&& ~~~(63#32 <<< 12) ||| BitVec.setWidth 32 x <<< 12 ||| BitVec.setWidth 32 x <<< 2 } u v = IEEE.addS a u v := by simp only [IEEE.addS, env_fpResult]
theorem subS_fpResult (a : Arch) (x : BitVec 5) (u v : W32) :
    IEEE.subS { a with FCSR :=
      a.FCSR &&& ~~~(63#32 <<< 12) ||| BitVec.setWidth 32 x <<< 12 ||| BitVec.setWidth 32 x <<< 2 } u v = IEEE.subS a u v := by simp only [IEEE.subS, env_fpResult]
theorem addD_fpResult (a : Arch) (x : BitVec 5) (u v : BitVec 64) :
    IEEE.addD { a with FCSR :=
      a.FCSR &&& ~~~(63#32 <<< 12) ||| BitVec.setWidth 32 x <<< 12 ||| BitVec.setWidth 32 x <<< 2 } u v = IEEE.addD a u v := by simp only [IEEE.addD, env_fpResult]
theorem subD_fpResult (a : Arch) (x : BitVec 5) (u v : BitVec 64) :
    IEEE.subD { a with FCSR :=
      a.FCSR &&& ~~~(63#32 <<< 12) ||| BitVec.setWidth 32 x <<< 12 ||| BitVec.setWidth 32 x <<< 2 } u v = IEEE.subD a u v := by simp only [IEEE.subD, env_fpResult]

theorem LoadMemory_any (cca : BitVec 3) (n : Nat) (pa va : W32) (iord : IorD) (c : Ctx) (f : Frame) :
    LoadMemory cca n pa va iord c f = (.ok (MemElemAt f.arch.Mem pa), { f with arch := { f.arch with
      LLbit := f.arch.LLbit && !(iord == .DATA && c.oracle.loadClearsLL f.arch) } }) := by
  obtain ⟨a, p, d⟩ := f
  simp only [LoadMemory, bind, Pseudo.get, Pseudo.oracle, Pseudo.modify]
  split
  · rename_i hh; simp only [hh, Bool.not_true, Bool.and_false]; rfl
  · rename_i hh; simp only [Bool.not_eq_true] at hh; simp only [hh, Bool.not_false, Bool.and_true]
    cases a; rfl

theorem StoreMemory_any (cca : BitVec 3) (n : Nat) (m pa va : W32) (c : Ctx) (f : Frame) :
    StoreMemory cca n m pa va c f = (.ok (), { f with arch := { f.arch with
      Mem := (storedLanes (pa &&& 3#32).toNat n).foldl
        (fun mm l => updMem mm ((pa &&& ~~~3#32) + BitVec.ofNat 32 l) (laneByte m l)) f.arch.Mem,
      LLbit := if c.oracle.storeClearsLL f.arch then false else f.arch.LLbit } }) := rfl

theorem ite_app2 {α β γ : Type} (c : Prop) [Decidable c] (f g : α → β → γ) (x : α) (y : β) :
    (if c then f else g) x y = if c then f x y else g x y := by split <;> rfl

macro "ofree_simp" : tactic => `(tactic| simp only [bind, GPR, Pseudo.get, AddressTranslation, setGPR, pure,
    ite_app2, Pseudo.oracle, Pseudo.impl, SignalException, LoadMemory_free, StoreMemory_free, ValueFPR64,
    StoreFPR64, IEEE.absS, IEEE.negS, IEEE.absD, IEEE.negD, cvtDS_free,
    cvtSD_free, ValueFPR32, StoreFPR32, Pseudo.modify, *, ↓reduceIte, Bool.false_eq_true, not_false_eq_true,
    FPResult, CheckFPException,
    addS_fpResult, subS_fpResult, addD_fpResult, subD_fpResult, ctxOf])

macro "cf_pre" h:ident : tactic => `(tactic| (
  (try simp only [ConsultsOracle, Bool.or_eq_false_iff,
    Bool.not_eq_false', decide_eq_false_iff_not] at $h:ident)
  repeat (obtain ⟨_, $h:ident⟩ := $h:ident)))

macro "ofree_all" : tactic => `(tactic| (
  (try simp_all only [bind, GPR, Pseudo.get, AddressTranslation, setGPR, pure,
    ite_app2, Pseudo.oracle, Pseudo.impl, SignalException, LoadMemory_free, StoreMemory_free, ValueFPR64,
    StoreFPR64, IEEE.absS, IEEE.negS, IEEE.absD, IEEE.negD, cvtDS_free,
    cvtSD_free, ValueFPR32, StoreFPR32, Pseudo.modify, ↓reduceIte, Bool.false_eq_true, not_false_eq_true,
    FPResult, CheckFPException,
    addS_fpResult, subS_fpResult, addD_fpResult, subD_fpResult, ctxOf, CTC1Unpredictable, Bool.and_true, Bool.true_and, Bool.and_false,
    Bool.false_and, bne_eq_false_iff_eq, writeGPR, Bool.or_false, Bool.not_false, Bool.not_true,
    Bool.true_eq_false, Bool.or_true])
  repeat' (first | rfl | (case_ite <;> (try simp_all only [bind, GPR, Pseudo.get, AddressTranslation, setGPR, pure,
    ite_app2, Pseudo.oracle, Pseudo.impl, SignalException, LoadMemory_free, StoreMemory_free, ValueFPR64,
    StoreFPR64, IEEE.absS, IEEE.negS, IEEE.absD, IEEE.negD, cvtDS_free,
    cvtSD_free, ValueFPR32, StoreFPR32, Pseudo.modify, ↓reduceIte, Bool.false_eq_true, not_false_eq_true,
    FPResult, CheckFPException,
    addS_fpResult, subS_fpResult, addD_fpResult, subD_fpResult, ctxOf, CTC1Unpredictable, Bool.and_true,
    Bool.true_and, Bool.and_false, Bool.false_and, bne_eq_false_iff_eq, writeGPR, Bool.or_false, Bool.not_false, Bool.not_true,
    Bool.true_eq_false, Bool.or_true])))))

macro "ofree_ll" : tactic => `(tactic| (
  (try simp_all only [bind, GPR, Pseudo.get, AddressTranslation, setGPR, pure,
    ite_app2, Pseudo.oracle, Pseudo.impl, SignalException, LoadMemory_any, StoreMemory_any, ValueFPR64,
    StoreFPR64, IEEE.absS, IEEE.negS, IEEE.absD, IEEE.negD, cvtDS_free,
    cvtSD_free, ValueFPR32, StoreFPR32, Pseudo.modify, ↓reduceIte, Bool.false_eq_true, not_false_eq_true,
    FPResult, CheckFPException,
    addS_fpResult, subS_fpResult, addD_fpResult, subD_fpResult, ctxOf, CTC1Unpredictable, Bool.and_true, Bool.true_and, Bool.and_false,
    Bool.false_and, bne_eq_false_iff_eq, writeGPR, Bool.or_false, Bool.not_false, Bool.not_true,
    Bool.true_eq_false, Bool.or_true])
  repeat' (first | rfl | (case_ite <;> (try simp_all only [bind, GPR, Pseudo.get, AddressTranslation, setGPR, pure,
    ite_app2, Pseudo.oracle, Pseudo.impl, SignalException, LoadMemory_any, StoreMemory_any, ValueFPR64,
    StoreFPR64, IEEE.absS, IEEE.negS, IEEE.absD, IEEE.negD, cvtDS_free,
    cvtSD_free, ValueFPR32, StoreFPR32, Pseudo.modify, ↓reduceIte, Bool.false_eq_true, not_false_eq_true,
    FPResult, CheckFPException,
    addS_fpResult, subS_fpResult, addD_fpResult, subD_fpResult, ctxOf, CTC1Unpredictable, Bool.and_true,
    Bool.true_and, Bool.and_false, Bool.false_and, bne_eq_false_iff_eq, writeGPR, Bool.or_false, Bool.not_false, Bool.not_true,
    Bool.true_eq_false, Bool.or_true])))))

macro "ofree" : tactic => `(tactic| (
  (try ofree_simp)
  repeat' (first | with_reducible rfl | (case_ite <;> (try ofree_simp)) | rfl)))

theorem cf_ll (base rt off : W32) (a : Arch) (h : ConsultsOracle (.ll base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.LL base rt off (ctxOf i o₁) { arch := a } = Ops.LL base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.LL]; ofree_ll

theorem cf_sc (base rt off : W32) (a : Arch) (h : ConsultsOracle (.sc base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.SC base rt off (ctxOf i o₁) { arch := a } = Ops.SC base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.SC]; ofree_ll

theorem cf_cfc1 (rt fs : W32) (a : Arch) (h : ConsultsOracle (.cfc1 rt fs) a = false) (i : Impl)
    (o₁ o₂ : Oracle) :
    Ops.CFC1 rt fs (ctxOf i o₁) { arch := a } = Ops.CFC1 rt fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.CFC1]; ofree_all

/-- Both sides of a path of `CTC1` that reads no oracle field: the FCSR write then `CheckFPException`. -/
macro "ccheck" : tactic => `(tactic| (simp only [Pseudo.modify, CheckFPException, bind, Pseudo.get,
  SignalException, ite_app2, pure] <;> try rfl))

theorem cf_ctc1 (rt fs : W32) (a : Arch) (h : ConsultsOracle (.ctc1 rt fs) a = false) (i : Impl)
    (o₁ o₂ : Oracle) :
    Ops.CTC1 rt fs (ctxOf i o₁) { arch := a } = Ops.CTC1 rt fs (ctxOf i o₂) { arch := a } := by
  simp only [ConsultsOracle, CTC1Unpredictable] at h
  simp only [Ops.CTC1, bind, GPR, Pseudo.get, Pseudo.oracle, ctxOf]
  generalize low (readGPR a (reg rt)) 32 = t at h ⊢
  by_cases h14 : (fs == 1#32 || fs == 4#32) = true
  · simp only [h14, ite_true, ite_app2]
    rfl
  by_cases h56 : (fs == 5#32 || fs == 6#32) = true
  · simp [h56] at h
  simp only [h56, Bool.false_eq_true, ite_false] at h
  simp only [h14, h56, Bool.false_eq_true, ite_false, ite_app2]
  by_cases h25 : fs = 25#32
  · subst h25; simp only [beq_self_eq_true, ite_true] at h ⊢
    simp only [h, Bool.false_eq_true, ite_false]; ccheck
  by_cases h26 : fs = 26#32
  · subst h26; simp only [beq_self_eq_true, ite_true, BitVec.reduceBEq, Bool.false_eq_true, ite_false] at h ⊢
    simp only [h, Bool.false_eq_true, ite_false]; ccheck
  by_cases h28 : fs = 28#32
  · subst h28; simp only [beq_self_eq_true, ite_true, BitVec.reduceBEq, Bool.false_eq_true, ite_false] at h ⊢
    simp only [h, Bool.false_eq_true, ite_false]; ccheck
  by_cases h31 : fs = 31#32
  · subst h31; simp only [beq_self_eq_true, ite_true, BitVec.reduceBEq, Bool.false_eq_true, ite_false] at h ⊢
    simp only [h, Bool.false_eq_true, ite_false]; ccheck
  simp only [beq_false_of_ne h25, beq_false_of_ne h26, beq_false_of_ne h28, beq_false_of_ne h31,
    Bool.false_eq_true, ite_false]
  ccheck

/-- A zero divisor writes the oracle's value to `GPR[rd]`, which has no effect for `rd = 0`; otherwise
the Operation reads no oracle field. -/
theorem cf_divResult (j : Instruction) (rs rd : W32) (zero : Bool) (v : W32) (a : Arch)
    (h : (zero && reg rd != 0) = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.divResult j rs rd zero v (ctxOf i o₁) { arch := a } =
      Ops.divResult j rs rd zero v (ctxOf i o₂) { arch := a } := by
  cases zero
  · rfl
  · have hrd : reg rd = 0 := by simpa using h
    simp only [Ops.divResult, bind, GPR, Pseudo.get, Pseudo.oracle, setGPR, writeGPR, hrd, ↓reduceIte]

theorem cf_div (rs rt rd : W32) (a : Arch) (h : ConsultsOracle (.div rs rt rd) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.DIV rs rt rd (ctxOf i o₁) { arch := a } = Ops.DIV rs rt rd (ctxOf i o₂) { arch := a } := by
  simp only [ConsultsOracle, ← toInt_beq_zero] at h
  simp only [Ops.DIV, bind, GPR]
  exact cf_divResult _ rs rd _ _ a h i o₁ o₂

theorem cf_mod (rs rt rd : W32) (a : Arch) (h : ConsultsOracle (.mod rs rt rd) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MOD rs rt rd (ctxOf i o₁) { arch := a } = Ops.MOD rs rt rd (ctxOf i o₂) { arch := a } := by
  simp only [ConsultsOracle, ← toInt_beq_zero] at h
  simp only [Ops.MOD, bind, GPR]
  exact cf_divResult _ rs rd _ _ a h i o₁ o₂

theorem cf_divu (rs rt rd : W32) (a : Arch) (h : ConsultsOracle (.divu rs rt rd) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.DIVU rs rt rd (ctxOf i o₁) { arch := a } = Ops.DIVU rs rt rd (ctxOf i o₂) { arch := a } := by
  simp only [ConsultsOracle, ← toNat_eq_zero'] at h
  simp only [Ops.DIVU, bind, GPR]
  exact cf_divResult _ rs rd _ _ a h i o₁ o₂

theorem cf_modu (rs rt rd : W32) (a : Arch) (h : ConsultsOracle (.modu rs rt rd) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MODU rs rt rd (ctxOf i o₁) { arch := a } = Ops.MODU rs rt rd (ctxOf i o₂) { arch := a } := by
  simp only [ConsultsOracle, ← toNat_eq_zero'] at h
  simp only [Ops.MODU, bind, GPR]
  exact cf_divResult _ rs rd _ _ a h i o₁ o₂

set_option linter.unusedSimpArgs false in
/-- **`unfold_ops`**: unfold the Operation (`Ops.<NAME>`, with the compact-branch helpers and `PC`) at
the head of an `operation_choiceFree` goal; fails if none of them occurs. -/
macro "unfold_ops" : tactic => `(tactic| simp only [
      Ops.ABS_D, Ops.ABS_S, Ops.ADD, Ops.ADDIU, Ops.ADDU, Ops.ADD_D, Ops.ADD_S, Ops.AND,
      Ops.ANDI, Ops.AUI, Ops.BAL, Ops.BEQ, Ops.BGEZ, Ops.BGTZ, Ops.BLEZ, Ops.BLTZ, Ops.BNE,
      Ops.BREAK, Ops.CEIL_W_D, Ops.CEIL_W_S, Ops.CLO, Ops.CLZ, Ops.CVT_D_S,
      Ops.CVT_D_W, Ops.CVT_S_D, Ops.CVT_S_W, Ops.CVT_W_D, Ops.CVT_W_S, Ops.DI, Ops.DIV_D,
      Ops.DIV_S, Ops.EI, Ops.ERET, Ops.EXT, Ops.FLOOR_W_D, Ops.FLOOR_W_S, Ops.INS, Ops.J,
      Ops.JAL, Ops.JALR, Ops.JALR_HB, Ops.LB, Ops.LBU, Ops.LDC1, Ops.LH, Ops.LHU,
      Ops.LW, Ops.LWC1, Ops.MFC0, Ops.MFC1, Ops.MFHC1, Ops.MOV_D, Ops.MOV_S, Ops.MTC0, Ops.MTC1,
      Ops.MTHC1, Ops.MUL_D, Ops.MUL_S, Ops.NAL, Ops.NEG_D, Ops.NEG_S, Ops.NOR, Ops.OR, Ops.ORI,
      Ops.PAUSE, Ops.PREF, Ops.RDPGPR, Ops.RECIP_D, Ops.RECIP_S, Ops.ROTR, Ops.ROTRV,
      Ops.ROUND_W_D, Ops.ROUND_W_S, Ops.RSQRT_D, Ops.RSQRT_S, Ops.SB, Ops.SDC1, Ops.SEB,
      Ops.SEH, Ops.SH, Ops.SLL, Ops.SLLV, Ops.SLT, Ops.SLTI, Ops.SLTIU, Ops.SLTU, Ops.SQRT_D,
      Ops.SQRT_S, Ops.SRA, Ops.SRAV, Ops.SRL, Ops.SRLV, Ops.SUB, Ops.SUBU, Ops.SUB_D, Ops.SUB_S,
      Ops.SW, Ops.SWC1, Ops.SYNC, Ops.SYNCI, Ops.SYSCALL, Ops.TEQ, Ops.TGE, Ops.TGEU, Ops.TLT,
      Ops.TLTU, Ops.TNE, Ops.TRUNC_W_D, Ops.TRUNC_W_S, Ops.WAIT, Ops.WRPGPR, Ops.WSBH, Ops.XOR,
      Ops.XORI, Ops.ERETNC, Ops.SIGRIE, Ops.CACHE,
      Ops.MUL, Ops.MUH, Ops.MULU, Ops.MUHU, Ops.SELEQZ, Ops.SELNEZ, Ops.LSA, Ops.ALIGN, Ops.BITSWAP,
      Ops.ADDIUPC, Ops.AUIPC, Ops.ALUIPC, Ops.LWPC, bind, PC,
      Ops.ROUND_L_S, Ops.ROUND_L_D, Ops.TRUNC_L_S, Ops.TRUNC_L_D, Ops.CEIL_L_S, Ops.CEIL_L_D,
      Ops.FLOOR_L_S, Ops.FLOOR_L_D, Ops.CVT_L_S, Ops.CVT_L_D, Ops.CVT_S_L, Ops.CVT_D_L,
      -- the compact branches
      Ops.BC, Ops.BALC, Ops.BEQC, Ops.BNEC, Ops.BLTC, Ops.BGEC, Ops.BLTUC, Ops.BGEUC, Ops.BLEZC,
      Ops.BGEZC, Ops.BGTZC, Ops.BLTZC, Ops.BEQZC, Ops.BNEZC, Ops.BOVC, Ops.BNVC, Ops.JIC, Ops.JIALC,
      Ops.BLEZALC, Ops.BGEZALC, Ops.BGTZALC, Ops.BLTZALC, Ops.BEQZALC, Ops.BNEZALC, Ops.BZALC,
      Ops.CompactIf, Ops.ForbiddenSlot, Ops.SumOverflow,
      -- the 64-bit FP results and the FP branches (the 32-bit results are rows)
      Ops.CMP_D, Ops.BC1EQZ, Ops.BC1NEZ, Ops.SEL_D, Ops.SELEQZ_D, Ops.SELNEZ_D, Ops.MADDF_D,
      Ops.MINMAX_D, Ops.CLASS_D, Ops.RINT_D])

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- **The Operation does not depend on the oracle where `ConsultsOracle` is `false`.** -/
theorem operation_choiceFree (ins : Instruction) (a : Arch) (h : ConsultsOracle ins a = false)
    (i : Impl) (o₁ o₂ : Oracle) :
    (Operation ins).map (fun p => p.run (ctxOf i o₁) { arch := a }) =
      (Operation ins).map (fun p => p.run (ctxOf i o₂) { arch := a }) := by
  cases ins <;> simp only [Operation, Option.map_some, Option.some.injEq, Pseudo.run]
  case rdhwr rt rd sel =>
    simp only [Ops.RDHWR]; ofree
    all_goals (generalize BitVec.toNat rd = n; split <;> rfl)
  -- The Operations that read an oracle field away from their rows (memory: `loadClearsLL` /
  -- `storeClearsLL` while `LLbit = 0`; `CVT.D.S` away from a quiet NaN; the UNPREDICTABLE operands
  -- of `MFC0`/`MTC0`, `EXT`/`INS`, `JALR`, the compact branches): unfold, split and rewrite (`ofree`).
  case lw | sw | lb | lbu | lh | lhu | sb | sh | swc1 | ldc1 | sdc1 | lwpc | mfc0 | mtc0 | mfhc1
    | mthc1 | jalr | jalrHb | ext | ins | addD | subD | mulD | divD | sqrtD | absD | movD | negD
    | recipD | rsqrtD | cvtDS | cvtDW | blezalc | bgezalc | bgtzalc | bltzalc | beqzalc | bnezalc
    | bc | balc | beqc | bnec | bltc | bgec | bltuc | bgeuc | blezc | bgezc | bgtzc | bltzc | beqzc
    | bnezc | bovc | bnvc | jic | jialc =>
    cf_pre h; unfold_ops; ofree
  -- The constructors with their own `cf_<ctor>` (LL/SC, CFC1/CTC1, the divisions) use it. Every other
  -- one is a row (`h` is `true = false`: the 32-bit FPR results) or definitional (`rfl`), or else
  -- one generic unfolding.
  all_goals apply_ctor_lemma "cf_" "" at h else first
    | (cases h; done)
    | rfl
    | (unfold_ops; ofree)

end Refine
