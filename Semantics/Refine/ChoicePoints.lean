import Semantics.Refine.Step

/-!
# Refine.ChoicePoints — the Operations are oracle-free where `ConsultsOracle` says so (wave 8)

`operation_choiceFree`: when `Manual.ConsultsOracle ins a = false`, the Operation of `ins` run from `a`
gives the same result (value, exception and state) under any two oracles. For the 113 constructors
whose Operation reads no oracle field this is definitional (`rfl`); for the 70 that read one
(`cf_<ctor>`) the proof splits on the conditions the Operation tests (`case_ite`), rewrites the
oracle-reading primitives to their oracle-free form under the hypotheses (`LoadMemory_free`,
`StoreMemory_free` while `LLbit = 0`, `ValueFPR64_even`/`StoreFPR64_even` for even registers,
`signOpS_free`/`cvtDS_free`/... away from a quiet NaN), and closes with `rfl`. `LL` and `SC` set
`LLbit` after their memory access, so their `loadClearsLL`/`storeClearsLL` choice never shows
(`LoadMemory_any`, `StoreMemory_any`). `NMADD`/`NMSUB` test the sum computed after the product's
`FPResult`, which leaves the FP environment unchanged (`env_fpResult`).
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

theorem ValueFPR64_even (fpr : Fin 32) (c : Ctx) (f : Frame) (h : bit (BitVec.ofNat 5 fpr.val) 0 = false) :
    ValueFPR64 fpr c f = (.ok (f.arch.FPR (fpr + 1) ++ f.arch.FPR fpr), f) := by
  simp only [ValueFPR64, h, FP32RegistersMode]; rfl

theorem StoreFPR64_even (fpr : Fin 32) (v : BitVec 64) (c : Ctx) (f : Frame)
    (h : bit (BitVec.ofNat 5 fpr.val) 0 = false) :
    StoreFPR64 fpr v c f = (.ok (), { f with arch := { f.arch with
      FPR := update (update f.arch.FPR fpr (v.extractLsb' 0 32)) (fpr + 1) (v.extractLsb' 32 32) } }) := by
  simp only [StoreFPR64, h]; rfl

/-- `signOpS` without its QNaN arm. -/
def signOpSFree (g : W32 → W32) (x : W32) : W32 × Mips.Fp.Flags :=
  if Mips.Fp.isSNaN32 x then (Mips.Fp.defaultQNaN32, Mips.Fp.Flags.invalidOnly) else (g x, Mips.Fp.Flags.none)
def signOpDFree (g : BitVec 64 → BitVec 64) (x : BitVec 64) : BitVec 64 × Mips.Fp.Flags :=
  if Mips.Fp.isSNaN64 x then (Mips.Fp.defaultQNaN64, Mips.Fp.Flags.invalidOnly) else (g x, Mips.Fp.Flags.none)

theorem signOpS_free (r : AbsNegNaN) (g : W32 → W32) (x : W32) (h : Mips.Fp.isQNaN32 x = false) :
    IEEE.signOpS r g x = signOpSFree g x := by
  simp only [IEEE.signOpS, signOpSFree, h, Bool.false_eq_true, ite_false]
theorem signOpD_free (r : AbsNegNaN) (g : BitVec 64 → BitVec 64) (x : BitVec 64)
    (h : Mips.Fp.isQNaN64 x = false) :
    IEEE.signOpD r g x = signOpDFree g x := by
  simp only [IEEE.signOpD, signOpDFree, h, Bool.false_eq_true, ite_false]
theorem cvtDS_free (q : W32 → BitVec 64) (x : W32) (h : Mips.Fp.isQNaN32 x = false) :
    IEEE.cvtDS q x = Mips.Fp.f32ToF64 x := by simp only [IEEE.cvtDS, h, Bool.false_eq_true, ite_false]
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
    ite_app2, Pseudo.oracle, Pseudo.impl, SignalException, LoadMemory_free, StoreMemory_free, ValueFPR64_even,
    StoreFPR64_even, IEEE.absS, IEEE.negS, IEEE.absD, IEEE.negD, signOpS_free, signOpD_free, cvtDS_free,
    cvtSD_free, ValueFPR32, StoreFPR32, Pseudo.modify, *, ↓reduceIte, Bool.false_eq_true, not_false_eq_true,
    OddFPR, FPRPair, FPResult, CheckFPException, FPConditionCode,
    addS_fpResult, subS_fpResult, addD_fpResult, subD_fpResult, ctxOf])

macro "cf_pre" h:ident : tactic => `(tactic| (
  (try simp only [ConsultsOracle, Bool.or_eq_false_iff, OddFPR, FPRPair,
    Bool.not_eq_false', decide_eq_false_iff_not, FPCC] at $h:ident)
  repeat (obtain ⟨_, $h:ident⟩ := $h:ident)))

macro "ofree_all" : tactic => `(tactic| (
  (try simp_all only [bind, GPR, Pseudo.get, AddressTranslation, setGPR, pure,
    ite_app2, Pseudo.oracle, Pseudo.impl, SignalException, LoadMemory_free, StoreMemory_free, ValueFPR64_even,
    StoreFPR64_even, IEEE.absS, IEEE.negS, IEEE.absD, IEEE.negD, signOpS_free, signOpD_free, cvtDS_free,
    cvtSD_free, ValueFPR32, StoreFPR32, Pseudo.modify, ↓reduceIte, Bool.false_eq_true, not_false_eq_true,
    OddFPR, FPRPair, FPResult, CheckFPException, FPConditionCode,
    addS_fpResult, subS_fpResult, addD_fpResult, subD_fpResult, ctxOf, CTC1Unpredictable, Bool.and_true, Bool.true_and, Bool.and_false,
    Bool.false_and, bne_eq_false_iff_eq, writeGPR, Bool.or_false, Bool.not_false, Bool.not_true,
    Bool.true_eq_false, Bool.or_true])
  repeat' (first | rfl | (case_ite <;> (try simp_all only [bind, GPR, Pseudo.get, AddressTranslation, setGPR, pure,
    ite_app2, Pseudo.oracle, Pseudo.impl, SignalException, LoadMemory_free, StoreMemory_free, ValueFPR64_even,
    StoreFPR64_even, IEEE.absS, IEEE.negS, IEEE.absD, IEEE.negD, signOpS_free, signOpD_free, cvtDS_free,
    cvtSD_free, ValueFPR32, StoreFPR32, Pseudo.modify, ↓reduceIte, Bool.false_eq_true, not_false_eq_true,
    OddFPR, FPRPair, FPResult, CheckFPException, FPConditionCode,
    addS_fpResult, subS_fpResult, addD_fpResult, subD_fpResult, ctxOf, CTC1Unpredictable, Bool.and_true,
    Bool.true_and, Bool.and_false, Bool.false_and, bne_eq_false_iff_eq, writeGPR, Bool.or_false, Bool.not_false, Bool.not_true,
    Bool.true_eq_false, Bool.or_true])))))

macro "ofree_ll" : tactic => `(tactic| (
  (try simp_all only [bind, GPR, Pseudo.get, AddressTranslation, setGPR, pure,
    ite_app2, Pseudo.oracle, Pseudo.impl, SignalException, LoadMemory_any, StoreMemory_any, ValueFPR64_even,
    StoreFPR64_even, IEEE.absS, IEEE.negS, IEEE.absD, IEEE.negD, signOpS_free, signOpD_free, cvtDS_free,
    cvtSD_free, ValueFPR32, StoreFPR32, Pseudo.modify, ↓reduceIte, Bool.false_eq_true, not_false_eq_true,
    OddFPR, FPRPair, FPResult, CheckFPException, FPConditionCode,
    addS_fpResult, subS_fpResult, addD_fpResult, subD_fpResult, ctxOf, CTC1Unpredictable, Bool.and_true, Bool.true_and, Bool.and_false,
    Bool.false_and, bne_eq_false_iff_eq, writeGPR, Bool.or_false, Bool.not_false, Bool.not_true,
    Bool.true_eq_false, Bool.or_true])
  repeat' (first | rfl | (case_ite <;> (try simp_all only [bind, GPR, Pseudo.get, AddressTranslation, setGPR, pure,
    ite_app2, Pseudo.oracle, Pseudo.impl, SignalException, LoadMemory_any, StoreMemory_any, ValueFPR64_even,
    StoreFPR64_even, IEEE.absS, IEEE.negS, IEEE.absD, IEEE.negD, signOpS_free, signOpD_free, cvtDS_free,
    cvtSD_free, ValueFPR32, StoreFPR32, Pseudo.modify, ↓reduceIte, Bool.false_eq_true, not_false_eq_true,
    OddFPR, FPRPair, FPResult, CheckFPException, FPConditionCode,
    addS_fpResult, subS_fpResult, addD_fpResult, subD_fpResult, ctxOf, CTC1Unpredictable, Bool.and_true,
    Bool.true_and, Bool.and_false, Bool.false_and, bne_eq_false_iff_eq, writeGPR, Bool.or_false, Bool.not_false, Bool.not_true,
    Bool.true_eq_false, Bool.or_true])))))

macro "ofree" : tactic => `(tactic| (
  (try ofree_simp)
  repeat' (first | with_reducible rfl | (case_ite <;> (try ofree_simp)) | rfl)))

theorem cf_lw (base rt off : W32) (a : Arch) (h : ConsultsOracle (.lw base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.LW base rt off (ctxOf i o₁) { arch := a } = Ops.LW base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.LW]; ofree

theorem cf_sw (base rt off : W32) (a : Arch) (h : ConsultsOracle (.sw base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.SW base rt off (ctxOf i o₁) { arch := a } = Ops.SW base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.SW]; ofree

theorem cf_lwl (base rt off : W32) (a : Arch) (h : ConsultsOracle (.lwl base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.LWL base rt off (ctxOf i o₁) { arch := a } = Ops.LWL base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.LWL]; ofree

theorem cf_mtc0 (rt rd sel : W32) (a : Arch) (h : ConsultsOracle (.mtc0 rt rd sel) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MTC0 rt rd sel (ctxOf i o₁) { arch := a } = Ops.MTC0 rt rd sel (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.MTC0]; ofree

theorem cf_bltzal (rs off : W32) (a : Arch) (h : ConsultsOracle (.bltzal rs off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.BLTZAL rs off (ctxOf i o₁) { arch := a } = Ops.BLTZAL rs off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.BLTZAL]; ofree

theorem cf_bgezal (rs off : W32) (a : Arch) (h : ConsultsOracle (.bgezal rs off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.BGEZAL rs off (ctxOf i o₁) { arch := a } = Ops.BGEZAL rs off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.BGEZAL]; ofree

theorem cf_bltzall (rs off : W32) (a : Arch) (h : ConsultsOracle (.bltzall rs off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.BLTZALL rs off (ctxOf i o₁) { arch := a } = Ops.BLTZALL rs off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.BLTZALL]; ofree

theorem cf_bgezall (rs off : W32) (a : Arch) (h : ConsultsOracle (.bgezall rs off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.BGEZALL rs off (ctxOf i o₁) { arch := a } = Ops.BGEZALL rs off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.BGEZALL]; ofree

theorem cf_jalr (rs rd : W32) (a : Arch) (h : ConsultsOracle (.jalr rs rd) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.JALR rs rd (ctxOf i o₁) { arch := a } = Ops.JALR rs rd (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.JALR]; ofree

theorem cf_jalrHb (rs rd : W32) (a : Arch) (h : ConsultsOracle (.jalrHb rs rd) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.JALR_HB rs rd (ctxOf i o₁) { arch := a } = Ops.JALR_HB rs rd (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.JALR_HB]; ofree

theorem cf_mfc0 (rt rd sel : W32) (a : Arch) (h : ConsultsOracle (.mfc0 rt rd sel) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MFC0 rt rd sel (ctxOf i o₁) { arch := a } = Ops.MFC0 rt rd sel (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.MFC0]; ofree

theorem cf_lb (base rt off : W32) (a : Arch) (h : ConsultsOracle (.lb base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.LB base rt off (ctxOf i o₁) { arch := a } = Ops.LB base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.LB]; ofree

theorem cf_lbu (base rt off : W32) (a : Arch) (h : ConsultsOracle (.lbu base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.LBU base rt off (ctxOf i o₁) { arch := a } = Ops.LBU base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.LBU]; ofree

theorem cf_lh (base rt off : W32) (a : Arch) (h : ConsultsOracle (.lh base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.LH base rt off (ctxOf i o₁) { arch := a } = Ops.LH base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.LH]; ofree

theorem cf_lhu (base rt off : W32) (a : Arch) (h : ConsultsOracle (.lhu base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.LHU base rt off (ctxOf i o₁) { arch := a } = Ops.LHU base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.LHU]; ofree

theorem cf_sb (base rt off : W32) (a : Arch) (h : ConsultsOracle (.sb base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.SB base rt off (ctxOf i o₁) { arch := a } = Ops.SB base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.SB]; ofree

theorem cf_sh (base rt off : W32) (a : Arch) (h : ConsultsOracle (.sh base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.SH base rt off (ctxOf i o₁) { arch := a } = Ops.SH base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.SH]; ofree

theorem cf_ll (base rt off : W32) (a : Arch) (h : ConsultsOracle (.ll base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.LL base rt off (ctxOf i o₁) { arch := a } = Ops.LL base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.LL]; ofree_ll

theorem cf_sc (base rt off : W32) (a : Arch) (h : ConsultsOracle (.sc base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.SC base rt off (ctxOf i o₁) { arch := a } = Ops.SC base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.SC]; ofree_ll

theorem cf_lwr (base rt off : W32) (a : Arch) (h : ConsultsOracle (.lwr base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.LWR base rt off (ctxOf i o₁) { arch := a } = Ops.LWR base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.LWR]; ofree

theorem cf_swl (base rt off : W32) (a : Arch) (h : ConsultsOracle (.swl base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.SWL base rt off (ctxOf i o₁) { arch := a } = Ops.SWL base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.SWL]; ofree

theorem cf_swr (base rt off : W32) (a : Arch) (h : ConsultsOracle (.swr base rt off) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.SWR base rt off (ctxOf i o₁) { arch := a } = Ops.SWR base rt off (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.SWR]; ofree

theorem cf_mfhc1 (rt fs : W32) (a : Arch) (h : ConsultsOracle (.mfhc1 rt fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MFHC1 rt fs (ctxOf i o₁) { arch := a } = Ops.MFHC1 rt fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.MFHC1]; ofree

theorem cf_mthc1 (rt fs : W32) (a : Arch) (h : ConsultsOracle (.mthc1 rt fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MTHC1 rt fs (ctxOf i o₁) { arch := a } = Ops.MTHC1 rt fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.MTHC1]; ofree

theorem cf_cfc1 (rt fs : W32) (a : Arch) (h : ConsultsOracle (.cfc1 rt fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.CFC1 rt fs (ctxOf i o₁) { arch := a } = Ops.CFC1 rt fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.CFC1]; ofree_all

theorem cf_ctc1 (rt fs : W32) (a : Arch) (h : ConsultsOracle (.ctc1 rt fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.CTC1 rt fs (ctxOf i o₁) { arch := a } = Ops.CTC1 rt fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.CTC1]; ofree_all

theorem cf_lwc1 (rs ft imm : W32) (a : Arch) (h : ConsultsOracle (.lwc1 rs ft imm) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.LWC1 rs ft imm (ctxOf i o₁) { arch := a } = Ops.LWC1 rs ft imm (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.LWC1]; ofree

theorem cf_swc1 (rs ft imm : W32) (a : Arch) (h : ConsultsOracle (.swc1 rs ft imm) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.SWC1 rs ft imm (ctxOf i o₁) { arch := a } = Ops.SWC1 rs ft imm (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.SWC1]; ofree

theorem cf_ldc1 (rs ft imm : W32) (a : Arch) (h : ConsultsOracle (.ldc1 rs ft imm) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.LDC1 rs ft imm (ctxOf i o₁) { arch := a } = Ops.LDC1 rs ft imm (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.LDC1]; ofree

theorem cf_sdc1 (rs ft imm : W32) (a : Arch) (h : ConsultsOracle (.sdc1 rs ft imm) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.SDC1 rs ft imm (ctxOf i o₁) { arch := a } = Ops.SDC1 rs ft imm (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.SDC1]; ofree

theorem cf_lwxc1 (fd index base : W32) (a : Arch) (h : ConsultsOracle (.lwxc1 fd index base) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.LWXC1 fd index base (ctxOf i o₁) { arch := a } = Ops.LWXC1 fd index base (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.LWXC1]; ofree

theorem cf_ldxc1 (fd index base : W32) (a : Arch) (h : ConsultsOracle (.ldxc1 fd index base) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.LDXC1 fd index base (ctxOf i o₁) { arch := a } = Ops.LDXC1 fd index base (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.LDXC1]; ofree

theorem cf_swxc1 (fs index base : W32) (a : Arch) (h : ConsultsOracle (.swxc1 fs index base) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.SWXC1 fs index base (ctxOf i o₁) { arch := a } = Ops.SWXC1 fs index base (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.SWXC1]; ofree

theorem cf_sdxc1 (fs index base : W32) (a : Arch) (h : ConsultsOracle (.sdxc1 fs index base) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.SDXC1 fs index base (ctxOf i o₁) { arch := a } = Ops.SDXC1 fs index base (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.SDXC1]; ofree

theorem cf_absS (fd fs : W32) (a : Arch) (h : ConsultsOracle (.absS fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.ABS_S fd fs (ctxOf i o₁) { arch := a } = Ops.ABS_S fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.ABS_S]; ofree

theorem cf_negS (fd fs : W32) (a : Arch) (h : ConsultsOracle (.negS fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.NEG_S fd fs (ctxOf i o₁) { arch := a } = Ops.NEG_S fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.NEG_S]; ofree

theorem cf_addD (fd fs ft : W32) (a : Arch) (h : ConsultsOracle (.addD fd fs ft) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.ADD_D fd fs ft (ctxOf i o₁) { arch := a } = Ops.ADD_D fd fs ft (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.ADD_D]; ofree

theorem cf_subD (fd fs ft : W32) (a : Arch) (h : ConsultsOracle (.subD fd fs ft) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.SUB_D fd fs ft (ctxOf i o₁) { arch := a } = Ops.SUB_D fd fs ft (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.SUB_D]; ofree

theorem cf_mulD (fd fs ft : W32) (a : Arch) (h : ConsultsOracle (.mulD fd fs ft) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MUL_D fd fs ft (ctxOf i o₁) { arch := a } = Ops.MUL_D fd fs ft (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.MUL_D]; ofree

theorem cf_divD (fd fs ft : W32) (a : Arch) (h : ConsultsOracle (.divD fd fs ft) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.DIV_D fd fs ft (ctxOf i o₁) { arch := a } = Ops.DIV_D fd fs ft (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.DIV_D]; ofree

theorem cf_sqrtD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.sqrtD fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.SQRT_D fd fs (ctxOf i o₁) { arch := a } = Ops.SQRT_D fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.SQRT_D]; ofree

theorem cf_absD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.absD fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.ABS_D fd fs (ctxOf i o₁) { arch := a } = Ops.ABS_D fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.ABS_D]; ofree

theorem cf_movD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.movD fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MOV_D fd fs (ctxOf i o₁) { arch := a } = Ops.MOV_D fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.MOV_D]; ofree

theorem cf_negD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.negD fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.NEG_D fd fs (ctxOf i o₁) { arch := a } = Ops.NEG_D fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.NEG_D]; ofree

theorem cf_recipD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.recipD fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.RECIP_D fd fs (ctxOf i o₁) { arch := a } = Ops.RECIP_D fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.RECIP_D]; ofree

theorem cf_rsqrtD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.rsqrtD fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.RSQRT_D fd fs (ctxOf i o₁) { arch := a } = Ops.RSQRT_D fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.RSQRT_D]; ofree

theorem cf_roundWD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.roundWD fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.ROUND_W_D fd fs (ctxOf i o₁) { arch := a } = Ops.ROUND_W_D fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.ROUND_W_D]; ofree

theorem cf_truncWD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.truncWD fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.TRUNC_W_D fd fs (ctxOf i o₁) { arch := a } = Ops.TRUNC_W_D fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.TRUNC_W_D]; ofree

theorem cf_ceilWD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.ceilWD fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.CEIL_W_D fd fs (ctxOf i o₁) { arch := a } = Ops.CEIL_W_D fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.CEIL_W_D]; ofree

theorem cf_floorWD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.floorWD fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.FLOOR_W_D fd fs (ctxOf i o₁) { arch := a } = Ops.FLOOR_W_D fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.FLOOR_W_D]; ofree

theorem cf_cvtWD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.cvtWD fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.CVT_W_D fd fs (ctxOf i o₁) { arch := a } = Ops.CVT_W_D fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.CVT_W_D]; ofree

theorem cf_cvtDS (fd fs : W32) (a : Arch) (h : ConsultsOracle (.cvtDS fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.CVT_D_S fd fs (ctxOf i o₁) { arch := a } = Ops.CVT_D_S fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.CVT_D_S]; ofree

theorem cf_cvtDW (fd fs : W32) (a : Arch) (h : ConsultsOracle (.cvtDW fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.CVT_D_W fd fs (ctxOf i o₁) { arch := a } = Ops.CVT_D_W fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.CVT_D_W]; ofree

theorem cf_cvtSD (fd fs : W32) (a : Arch) (h : ConsultsOracle (.cvtSD fd fs) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.CVT_S_D fd fs (ctxOf i o₁) { arch := a } = Ops.CVT_S_D fd fs (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.CVT_S_D]; ofree

theorem cf_cCondD (cond cc fs ft : W32) (a : Arch) (h : ConsultsOracle (.cCondD cond cc fs ft) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.C_cond_D cond cc fs ft (ctxOf i o₁) { arch := a } = Ops.C_cond_D cond cc fs ft (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.C_cond_D]; ofree

theorem cf_movfD (fd fs cc : W32) (a : Arch) (h : ConsultsOracle (.movfD fd fs cc) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MOVF_D fd fs cc (ctxOf i o₁) { arch := a } = Ops.MOVF_D fd fs cc (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.MOVF_D]; ofree_all

theorem cf_movtD (fd fs cc : W32) (a : Arch) (h : ConsultsOracle (.movtD fd fs cc) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MOVT_D fd fs cc (ctxOf i o₁) { arch := a } = Ops.MOVT_D fd fs cc (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.MOVT_D]; ofree_all

theorem cf_movnD (fd fs rt : W32) (a : Arch) (h : ConsultsOracle (.movnD fd fs rt) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MOVN_D fd fs rt (ctxOf i o₁) { arch := a } = Ops.MOVN_D fd fs rt (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.MOVN_D]; ofree_all

theorem cf_movzD (fd fs rt : W32) (a : Arch) (h : ConsultsOracle (.movzD fd fs rt) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MOVZ_D fd fs rt (ctxOf i o₁) { arch := a } = Ops.MOVZ_D fd fs rt (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.MOVZ_D]; ofree_all

theorem cf_maddD (fd fr fs ft : W32) (a : Arch) (h : ConsultsOracle (.maddD fd fr fs ft) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MADD_D fd fr fs ft (ctxOf i o₁) { arch := a } = Ops.MADD_D fd fr fs ft (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.MADD_D]; ofree

theorem cf_msubD (fd fr fs ft : W32) (a : Arch) (h : ConsultsOracle (.msubD fd fr fs ft) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MSUB_D fd fr fs ft (ctxOf i o₁) { arch := a } = Ops.MSUB_D fd fr fs ft (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.MSUB_D]; ofree

theorem cf_nmaddS (fd fr fs ft : W32) (a : Arch) (h : ConsultsOracle (.nmaddS fd fr fs ft) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.NMADD_S fd fr fs ft (ctxOf i o₁) { arch := a } = Ops.NMADD_S fd fr fs ft (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.NMADD_S]; ofree

theorem cf_nmaddD (fd fr fs ft : W32) (a : Arch) (h : ConsultsOracle (.nmaddD fd fr fs ft) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.NMADD_D fd fr fs ft (ctxOf i o₁) { arch := a } = Ops.NMADD_D fd fr fs ft (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.NMADD_D]; ofree

theorem cf_nmsubS (fd fr fs ft : W32) (a : Arch) (h : ConsultsOracle (.nmsubS fd fr fs ft) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.NMSUB_S fd fr fs ft (ctxOf i o₁) { arch := a } = Ops.NMSUB_S fd fr fs ft (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.NMSUB_S]; ofree

theorem cf_nmsubD (fd fr fs ft : W32) (a : Arch) (h : ConsultsOracle (.nmsubD fd fr fs ft) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.NMSUB_D fd fr fs ft (ctxOf i o₁) { arch := a } = Ops.NMSUB_D fd fr fs ft (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.NMSUB_D]; ofree

theorem cf_div (rs rt : W32) (a : Arch) (h : ConsultsOracle (.div rs rt) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.DIV rs rt (ctxOf i o₁) { arch := a } = Ops.DIV rs rt (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.DIV]; ofree

theorem cf_divu (rs rt : W32) (a : Arch) (h : ConsultsOracle (.divu rs rt) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.DIVU rs rt (ctxOf i o₁) { arch := a } = Ops.DIVU rs rt (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.DIVU]; ofree

theorem cf_mul (rs rt rd : W32) (a : Arch) (h : ConsultsOracle (.mul rs rt rd) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.MUL rs rt rd (ctxOf i o₁) { arch := a } = Ops.MUL rs rt rd (ctxOf i o₂) { arch := a } := by
  cf_pre h

theorem cf_ext (rt rs pos size : W32) (a : Arch) (h : ConsultsOracle (.ext rt rs pos size) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.EXT rt rs pos size (ctxOf i o₁) { arch := a } = Ops.EXT rt rs pos size (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.EXT]; ofree

theorem cf_ins (rt rs pos size : W32) (a : Arch) (h : ConsultsOracle (.ins rt rs pos size) a = false) (i : Impl) (o₁ o₂ : Oracle) :
    Ops.INS rt rs pos size (ctxOf i o₁) { arch := a } = Ops.INS rt rs pos size (ctxOf i o₂) { arch := a } := by
  cf_pre h; simp only [Ops.INS]; ofree


set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- **The Operation does not depend on the oracle where `ConsultsOracle` is `false`.** -/
theorem operation_choiceFree (ins : Instruction) (a : Arch) (h : ConsultsOracle ins a = false)
    (i : Impl) (o₁ o₂ : Oracle) :
    (Operation ins).map (fun p => p.run (ctxOf i o₁) { arch := a }) =
      (Operation ins).map (fun p => p.run (ctxOf i o₂) { arch := a }) := by
  cases ins <;> simp only [Operation, Option.map_some, Option.some.injEq, Pseudo.run]
  case lw base rt off => exact cf_lw base rt off a h i o₁ o₂
  case sw base rt off => exact cf_sw base rt off a h i o₁ o₂
  case lwl base rt off => exact cf_lwl base rt off a h i o₁ o₂
  case mtc0 rt rd sel => exact cf_mtc0 rt rd sel a h i o₁ o₂
  case bltzal rs off => exact cf_bltzal rs off a h i o₁ o₂
  case bgezal rs off => exact cf_bgezal rs off a h i o₁ o₂
  case bltzall rs off => exact cf_bltzall rs off a h i o₁ o₂
  case bgezall rs off => exact cf_bgezall rs off a h i o₁ o₂
  case jalr rs rd => exact cf_jalr rs rd a h i o₁ o₂
  case jalrHb rs rd => exact cf_jalrHb rs rd a h i o₁ o₂
  case mfc0 rt rd sel => exact cf_mfc0 rt rd sel a h i o₁ o₂
  case lb base rt off => exact cf_lb base rt off a h i o₁ o₂
  case lbu base rt off => exact cf_lbu base rt off a h i o₁ o₂
  case lh base rt off => exact cf_lh base rt off a h i o₁ o₂
  case lhu base rt off => exact cf_lhu base rt off a h i o₁ o₂
  case sb base rt off => exact cf_sb base rt off a h i o₁ o₂
  case sh base rt off => exact cf_sh base rt off a h i o₁ o₂
  case ll base rt off => exact cf_ll base rt off a h i o₁ o₂
  case sc base rt off => exact cf_sc base rt off a h i o₁ o₂
  case lwr base rt off => exact cf_lwr base rt off a h i o₁ o₂
  case swl base rt off => exact cf_swl base rt off a h i o₁ o₂
  case swr base rt off => exact cf_swr base rt off a h i o₁ o₂
  case mfhc1 rt fs => exact cf_mfhc1 rt fs a h i o₁ o₂
  case mthc1 rt fs => exact cf_mthc1 rt fs a h i o₁ o₂
  case cfc1 rt fs => exact cf_cfc1 rt fs a h i o₁ o₂
  case ctc1 rt fs => exact cf_ctc1 rt fs a h i o₁ o₂
  case lwc1 rs ft imm => exact cf_lwc1 rs ft imm a h i o₁ o₂
  case swc1 rs ft imm => exact cf_swc1 rs ft imm a h i o₁ o₂
  case ldc1 rs ft imm => exact cf_ldc1 rs ft imm a h i o₁ o₂
  case sdc1 rs ft imm => exact cf_sdc1 rs ft imm a h i o₁ o₂
  case lwxc1 fd index base => exact cf_lwxc1 fd index base a h i o₁ o₂
  case ldxc1 fd index base => exact cf_ldxc1 fd index base a h i o₁ o₂
  case swxc1 fs index base => exact cf_swxc1 fs index base a h i o₁ o₂
  case sdxc1 fs index base => exact cf_sdxc1 fs index base a h i o₁ o₂
  case absS fd fs => exact cf_absS fd fs a h i o₁ o₂
  case negS fd fs => exact cf_negS fd fs a h i o₁ o₂
  case addD fd fs ft => exact cf_addD fd fs ft a h i o₁ o₂
  case subD fd fs ft => exact cf_subD fd fs ft a h i o₁ o₂
  case mulD fd fs ft => exact cf_mulD fd fs ft a h i o₁ o₂
  case divD fd fs ft => exact cf_divD fd fs ft a h i o₁ o₂
  case sqrtD fd fs => exact cf_sqrtD fd fs a h i o₁ o₂
  case absD fd fs => exact cf_absD fd fs a h i o₁ o₂
  case movD fd fs => exact cf_movD fd fs a h i o₁ o₂
  case negD fd fs => exact cf_negD fd fs a h i o₁ o₂
  case recipD fd fs => exact cf_recipD fd fs a h i o₁ o₂
  case rsqrtD fd fs => exact cf_rsqrtD fd fs a h i o₁ o₂
  case roundWD fd fs => exact cf_roundWD fd fs a h i o₁ o₂
  case truncWD fd fs => exact cf_truncWD fd fs a h i o₁ o₂
  case ceilWD fd fs => exact cf_ceilWD fd fs a h i o₁ o₂
  case floorWD fd fs => exact cf_floorWD fd fs a h i o₁ o₂
  case cvtWD fd fs => exact cf_cvtWD fd fs a h i o₁ o₂
  case cvtDS fd fs => exact cf_cvtDS fd fs a h i o₁ o₂
  case cvtDW fd fs => exact cf_cvtDW fd fs a h i o₁ o₂
  case cvtSD fd fs => exact cf_cvtSD fd fs a h i o₁ o₂
  case cCondD cond cc fs ft => exact cf_cCondD cond cc fs ft a h i o₁ o₂
  case movfD fd fs cc => exact cf_movfD fd fs cc a h i o₁ o₂
  case movtD fd fs cc => exact cf_movtD fd fs cc a h i o₁ o₂
  case movnD fd fs rt => exact cf_movnD fd fs rt a h i o₁ o₂
  case movzD fd fs rt => exact cf_movzD fd fs rt a h i o₁ o₂
  case maddD fd fr fs ft => exact cf_maddD fd fr fs ft a h i o₁ o₂
  case msubD fd fr fs ft => exact cf_msubD fd fr fs ft a h i o₁ o₂
  case nmaddS fd fr fs ft => exact cf_nmaddS fd fr fs ft a h i o₁ o₂
  case nmaddD fd fr fs ft => exact cf_nmaddD fd fr fs ft a h i o₁ o₂
  case nmsubS fd fr fs ft => exact cf_nmsubS fd fr fs ft a h i o₁ o₂
  case nmsubD fd fr fs ft => exact cf_nmsubD fd fr fs ft a h i o₁ o₂
  case div rs rt => exact cf_div rs rt a h i o₁ o₂
  case divu rs rt => exact cf_divu rs rt a h i o₁ o₂
  case mul rs rt rd => exact cf_mul rs rt rd a h i o₁ o₂
  case ext rt rs pos size => exact cf_ext rt rs pos size a h i o₁ o₂
  case ins rt rs pos size => exact cf_ins rt rs pos size a h i o₁ o₂
  case rdhwr rt rd =>
    simp only [Ops.RDHWR]; ofree
    all_goals (generalize BitVec.toNat rd = n; rcases n with _ | _ | _ | _ | n <;> rfl)
  all_goals first
    | rfl
    | (simp only [
      Ops.ABS_D, Ops.ABS_S, Ops.ADD, Ops.ADDI, Ops.ADDIU, Ops.ADDU, Ops.ADD_D, Ops.ADD_S, Ops.AND,
      Ops.ANDI, Ops.BC1F, Ops.BC1FL, Ops.BC1T, Ops.BC1TL, Ops.BEQ, Ops.BEQL, Ops.BGEZ, Ops.BGEZAL,
      Ops.BGEZALL, Ops.BGEZL, Ops.BGTZ, Ops.BGTZL, Ops.BLEZ, Ops.BLEZL, Ops.BLTZ, Ops.BLTZAL,
      Ops.BLTZALL, Ops.BLTZL, Ops.BNE, Ops.BNEL, Ops.BREAK, Ops.CEIL_W_D, Ops.CEIL_W_S, Ops.CFC1,
      Ops.CLO, Ops.CLZ, Ops.CTC1, Ops.CVT_D_S, Ops.CVT_D_W, Ops.CVT_S_D, Ops.CVT_S_W, Ops.CVT_W_D,
      Ops.CVT_W_S, Ops.C_cond_D, Ops.C_cond_S, Ops.DI, Ops.DIV, Ops.DIVU, Ops.DIV_D, Ops.DIV_S,
      Ops.EI, Ops.ERET, Ops.EXT, Ops.FLOOR_W_D, Ops.FLOOR_W_S, Ops.INS, Ops.J, Ops.JAL, Ops.JALR,
      Ops.JALR_HB, Ops.JR, Ops.JR_HB, Ops.LB, Ops.LBU, Ops.LDC1, Ops.LDXC1, Ops.LH, Ops.LHU, Ops.LL,
      Ops.LUI, Ops.LW, Ops.LWC1, Ops.LWL, Ops.LWR, Ops.LWXC1, Ops.MADD, Ops.MADDU, Ops.MADD_D,
      Ops.MADD_S, Ops.MFC0, Ops.MFC1, Ops.MFHC1, Ops.MFHI, Ops.MFLO, Ops.MOVF, Ops.MOVF_D,
      Ops.MOVF_S, Ops.MOVN, Ops.MOVN_D, Ops.MOVN_S, Ops.MOVT, Ops.MOVT_D, Ops.MOVT_S, Ops.MOVZ,
      Ops.MOVZ_D, Ops.MOVZ_S, Ops.MOV_D, Ops.MOV_S, Ops.MSUB, Ops.MSUBU, Ops.MSUB_D, Ops.MSUB_S,
      Ops.MTC0, Ops.MTC1, Ops.MTHC1, Ops.MTHI, Ops.MTLO, Ops.MUL, Ops.MULT, Ops.MULTU, Ops.MUL_D,
      Ops.MUL_S, Ops.NEG_D, Ops.NEG_S, Ops.NMADD_D, Ops.NMADD_S, Ops.NMSUB_D, Ops.NMSUB_S, Ops.NOR,
      Ops.OR, Ops.ORI, Ops.PREF, Ops.PREFX, Ops.RDHWR, Ops.RDPGPR, Ops.RECIP_D, Ops.RECIP_S,
      Ops.ROTR, Ops.ROTRV, Ops.ROUND_W_D, Ops.ROUND_W_S, Ops.RSQRT_D, Ops.RSQRT_S, Ops.SB, Ops.SC,
      Ops.SDC1, Ops.SDXC1, Ops.SEB, Ops.SEH, Ops.SH, Ops.SLL, Ops.SLLV, Ops.SLT, Ops.SLTI,
      Ops.SLTIU, Ops.SLTU, Ops.SQRT_D, Ops.SQRT_S, Ops.SRA, Ops.SRAV, Ops.SRL, Ops.SRLV, Ops.SUB,
      Ops.SUBU, Ops.SUB_D, Ops.SUB_S, Ops.SW, Ops.SWC1, Ops.SWL, Ops.SWR, Ops.SWXC1, Ops.SYNC,
      Ops.SYNCI, Ops.SYSCALL, Ops.TEQ, Ops.TEQI, Ops.TGE, Ops.TGEI, Ops.TGEIU, Ops.TGEU, Ops.TLT,
      Ops.TLTI, Ops.TLTIU, Ops.TLTU, Ops.TNE, Ops.TNEI, Ops.TRUNC_W_D, Ops.TRUNC_W_S, Ops.WAIT,
      Ops.WRPGPR, Ops.WSBH, Ops.XOR, Ops.XORI]
       ofree)

end Refine
