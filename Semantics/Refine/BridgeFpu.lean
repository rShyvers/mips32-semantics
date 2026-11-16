import Semantics.Refine.Bridge
import Semantics.FpOpsFacts

/-!
# Refine.BridgeFpu — the FPU Operations' building blocks against the model's

Proved once and reused by `Refine/FpuArith.lean`, `Refine/FpuConvert.lean`,
`Refine/FpuCompare.lean` (7C S4a):

* `execute_cop1`: `Execute` of a COP1 instruction (not a CTI) is the Coprocessor Unusable
  exception when `Status.CU1 = 0` and the Operation otherwise, against the model's `execInstr`.
* `runAbs`: the outcome of an Operation run on `abs s` (completion or exception entry).
* **The FCSR bookkeeping** (`FPResult`: Cause, `CheckFPException`, Flags; MD00082 Vol I-A Rev 6.01
  §6.7.1, p.98-99) against the model's `Mips.Fp.fpUpdate`: `runAbs_FPResult` (one operation
  followed by the rest of the Operation, the model's `fpThen`), and its instances `runAbs_finS`
  (`fpFinishS`), `runAbs_finD` (`fpFinishD`); `runAbs_FPCheck` (`FPCheck`, one operation of a
  multiply-add: Cause and trap check only, the model's `fpStep`; Wave 12a).
* `ValueFPR`/`StoreFPR` (R6-5: 64-bit FPRs, `Status.FR = 1`): a double is one FPR (`readFpD`/`writeFpD`);
  a 32-bit store keeps the upper half (the model oracle's `fprUpper`, as `writeFpReg`).
-/

namespace Refine

open Manual

/-! ## The FCSR side of one operation -/

theorem fcsr1_fields (F : W32) (b : BitVec 5) :
    bit ((F &&& ~~~(0x3F#32 <<< 12)) ||| (b.setWidth 32 <<< 12)) 17 = false ∧
    ((F &&& ~~~(0x3F#32 <<< 12)) ||| (b.setWidth 32 <<< 12)).extractLsb' 12 5 = b ∧
    ((F &&& ~~~(0x3F#32 <<< 12)) ||| (b.setWidth 32 <<< 12)).extractLsb' 7 5 = F.extractLsb' 7 5 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [bit]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    rcases i with _|_|_|_|_|i <;> simp <;> omega
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    rcases i with _|_|_|_|_|i <;> simp <;> omega

/-- **`FPResult` in closed form**: Cause written, then the trap check on the new FCSR, then Flags. -/
theorem FPResult_run {α : Type} (r : α × Mips.Fp.Flags) (c : Ctx) (f : Frame) :
    FPResult r c f =
      if (r.2.toBits &&& f.arch.FCSR.extractLsb' 7 5) != 0#5 then
        (.signal .FloatingPoint, { f with arch := { f.arch with FCSR :=
          (f.arch.FCSR &&& ~~~(0x3F#32 <<< 12)) ||| (r.2.toBits.setWidth 32 <<< 12) } })
      else
        (.ok r.1, { f with arch := { f.arch with FCSR :=
          ((f.arch.FCSR &&& ~~~(0x3F#32 <<< 12)) ||| (r.2.toBits.setWidth 32 <<< 12)) |||
            (r.2.toBits.setWidth 32 <<< 2) } }) := by
  obtain ⟨h17, hcause, hen⟩ := fcsr1_fields f.arch.FCSR r.2.toBits
  simp only [FPResult, bind, Pseudo.modify, CheckFPException, Pseudo.get, h17, hcause, hen,
    Bool.false_or]
  cases (r.2.toBits &&& f.arch.FCSR.extractLsb' 7 5 != 0#5) <;> rfl

/-! ## Running an Operation on `abs s` -/

/-- What `Execute` makes of the Operation `op` run on `abs s` with the model's choices. -/
def runAbs (op : Pseudo Unit) (s : State) : Option Arch :=
  match op.run modelCtx { arch := abs s } with
  | (.ok (), f) => some (Complete (abs s) f)
  | (.signal e, f) => some (GeneralExceptionProcessing modelImpl modelOracle e f.arch)

theorem runAbs_congr (op op' : Pseudo Unit) (s : State)
    (h : op modelCtx { arch := abs s } = op' modelCtx { arch := abs s }) :
    runAbs op s = runAbs op' s := by
  unfold runAbs Pseudo.run; rw [h]

/-! The model's choices, by definition. -/

theorem modelCtx_oracle : modelCtx.oracle = modelOracle := rfl
theorem modelCtx_impl : modelCtx.impl = modelImpl := rfl
-- R6-5: the model's upper half of a 32-bit FPR write is the old one.
theorem fprUpper_model (a : Arch) (fpr : Fin 32) :
    modelCtx.oracle.fprUpper a fpr = (a.FPR fpr).extractLsb' 32 32 := rfl
theorem modelImpl_recipS : modelImpl.recipS = Mips.Fp.f32Recip := rfl
theorem modelImpl_recipD : modelImpl.recipD = Mips.Fp.f64Recip := rfl
theorem modelImpl_rsqrtS : modelImpl.rsqrtS = Mips.Fp.f32Rsqrt := rfl
theorem modelImpl_rsqrtD : modelImpl.rsqrtD = Mips.Fp.f64Rsqrt := rfl

theorem execInstr_cop1 (s : State) (i : Instruction) (hb : isBranchLike i = false)
    (hu : usesCop1 i = true) (h0 : usesCop0 i = false) :
    execInstr s i = if (!cu1Enabled s) = true then takeCoprocessorUnusable s else execBody s i := by
  unfold execInstr; rw [hb, hu, h0]; simp only [Bool.true_and, Bool.false_and, Bool.false_eq_true,
    ite_false]

/-- **`Execute` of a COP1 instruction**: Coprocessor Unusable when `Status.CU1 = 0`, else the
Operation; against `execInstr`. -/
theorem execute_cop1 (s : State) (w : W32) (i : Instruction) (op : Pseudo Unit)
    (hcti : IsCTI i = false) (h1 : InCop1Space w = true) (h0 : InCop0Space w = false)
    (hop : Operation i = some op) (hb : isBranchLike i = false) (hu : usesCop1 i = true)
    (hu0 : usesCop0 i = false)
    (hrun : cu1Enabled s = true → runAbs op s = some (abs (execBody s i))) :
    Execute modelCtx w i (abs s) = some (abs (execInstr s i)) := by
  rw [execInstr_cop1 s i hb hu hu0]
  simp only [Execute, Execute.runOperation, hcti, h1, h0, hop, Bool.false_and, Bool.false_eq_true,
    ite_false, Bool.true_and, cu1_abs]
  cases hc : cu1Enabled s
  · simp only [Bool.not_false, ↓reduceIte]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl,
      gep_eq s (.CoprocessorUnusable 1) (by intro h; cases h) (by intro u h; cases h; omega)]
    rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact hrun hc

/-- **One FP operation, then the rest of the Operation** = the model's `fpThen`. -/
theorem runAbs_FPResult {α : Type} (s : State) (r : α × Mips.Fp.Flags) (k : α → Pseudo Unit)
    (K : State → α → State)
    (hk : Mips.Fp.fpeEnabled s.fcsr r.2 = false →
      runAbs (k r.1) { s with fcsr := Mips.Fp.raiseFlags s.fcsr r.2 } =
        some (abs (K { s with fcsr := Mips.Fp.raiseFlags s.fcsr r.2 } r.1))) :
    runAbs (FPResult r >>= k) s = some (abs (fpThen s r K)) := by
  unfold fpThen
  simp only [Mips.Fp.fpUpdate] at hk ⊢
  by_cases hX : Mips.Fp.fpeEnabled s.fcsr r.2 = true
  · simp only [hX, ↓reduceIte]
    unfold runAbs
    simp only [Mips.Fp.fpeEnabled] at hX
    simp only [Pseudo.run, bind, FPResult_run, abs_FCSR, hX, ↓reduceIte]
    rw [← gep_take _ .FloatingPoint rfl excCodeFPE (by decide)]
    rfl
  · simp only [hX, Bool.false_eq_true, ↓reduceIte]
    rw [← hk (by simpa using hX)]
    simp only [Mips.Fp.fpeEnabled] at hX
    unfold runAbs
    simp only [Pseudo.run, bind, FPResult_run, abs_FCSR, hX, Bool.false_eq_true, ↓reduceIte]
    rfl

/-! ## Stores -/

theorem regIdx_add_one (f : W32) : regIdx (f + 1#32) = reg f + 1 := by
  rw [regIdx_eq_reg]; unfold reg; apply Fin.ext
  simp only [Fin.val_add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem runAbs_store32 (s : State) (hfsz : s.fpRegs.size = 32) (fd v : W32) :
    runAbs (StoreFPR32 (reg fd) v) s = some (abs (mkNext s (writeFpReg s (regIdx fd) v))) := by
  unfold runAbs
  simp only [Pseudo.run, StoreFPR32]
  rw [complete_plain, mkNext, abs_advance _ _ (by rfl), abs_writeFpReg _ _ _ hfsz, regIdx_eq_reg]
  rfl

theorem writeFpReg_size (s : State) (i : Fin 32) (v : W32) :
    (writeFpReg s i v).fpRegs.size = s.fpRegs.size := by
  unfold writeFpReg writeFpReg64; simp

theorem abs_writeFpD (s : State) (hfsz : s.fpRegs.size = 32) (fd : W32) (v : BitVec 64) :
    abs (writeFpD s fd v) = { abs s with FPR := update (abs s).FPR (reg fd) v } := by
  unfold writeFpD
  rw [abs_writeFpReg64 _ _ _ hfsz, regIdx_eq_reg]

/-- `StoreFPR(fpr, D, value)` (`FR = 1`): the whole FPR. -/
theorem storeFPR64_model (fpr : Fin 32) (v : BitVec 64) (f : Frame) :
    StoreFPR64 fpr v modelCtx f =
      (.ok (), { f with arch := { f.arch with FPR := update f.arch.FPR fpr v } }) := rfl

theorem runAbs_store64 (s : State) (hfsz : s.fpRegs.size = 32) (fd : W32) (v : BitVec 64) :
    runAbs (StoreFPR64 (reg fd) v) s = some (abs (mkNext s (writeFpD s fd v))) := by
  unfold runAbs
  rw [mkNext, abs_advance _ _ (by rfl), abs_writeFpD _ hfsz]
  simp only [Pseudo.run, storeFPR64_model]
  rfl

/-- `fpFinishS` is `fpThen` with the store as the rest. -/
theorem fpFinishS_eq (s : State) (fd : W32) (r : W32 × Mips.Fp.Flags) :
    fpFinishS s fd r = fpThen s r (fun s1 v => mkNext s1 (writeFpReg s1 (regIdx fd) v)) := rfl

theorem fpFinishD_eq (s : State) (fd : W32) (r : BitVec 64 × Mips.Fp.Flags) :
    fpFinishD s fd r = fpThen s r (fun s1 v => mkNext s1 (writeFpD s1 fd v)) := rfl

/-- **One FP operation with a single result** = `fpFinishS`. -/
theorem runAbs_finS (s : State) (hfsz : s.fpRegs.size = 32) (fd : W32) (r : W32 × Mips.Fp.Flags) :
    runAbs (FPResult r >>= fun v => StoreFPR32 (reg fd) v) s = some (abs (fpFinishS s fd r)) := by
  rw [fpFinishS_eq]
  exact runAbs_FPResult s r _ _ fun _ =>
    runAbs_store32 { s with fcsr := Mips.Fp.raiseFlags s.fcsr r.2 } hfsz fd r.1

/-- **One FP operation with a double result** = `fpFinishD`. -/
theorem runAbs_finD (s : State) (hfsz : s.fpRegs.size = 32) (fd : W32)
    (r : BitVec 64 × Mips.Fp.Flags) :
    runAbs (FPResult r >>= fun v => StoreFPR64 (reg fd) v) s = some (abs (fpFinishD s fd r)) := by
  rw [fpFinishD_eq]
  exact runAbs_FPResult s r _ _ fun _ =>
    runAbs_store64 { s with fcsr := Mips.Fp.raiseFlags s.fcsr r.2 } hfsz fd r.1

/-! ## Reads -/

/-- `ValueFPR(fpr, D)` (`FR = 1`): the whole FPR. -/
theorem valueFPR64_model (fpr : Fin 32) (f : Frame) :
    ValueFPR64 fpr modelCtx f = (.ok (f.arch.FPR fpr), f) := rfl

theorem readFpReg_eq (s : State) (i : Fin 32) : readFpReg s i = (readFpReg64 s i).extractLsb' 0 32 := rfl

theorem readFpD_abs (s : State) (f : W32) : readFpD s f = (abs s).FPR (reg f) := by
  unfold readFpD; rw [regIdx_eq_reg]; rfl

/-! ## The environment of a later operation

`IEEE.env` reads `RM`, `Enables` and `FS`; an operation's FCSR update writes only `Cause` and
`Flags`, so a later operation of the same instruction runs in the environment of the first. -/

theorem envOf_raiseFlags (F : W32) (f : Mips.Fp.Flags) :
    Mips.Fp.envOf (Mips.Fp.raiseFlags F f) = Mips.Fp.envOf F := by
  have h1 : (Mips.Fp.raiseFlags F f).extractLsb' 0 2 = F.extractLsb' 0 2 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [Mips.Fp.raiseFlags, Mips.Fp.fcsrCauseMask, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
    rcases i with _|_|i <;> simp <;> omega
  have h2 : (Mips.Fp.raiseFlags F f).extractLsb' 7 5 = F.extractLsb' 7 5 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [Mips.Fp.raiseFlags, Mips.Fp.fcsrCauseMask, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
    rcases i with _|_|_|_|_|i <;> simp <;> omega
  have h3 : (Mips.Fp.raiseFlags F f).getLsbD 24 = F.getLsbD 24 := by
    simp [Mips.Fp.raiseFlags, Mips.Fp.fcsrCauseMask]
  simp only [Mips.Fp.envOf, Mips.Fp.getRM, Mips.Fp.getEnables, Mips.Fp.getFS, h1, h2, h3]

theorem fpEnv_raiseFlags (s : State) (f : Mips.Fp.Flags) :
    fpEnv { s with fcsr := Mips.Fp.raiseFlags s.fcsr f } = fpEnv s :=
  envOf_raiseFlags s.fcsr f

theorem env_abs (s : State) : IEEE.env (abs s) = fpEnv s := rfl

/-! ## Encoding spaces -/

theorem cop1_rFormat {i : Instruction} {w : W32} (op rs rt rd sa fn : W32)
    (hop : op = 0x11#32)
    (he : enc i = some (rFormat op rs rt rd sa fn)) (hw : enc i = some w) :
    InCop1Space w = true ∧ InCop0Space w = false := by
  rw [he] at hw; cases hw
  subst hop; simp [InCop1Space, InCop0Space, opcode_rFormat]

/-! ## NaN classes -/

theorem isNaN32_split (x : W32) :
    Mips.Fp.isNaN32 x = (Mips.Fp.isSNaN32 x || Mips.Fp.isQNaN32 x) := by
  unfold Mips.Fp.isSNaN32 Mips.Fp.isQNaN32 Mips.Fp.isNaN32 Mips.Fp.Format.isSNaN
    Mips.Fp.Format.isQNaN
  cases Mips.Fp.binary32.isNaN x.toNat <;> simp only [Bool.false_and, Bool.or_self, Bool.true_and]
  simp only [Mips.Fp.Format.fracField, Mips.Fp.binary32]
  have : x.toNat % 2 ^ 23 / 2 ^ 22 < 2 := by omega
  rcases h : x.toNat % 2 ^ 23 / 2 ^ 22 with _ | _ | n
  · rfl
  · rfl
  · omega

theorem isNaN64_split (x : BitVec 64) :
    Mips.Fp.isNaN64 x = (Mips.Fp.isSNaN64 x || Mips.Fp.isQNaN64 x) := by
  unfold Mips.Fp.isSNaN64 Mips.Fp.isQNaN64 Mips.Fp.isNaN64 Mips.Fp.Format.isSNaN
    Mips.Fp.Format.isQNaN
  cases Mips.Fp.binary64.isNaN x.toNat <;> simp only [Bool.false_and, Bool.or_self, Bool.true_and]
  simp only [Mips.Fp.Format.fracField, Mips.Fp.binary64]
  have : x.toNat % 2 ^ 52 / 2 ^ 51 < 2 := by omega
  rcases h : x.toNat % 2 ^ 52 / 2 ^ 51 with _ | _ | n
  · rfl
  · rfl
  · omega

theorem snan_not_qnan32 (x : W32) (h : Mips.Fp.isSNaN32 x = true) : Mips.Fp.isQNaN32 x = false := by
  unfold Mips.Fp.isSNaN32 Mips.Fp.Format.isSNaN at h
  unfold Mips.Fp.isQNaN32 Mips.Fp.Format.isQNaN
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1, h.2]; rfl

theorem snan_not_qnan64 (x : BitVec 64) (h : Mips.Fp.isSNaN64 x = true) :
    Mips.Fp.isQNaN64 x = false := by
  unfold Mips.Fp.isSNaN64 Mips.Fp.Format.isSNaN at h
  unfold Mips.Fp.isQNaN64 Mips.Fp.Format.isQNaN
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1, h.2]; rfl

/-! ## ABS / NEG (non-arithmetic, `FCSR.ABS2008 = 1`): the model's core functions are the spec's -/

theorem f32Abs_eq (x : W32) : Mips.Fp.f32Abs x = IEEE.absS x := by
  unfold Mips.Fp.f32Abs IEEE.absS; rfl

theorem f32Neg_eq (x : W32) : Mips.Fp.f32Neg x = IEEE.negS x := by
  unfold Mips.Fp.f32Neg IEEE.negS; rfl

theorem f64Abs_eq (x : BitVec 64) : Mips.Fp.f64Abs x = IEEE.absD x := by
  unfold Mips.Fp.f64Abs IEEE.absD; rfl

theorem f64Neg_eq (x : BitVec 64) : Mips.Fp.f64Neg x = IEEE.negD x := by
  unfold Mips.Fp.f64Neg IEEE.negD; rfl

/-! ## Conversions of a QNaN: the model's oracle choices (`cvtQNaNToD`/`cvtQNaNToS`) -/

theorem convert_qnan (src dst : Mips.Fp.Format) (e : Mips.Fp.Env) (n : Nat)
    (hq : src.isQNaN n = true) :
    src.convert dst e n = src.convert dst Mips.Fp.Env.RN n ∧ (src.convert dst e n).2 = Mips.Fp.Flags.none := by
  have hn : src.isNaN n = true := by
    unfold Mips.Fp.Format.isQNaN at hq; revert hq; cases src.isNaN n <;> simp
  have hs : src.isSNaN n = false := by
    unfold Mips.Fp.Format.isQNaN at hq; unfold Mips.Fp.Format.isSNaN; rw [hn] at hq ⊢
    simp only [Bool.true_and, beq_iff_eq] at hq ⊢; simp [hq]
  unfold Mips.Fp.Format.convert Mips.Fp.Format.convertNaN
  simp only [hn, hs, ↓reduceIte, Bool.false_eq_true, true_and]

theorem qnan_isNaN32 (x : W32) (hq : Mips.Fp.isQNaN32 x = true) : Mips.Fp.binary32.isNaN x.toNat = true := by
  unfold Mips.Fp.isQNaN32 Mips.Fp.Format.isQNaN at hq; revert hq; cases Mips.Fp.binary32.isNaN x.toNat <;> simp

theorem qnan_isNaN64 (x : BitVec 64) (hq : Mips.Fp.isQNaN64 x = true) :
    Mips.Fp.binary64.isNaN x.toNat = true := by
  unfold Mips.Fp.isQNaN64 Mips.Fp.Format.isQNaN at hq; revert hq; cases Mips.Fp.binary64.isNaN x.toNat <;> simp

/-- `CVT.D.S` with the model's oracle is the core's `f32ToF64` (flushing per `FCSR.FS`). -/
theorem cvtDS_model (a : Arch) (x : W32) :
    IEEE.cvtDS modelOracle.cvtQNaNToD a x = Mips.Fp.f32ToF64 (FCSR_FS a) x := by
  unfold IEEE.cvtDS
  split
  · next hq =>
    have hf : ∀ fl, Mips.Fp.binary32.flushIn fl x.toNat = x.toNat := fun fl =>
      Mips.Fp.Format.flushIn_of_isNaN _ _ _ (by decide) (qnan_isNaN32 x hq)
    have := (convert_qnan Mips.Fp.binary32 Mips.Fp.binary64 Mips.Fp.Env.RN x.toNat hq).2
    show ((Mips.Fp.f32ToF64 false x).1, Mips.Fp.Flags.none) = Mips.Fp.f32ToF64 (FCSR_FS a) x
    simp only [Mips.Fp.f32ToF64, hf]; rw [this]
  · rfl

/-- `CVT.S.D` with the model's oracle is the core's `f64ToF32` under the FCSR environment. -/
theorem cvtSD_model (a : Arch) (x : BitVec 64) :
    IEEE.cvtSD modelOracle.cvtQNaNToS a x = Mips.Fp.f64ToF32 (IEEE.env a) x := by
  unfold IEEE.cvtSD
  split
  · next hq =>
    have hf : ∀ fl, Mips.Fp.binary64.flushIn fl x.toNat = x.toNat := fun fl =>
      Mips.Fp.Format.flushIn_of_isNaN _ _ _ (by decide) (qnan_isNaN64 x hq)
    have h := convert_qnan Mips.Fp.binary64 Mips.Fp.binary32 (IEEE.env a) x.toNat hq
    show ((Mips.Fp.f64ToF32 Mips.Fp.Env.RN x).1, Mips.Fp.Flags.none) = Mips.Fp.f64ToF32 (IEEE.env a) x
    obtain ⟨h1, h2⟩ := h; simp only [Mips.Fp.f64ToF32, hf]; rw [h1] at h2 ⊢; rw [h2]
  · rfl

end Refine
