import Semantics.Refine.BridgeFpu
import Semantics.Refine.BridgeControl
import Semantics.Refine.Decode

/-!
# Refine.FpuR6 — the Release 6 FP instructions against `execInstr`

`Refine.<ctor>_refines` for `CMP.condn.fmt`, `BC1EQZ`/`BC1NEZ`, `SEL.fmt`, `SELEQZ.fmt`/`SELNEZ.fmt`,
`MADDF.fmt`/`MSUBF.fmt`, `MAX`/`MIN`/`MAXA`/`MINA.fmt`, `CLASS.fmt`, `RINT.fmt` (fmt = S, D;
MD00086 Vol II-A Rev 6.06). The arithmetic ones complete through `FPResult` against the model's
`fpFinishS`/`fpFinishD` (`runAbs_finS`/`runAbs_finD`, `runAbs_FPResult`); the core operations are
the same functions on both sides (`Manual.IEEE.fmaS` …), except `CMP.condn.fmt`, whose Operation is
transcribed from the page (p.140) and is the model's `Mips.Fp.f32Cmp`/`f64Cmp` by `f32Cmp_eq`/
`f64Cmp_eq`. `BC1EQZ`/`BC1NEZ` are COP1 instructions and CTIs: in a delay slot Reserved Instruction
(`execute_cti_slot`), else the coprocessor check and the Operation (`execute_cop1_branch`).
-/

namespace Refine

open Manual

set_option linter.unusedSimpArgs false

/-! ## Bridges -/

/-- **`Execute` of a COP1 instruction outside a delay slot** (a CTI included): Coprocessor Unusable
when `Status.CU1 = 0`, else the Operation; against `execInstr`. -/
theorem execute_cop1_branch (s : State) (w : W32) (i : Instruction) (op : Pseudo Unit)
    (hpb : s.pendingBranch = none) (h1 : InCop1Space w = true) (h0 : InCop0Space w = false)
    (hop : Operation i = some op) (hu : usesCop1 i = true) (hu0 : usesCop0 i = false)
    (hrun : cu1Enabled s = true → runAbs op s = some (abs (execBody s i))) :
    Execute modelCtx w i (abs s) = some (abs (execInstr s i)) := by
  have hb : (abs s).BranchDelay.isSome = false := by simp [abs, hpb]
  have hex : execInstr s i =
      if (!cu1Enabled s) = true then takeCoprocessorUnusable s else execBody s i := by
    unfold execInstr; rw [hpb, hu, hu0]
    try simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, ite_false, Bool.true_and,
      Bool.false_and]
  rw [hex]
  simp only [Execute, Execute.runOperation, hb, Bool.and_false, Bool.false_eq_true, ite_false, h1, h0,
    hop, Bool.false_and, Bool.true_and, cu1_abs]
  cases hc : cu1Enabled s
  · simp only [Bool.not_false, ↓reduceIte]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl,
      gep_eq s (.CoprocessorUnusable 1) (by intro h; cases h) (by intro u h; cases h; omega)]
    rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact hrun hc

theorem cmpCondn_getLsbD4 (cond : W32) (i : Nat) (h : i < 4) :
    ((cmpCondn cond).setWidth 4).getLsbD i = bit cond i := by
  simp [cmpCondn, h, bit]

theorem cmpCondn_getLsbD (cond : W32) : (cmpCondn cond).getLsbD 4 = bit cond 4 := by
  simp [cmpCondn, bit]

/-- The core's `f32Cmp` is the Operation of `CMP.condn.S` (MD00086 Vol II-A Rev 6.06,
CMP.condn.fmt, p.140). -/
theorem f32Cmp_eq (cond x y : W32) :
    Mips.Fp.f32Cmp (cmpCondn cond) x y =
      (let isNaN := IEEE.isSNaNS x || IEEE.isSNaNS y || IEEE.isQNaNS x || IEEE.isQNaNS y
       let invalid := (IEEE.isSNaNS x || IEEE.isSNaNS y) ||
         (bit cond 3 && (IEEE.isQNaNS x || IEEE.isQNaNS y))
       let less := if isNaN then false else IEEE.ltS x y
       let equal := if isNaN then false else IEEE.eqS x y
       (bit cond 4 ^^ ((bit cond 2 && less) || (bit cond 1 && equal) || (bit cond 0 && isNaN)),
        if invalid then Mips.Fp.Flags.invalidOnly else Mips.Fp.Flags.none)) := by
  have hn : (IEEE.isSNaNS x || IEEE.isSNaNS y || IEEE.isQNaNS x || IEEE.isQNaNS y) =
      (Mips.Fp.isNaN32 x || Mips.Fp.isNaN32 y) := by
    rw [isNaN32_split, isNaN32_split]; unfold IEEE.isSNaNS IEEE.isQNaNS
    cases Mips.Fp.isSNaN32 x <;> cases Mips.Fp.isSNaN32 y <;> cases Mips.Fp.isQNaN32 x <;>
      cases Mips.Fp.isQNaN32 y <;> rfl
  simp only [hn]
  unfold Mips.Fp.f32Cmp Mips.Fp.cmpCondition IEEE.ltS IEEE.eqS IEEE.isSNaNS IEEE.isQNaNS
    Mips.Fp.f32Relation Mips.Fp.Format.relation Mips.Fp.fpCompare Mips.Fp.fpCompareInvalid
  simp only [cmpCondn_getLsbD4 cond 0 (by omega), cmpCondn_getLsbD4 cond 1 (by omega),
    cmpCondn_getLsbD4 cond 2 (by omega), cmpCondn_getLsbD4 cond 3 (by omega), cmpCondn_getLsbD]
  rw [show Mips.Fp.binary32.isNaN x.toNat = Mips.Fp.isNaN32 x from rfl,
    show Mips.Fp.binary32.isNaN y.toNat = Mips.Fp.isNaN32 y from rfl]
  rw [isNaN32_split x, isNaN32_split y]
  cases Mips.Fp.isSNaN32 x <;> cases Mips.Fp.isSNaN32 y <;> cases Mips.Fp.isQNaN32 x <;>
    cases Mips.Fp.isQNaN32 y <;> cases bit cond 0 <;> cases bit cond 1 <;> cases bit cond 2 <;>
    cases bit cond 3 <;> simp [Mips.Fp.Flags.invalidOnly, Mips.Fp.Flags.none, Bool.or_comm]

/-- As `f32Cmp_eq`, for `CMP.condn.D`. -/
theorem f64Cmp_eq (cond : W32) (x y : BitVec 64) :
    Mips.Fp.f64Cmp (cmpCondn cond) x y =
      (let isNaN := IEEE.isSNaND x || IEEE.isSNaND y || IEEE.isQNaND x || IEEE.isQNaND y
       let invalid := (IEEE.isSNaND x || IEEE.isSNaND y) ||
         (bit cond 3 && (IEEE.isQNaND x || IEEE.isQNaND y))
       let less := if isNaN then false else IEEE.ltD x y
       let equal := if isNaN then false else IEEE.eqD x y
       (bit cond 4 ^^ ((bit cond 2 && less) || (bit cond 1 && equal) || (bit cond 0 && isNaN)),
        if invalid then Mips.Fp.Flags.invalidOnly else Mips.Fp.Flags.none)) := by
  have hn : (IEEE.isSNaND x || IEEE.isSNaND y || IEEE.isQNaND x || IEEE.isQNaND y) =
      (Mips.Fp.isNaN64 x || Mips.Fp.isNaN64 y) := by
    rw [isNaN64_split, isNaN64_split]; unfold IEEE.isSNaND IEEE.isQNaND
    cases Mips.Fp.isSNaN64 x <;> cases Mips.Fp.isSNaN64 y <;> cases Mips.Fp.isQNaN64 x <;>
      cases Mips.Fp.isQNaN64 y <;> rfl
  simp only [hn]
  unfold Mips.Fp.f64Cmp Mips.Fp.cmpCondition IEEE.ltD IEEE.eqD IEEE.isSNaND IEEE.isQNaND
    Mips.Fp.f64Relation Mips.Fp.Format.relation Mips.Fp.fpCompare Mips.Fp.fpCompareInvalid
  simp only [cmpCondn_getLsbD4 cond 0 (by omega), cmpCondn_getLsbD4 cond 1 (by omega),
    cmpCondn_getLsbD4 cond 2 (by omega), cmpCondn_getLsbD4 cond 3 (by omega), cmpCondn_getLsbD]
  rw [show Mips.Fp.binary64.isNaN x.toNat = Mips.Fp.isNaN64 x from rfl,
    show Mips.Fp.binary64.isNaN y.toNat = Mips.Fp.isNaN64 y from rfl]
  rw [isNaN64_split x, isNaN64_split y]
  cases Mips.Fp.isSNaN64 x <;> cases Mips.Fp.isSNaN64 y <;> cases Mips.Fp.isQNaN64 x <;>
    cases Mips.Fp.isQNaN64 y <;> cases bit cond 0 <;> cases bit cond 1 <;> cases bit cond 2 <;>
    cases bit cond 3 <;> simp [Mips.Fp.Flags.invalidOnly, Mips.Fp.Flags.none, Bool.or_comm]

/-! ## CMP.condn.fmt -/

theorem fcsrFS_abs6 (s : State) : FCSR_FS (abs s) = (fpEnv s).flush := rfl

/-- **CMP.condn.S refines.** -/
theorem cmpS_refines (s : State) (hg : Good s) (cond fd fs ft w : W32)
    (hw : enc (.cmpS cond fd fs ft) = some w) :
    Execute modelCtx w (.cmpS cond fd fs ft) (abs s) =
      some (abs (execInstr s (.cmpS cond fd fs ft))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  have hc : CmpCondnOK cond = true := (encIf_some hw).1
  obtain ⟨h1, h0⟩ := cop1_rFormat 0x11#32 0x14#32 ft fs fd cond rfl
    (by simp only [enc, encIf_true hc]) hw
  refine execute_cop1 s w _ (Ops.CMP_S cond fd fs ft) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.cmpS cond fd fs ft) =
      fpThen s (Mips.Fp.f32Cmp (cmpCondn cond) (cmpInS (fpEnv s).flush (readFpReg s (regIdx fs)))
        (cmpInS (fpEnv s).flush (readFpReg s (regIdx ft))))
        (fun s1 b => mkNext s1 (writeFpReg s1 (regIdx fd) (Ops.ExtendBitS b))) from rfl, f32Cmp_eq]
  refine Eq.trans ?_ (runAbs_FPResult s _ (fun b => StoreFPR32 (reg fd) (Ops.ExtendBitS b)) _
    fun _ => runAbs_store32 { s with fcsr := Mips.Fp.raiseFlags s.fcsr _ } hfsz fd _)
  apply runAbs_congr
  simp only [Ops.CMP_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg,
    IEEE.flushInS, cmpInS, fcsrFS_abs6]
  rfl

/-- **CMP.condn.D refines.** -/
theorem cmpD_refines (s : State) (hg : Good s) (cond fd fs ft w : W32)
    (hw : enc (.cmpD cond fd fs ft) = some w) :
    Execute modelCtx w (.cmpD cond fd fs ft) (abs s) =
      some (abs (execInstr s (.cmpD cond fd fs ft))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  have hc : CmpCondnOK cond = true := (encIf_some hw).1
  obtain ⟨h1, h0⟩ := cop1_rFormat 0x11#32 0x15#32 ft fs fd cond rfl
    (by simp only [enc, encIf_true hc]) hw
  refine execute_cop1 s w _ (Ops.CMP_D cond fd fs ft) rfl h1 h0 rfl rfl rfl rfl fun _ => ?_
  rw [show execBody s (.cmpD cond fd fs ft) =
      fpThen s (Mips.Fp.f64Cmp (cmpCondn cond) (cmpInD (fpEnv s).flush (readFpD s fs))
        (cmpInD (fpEnv s).flush (readFpD s ft)))
        (fun s1 b => mkNext s1 (writeFpD s1 fd (Ops.ExtendBitD b))) from rfl, f64Cmp_eq]
  refine Eq.trans ?_ (runAbs_FPResult s _ (fun b => StoreFPR64 (reg fd) (Ops.ExtendBitD b)) _
    fun _ => runAbs_store64 { s with fcsr := Mips.Fp.raiseFlags s.fcsr _ } hfsz fd _)
  apply runAbs_congr
  simp only [Ops.CMP_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, IEEE.flushInD, cmpInD, fcsrFS_abs6]
  rfl

/-! ## BC1EQZ, BC1NEZ -/

/-- **BC1EQZ refines.** -/
theorem bc1eqz_refines (s : State) (hg : Good s) (ft off w : W32)
    (hw : enc (.bc1eqz ft off) = some w) :
    Execute modelCtx w (.bc1eqz ft off) (abs s) = some (abs (execInstr s (.bc1eqz ft off))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  have hw' : w = iFormat 0x11#32 0x09#32 ft off := (Option.some.inj hw).symm
  have hc1 : InCop1Space w = true := by subst hw'; simp [InCop1Space, opcode_iFormat]
  have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_iFormat]
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w _ s t rfl hpb]
    unfold execInstr; rw [show isBranchLike (.bc1eqz ft off) = true from rfl, hpb]; rfl
  | none =>
    refine execute_cop1_branch s w _ (Ops.BC1EQZ ft off) hpb hc1 hc0 rfl rfl rfl fun _ => ?_
    rw [show execBody s (.bc1eqz ft off) =
        (if readFpReg s (regIdx ft) &&& 1#32 == 0#32 then
          { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }
        else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) from rfl]
    unfold runAbs
    simp only [Pseudo.run, Ops.BC1EQZ, bind, ValueFPR32, PC, abs_FPR, ← readFpReg_eq, ← regIdx_eq_reg,
      branch_offset]
    by_cases hc : readFpReg s (regIdx ft) &&& 1#32 = 0#32 <;>
      simp [hc, I1, Complete, abs, readReg, readFpReg64, hpb]

/-- **BC1NEZ refines.** -/
theorem bc1nez_refines (s : State) (hg : Good s) (ft off w : W32)
    (hw : enc (.bc1nez ft off) = some w) :
    Execute modelCtx w (.bc1nez ft off) (abs s) = some (abs (execInstr s (.bc1nez ft off))) := by
  obtain ⟨-, hfsz, -⟩ := hg
  have hw' : w = iFormat 0x11#32 0x0D#32 ft off := (Option.some.inj hw).symm
  have hc1 : InCop1Space w = true := by subst hw'; simp [InCop1Space, opcode_iFormat]
  have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_iFormat]
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w _ s t rfl hpb]
    unfold execInstr; rw [show isBranchLike (.bc1nez ft off) = true from rfl, hpb]; rfl
  | none =>
    refine execute_cop1_branch s w _ (Ops.BC1NEZ ft off) hpb hc1 hc0 rfl rfl rfl fun _ => ?_
    rw [show execBody s (.bc1nez ft off) =
        (if readFpReg s (regIdx ft) &&& 1#32 == 0#32 then
          { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }
        else { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 4#32 + (signExt16 off <<< 2)) }) from rfl]
    unfold runAbs
    simp only [Pseudo.run, Ops.BC1NEZ, bind, ValueFPR32, PC, abs_FPR, ← readFpReg_eq, ← regIdx_eq_reg,
      branch_offset]
    by_cases hc : readFpReg s (regIdx ft) &&& 1#32 = 0#32 <;>
      simp [hc, I1, Complete, abs, readReg, readFpReg64, hpb]

/-! ## SEL.fmt, SELEQZ.fmt, SELNEZ.fmt (FCSR untouched) -/

/-- **SEL.S refines.** -/
theorem selS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.selS fd fs ft) = some w) :
    Execute modelCtx w (.selS fd fs ft) (abs s) = some (abs (execInstr s (.selS fd fs ft))) := by
  fp_refine runAbs_store32 fd =>
    cases hb : (readFpReg s (regIdx fd)).getLsbD 0 <;>
      simp only [regIdx_eq_reg, readFpReg_eq] at hb <;>
      simp only [Ops.SEL_S, bind, ValueFPR32, abs_FPR, bit, hb, Bool.not_false, Bool.not_true,
        ite_true, ite_false, Bool.false_eq_true, valueFPR64_model, pure, readFpD_abs, readFpReg_eq,
        regIdx_eq_reg] <;> rfl

/-- **SELEQZ.S refines.** -/
theorem seleqzS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.seleqzS fd fs ft) = some w) :
    Execute modelCtx w (.seleqzS fd fs ft) (abs s) = some (abs (execInstr s (.seleqzS fd fs ft))) := by
  fp_refine runAbs_store32 fd =>
    cases hb : (readFpReg s (regIdx ft)).getLsbD 0 <;>
      simp only [regIdx_eq_reg, readFpReg_eq] at hb <;>
      simp only [Ops.SELEQZ_S, bind, ValueFPR32, abs_FPR, bit, hb, Bool.not_false, Bool.not_true,
        ite_true, ite_false, Bool.false_eq_true, valueFPR64_model, pure, readFpD_abs, readFpReg_eq,
        regIdx_eq_reg] <;> rfl

/-- **SELNEZ.S refines.** -/
theorem selnezS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.selnezS fd fs ft) = some w) :
    Execute modelCtx w (.selnezS fd fs ft) (abs s) = some (abs (execInstr s (.selnezS fd fs ft))) := by
  fp_refine runAbs_store32 fd =>
    cases hb : (readFpReg s (regIdx ft)).getLsbD 0 <;>
      simp only [regIdx_eq_reg, readFpReg_eq] at hb <;>
      simp only [Ops.SELNEZ_S, bind, ValueFPR32, abs_FPR, bit, hb, Bool.not_false, Bool.not_true,
        ite_true, ite_false, Bool.false_eq_true, valueFPR64_model, pure, readFpD_abs, readFpReg_eq,
        regIdx_eq_reg] <;> rfl

/-- **SEL.D refines.** -/
theorem selD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.selD fd fs ft) = some w) :
    Execute modelCtx w (.selD fd fs ft) (abs s) = some (abs (execInstr s (.selD fd fs ft))) := by
  fp_refine runAbs_store64 fd =>
    cases hb : (readFpReg s (regIdx fd)).getLsbD 0 <;>
      simp only [regIdx_eq_reg, readFpReg_eq] at hb <;>
      simp only [Ops.SEL_D, bind, ValueFPR32, abs_FPR, bit, hb, Bool.not_false, Bool.not_true,
        ite_true, ite_false, Bool.false_eq_true, valueFPR64_model, pure, readFpD_abs, readFpReg_eq,
        regIdx_eq_reg] <;> rfl

/-- **SELEQZ.D refines.** -/
theorem seleqzD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.seleqzD fd fs ft) = some w) :
    Execute modelCtx w (.seleqzD fd fs ft) (abs s) = some (abs (execInstr s (.seleqzD fd fs ft))) := by
  fp_refine runAbs_store64 fd =>
    cases hb : (readFpReg s (regIdx ft)).getLsbD 0 <;>
      simp only [regIdx_eq_reg, readFpReg_eq] at hb <;>
      simp only [Ops.SELEQZ_D, bind, ValueFPR32, abs_FPR, bit, hb, Bool.not_false, Bool.not_true,
        ite_true, ite_false, Bool.false_eq_true, valueFPR64_model, pure, readFpD_abs, readFpReg_eq,
        regIdx_eq_reg] <;> rfl

/-- **SELNEZ.D refines.** -/
theorem selnezD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.selnezD fd fs ft) = some w) :
    Execute modelCtx w (.selnezD fd fs ft) (abs s) = some (abs (execInstr s (.selnezD fd fs ft))) := by
  fp_refine runAbs_store64 fd =>
    cases hb : (readFpReg s (regIdx ft)).getLsbD 0 <;>
      simp only [regIdx_eq_reg, readFpReg_eq] at hb <;>
      simp only [Ops.SELNEZ_D, bind, ValueFPR32, abs_FPR, bit, hb, Bool.not_false, Bool.not_true,
        ite_true, ite_false, Bool.false_eq_true, valueFPR64_model, pure, readFpD_abs, readFpReg_eq,
        regIdx_eq_reg] <;> rfl

/-! ## The arithmetic ones -/

/-- **maddfS refines.** -/
theorem maddfS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.maddfS fd fs ft) = some w) :
    Execute modelCtx w (.maddfS fd fs ft) (abs s) = some (abs (execInstr s (.maddfS fd fs ft))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.MADDF_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.fmaS]

/-- **msubfS refines.** -/
theorem msubfS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.msubfS fd fs ft) = some w) :
    Execute modelCtx w (.msubfS fd fs ft) (abs s) = some (abs (execInstr s (.msubfS fd fs ft))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.MADDF_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.fmaS]

/-- **maxS refines.** -/
theorem maxS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.maxS fd fs ft) = some w) :
    Execute modelCtx w (.maxS fd fs ft) (abs s) = some (abs (execInstr s (.maxS fd fs ft))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.MINMAX_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.minMaxS]

/-- **minS refines.** -/
theorem minS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.minS fd fs ft) = some w) :
    Execute modelCtx w (.minS fd fs ft) (abs s) = some (abs (execInstr s (.minS fd fs ft))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.MINMAX_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.minMaxS]

/-- **maxaS refines.** -/
theorem maxaS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.maxaS fd fs ft) = some w) :
    Execute modelCtx w (.maxaS fd fs ft) (abs s) = some (abs (execInstr s (.maxaS fd fs ft))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.MINMAX_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.minMaxS]

/-- **minaS refines.** -/
theorem minaS_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.minaS fd fs ft) = some w) :
    Execute modelCtx w (.minaS fd fs ft) (abs s) = some (abs (execInstr s (.minaS fd fs ft))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.MINMAX_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs, IEEE.minMaxS]

/-- **maddfD refines.** -/
theorem maddfD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.maddfD fd fs ft) = some w) :
    Execute modelCtx w (.maddfD fd fs ft) (abs s) = some (abs (execInstr s (.maddfD fd fs ft))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.MADDF_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.fmaD]

/-- **msubfD refines.** -/
theorem msubfD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.msubfD fd fs ft) = some w) :
    Execute modelCtx w (.msubfD fd fs ft) (abs s) = some (abs (execInstr s (.msubfD fd fs ft))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.MADDF_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.fmaD]

/-- **maxD refines.** -/
theorem maxD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.maxD fd fs ft) = some w) :
    Execute modelCtx w (.maxD fd fs ft) (abs s) = some (abs (execInstr s (.maxD fd fs ft))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.MINMAX_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.minMaxD]

/-- **minD refines.** -/
theorem minD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.minD fd fs ft) = some w) :
    Execute modelCtx w (.minD fd fs ft) (abs s) = some (abs (execInstr s (.minD fd fs ft))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.MINMAX_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.minMaxD]

/-- **maxaD refines.** -/
theorem maxaD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.maxaD fd fs ft) = some w) :
    Execute modelCtx w (.maxaD fd fs ft) (abs s) = some (abs (execInstr s (.maxaD fd fs ft))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.MINMAX_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.minMaxD]

/-- **minaD refines.** -/
theorem minaD_refines (s : State) (hg : Good s) (fd fs ft w : W32)
    (hw : enc (.minaD fd fs ft) = some w) :
    Execute modelCtx w (.minaD fd fs ft) (abs s) = some (abs (execInstr s (.minaD fd fs ft))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.MINMAX_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.minMaxD]

/-! ## CLASS.fmt (FCSR untouched), RINT.fmt -/

/-- **CLASS.S refines.** -/
theorem classS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.classS fd fs) = some w) :
    Execute modelCtx w (.classS fd fs) (abs s) = some (abs (execInstr s (.classS fd fs))) := by
  fp_refine runAbs_store32 fd =>
    simp only [Ops.CLASS_S, bind, ValueFPR32, abs_FPR, readFpReg_eq, regIdx_eq_reg, IEEE.classS]

/-- **CLASS.D refines.** -/
theorem classD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.classD fd fs) = some w) :
    Execute modelCtx w (.classD fd fs) (abs s) = some (abs (execInstr s (.classD fd fs))) := by
  fp_refine runAbs_store64 fd =>
    simp only [Ops.CLASS_D, bind, valueFPR64_model, readFpD_abs, IEEE.classD]

/-- **RINT.S refines.** -/
theorem rintS_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.rintS fd fs) = some w) :
    Execute modelCtx w (.rintS fd fs) (abs s) = some (abs (execInstr s (.rintS fd fs))) := by
  fp_refine runAbs_finS fd =>
    simp only [Ops.RINT_S, bind, ValueFPR32, Pseudo.get, abs_FPR, readFpReg_eq, regIdx_eq_reg, env_abs,
      IEEE.rintS]

/-- **RINT.D refines.** -/
theorem rintD_refines (s : State) (hg : Good s) (fd fs w : W32)
    (hw : enc (.rintD fd fs) = some w) :
    Execute modelCtx w (.rintD fd fs) (abs s) = some (abs (execInstr s (.rintD fd fs))) := by
  fp_refine runAbs_finD fd =>
    simp only [Ops.RINT_D, bind, valueFPR64_model, Pseudo.get, readFpD_abs, env_abs, IEEE.rintD]

end Refine
