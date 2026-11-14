import Semantics.Refine.BridgeFpuMove

/-!
# Refine.FpuControl — FP control register moves against `execInstr` (7C S4b)

`CFC1` and `CTC1`: the FCCR/FEXR/FENR/FCSR views of the manual's Operation (MD00086 Vol II-A Rev 6.06,
CFC1 p.129-130, CTC1 p.149-150) against `Mips.Fp.readControl`/`writeControl`, the UNPREDICTABLE arms
under `modelOracle` (`cfc1Unpredictable` reads 0; `ctc1Unpredictable` writes the page's value with the
reserved bits ignored, or nothing for a register that does not exist), and `CTC1`'s
`CheckFPException()` after the write ("The register is written before the exception occurs", p.149)
against `Mips.Fp.fcsrTrapPending`.

`cfc1_refines` assumes `FcsrReservedZero s` (FCSR bits 22..18 are 0, as they read on this profile):
the manual's `temp ← FCSR` returns the register while the model's read masks those bits.
-/

namespace Refine

open Manual

/-- The value `CFC1` reads, the manual's `if` chain against `Mips.Fp.readControl`. -/
theorem cfc1_temp (F fs : W32) (hres : F.extractLsb' 18 5 = 0#5) :
    (if (fs == 0#32) = true then (0x00330000#32 : W32)
     else if (fs == 25#32) = true then (0#24 ++ F.extractLsb' 25 7 ++ BitVec.ofBool (bit F 23) : BitVec 32)
     else if (fs == 26#32) = true then
       (0#14 ++ F.extractLsb' 12 6 ++ 0#5 ++ F.extractLsb' 2 5 ++ 0#2 : BitVec 32)
     else if (fs == 28#32) = true then
       (0#20 ++ F.extractLsb' 7 5 ++ 0#4 ++ BitVec.ofBool (bit F 24) ++ F.extractLsb' 0 2 : BitVec 32)
     else if (fs == 31#32) = true then F
     else 0#32) = (Mips.Fp.readControl F fs.toNat).getD 0#32 := by
  by_cases h0 : fs = 0#32
  · subst h0; rfl
  by_cases h25 : fs = 25#32
  · subst h25; rw [cfc1_fccr]; rfl
  by_cases h26 : fs = 26#32
  · subst h26; rw [cfc1_fexr]; rfl
  by_cases h28 : fs = 28#32
  · subst h28; rw [cfc1_fenr]; rfl
  by_cases h31 : fs = 31#32
  · subst h31
    show F = Mips.Fp.readFCSR F
    rw [readFCSR_of_reserved F hres]
  have hn : Mips.Fp.readControl F fs.toNat = none := by
    have := toNat_ne_of_ne h0 (by omega); have := toNat_ne_of_ne h25 (by omega)
    have := toNat_ne_of_ne h26 (by omega); have := toNat_ne_of_ne h28 (by omega)
    have := toNat_ne_of_ne h31 (by omega)
    unfold Mips.Fp.readControl; split <;> simp_all
  simp only [beq_iff_eq, h0, h25, h26, h28, h31, ↓reduceIte, hn,
    Option.getD_none]

/-- **CFC1 refines**, for the states whose FCSR reserved bits read 0 (`FcsrReservedZero`). -/
theorem cfc1_refines (s : State) (hg : Good s) (hres : FcsrReservedZero s) (rt fs w : W32)
    (hw : enc (.cfc1 rt fs) = some w) :
    Execute modelCtx w (.cfc1 rt fs) (abs s) = some (abs (execInstr s (.cfc1 rt fs))) := by
  obtain ⟨hsz, -, -⟩ := hg
  have hw' : w = rFormat 0x11#32 0x02#32 rt fs 0#32 0#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.CFC1 rt fs) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.cfc1 rt fs) =
      mkNext s (writeReg s (regIdx rt) ((Mips.Fp.readControl s.fcsr fs.toNat).getD 0#32)) := rfl
  rw [hb, abs_mkNext_writeReg _ _ _ hsz]
  simp only [Pseudo.run, Ops.CFC1, bind, Pseudo.get, Pseudo.oracle, Pseudo.impl, setGPR, abs_FCSR,
    show modelCtx.impl.FIR = 0x00330000#32 from rfl,
    show modelCtx.oracle.cfc1Unpredictable (abs s) fs = 0#32 from rfl, cfc1_temp s.fcsr fs (fcsrReservedZero_extract s hres),
    complete_plain, regIdx_eq_reg]

/-- The FCSR after the write part of `CTC1` (before `CheckFPException()`), under `modelOracle`: the
model's `Mips.Fp.writeControl`, the FCSR unchanged for a register that does not exist. -/
theorem ctc1_run (s : State) (h0 : readReg s 0 = 0#32) (rt fs : W32) :
    (Ops.CTC1 rt fs).run modelCtx { arch := abs s } =
      CheckFPException modelCtx { arch := { abs s with FCSR :=
        (Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt))).getD s.fcsr } } := by
  simp only [Pseudo.run, Ops.CTC1, bind, Pseudo.get, Pseudo.oracle, GPR, readGPR_abs s h0, low_32,
    ← regIdx_eq_reg]
  generalize readReg s (regIdx rt) = v
  have ho : modelCtx.oracle = modelOracle := rfl
  by_cases h25 : fs = 25#32
  · subst h25
    simp only [beq_self_eq_true, ↓reduceIte]
    cases (bits v 31 8 != 0#24)
    · simp only [Bool.false_eq_true, ↓reduceIte, Pseudo.modify, ctc1_fccr]
      rfl
    · simp only [↓reduceIte, ho, modelOracle, resolve, beq_self_eq_true, ctc1_fccr']
      rfl
  by_cases h26 : fs = 26#32
  · subst h26
    simp only [BitVec.reduceBEq, Bool.false_eq_true, ↓reduceIte]
    cases (bits v 31 18 != 0#14 || bits v 11 7 != 0#5 || bits v 2 0 != 0#3)
    · simp only [Bool.false_eq_true, ↓reduceIte, Pseudo.modify, ctc1_fexr]
      rfl
    · simp only [↓reduceIte, ho, modelOracle, resolve, BitVec.reduceBEq, Bool.false_eq_true, ctc1_fexr']
      rfl
  by_cases h28 : fs = 28#32
  · subst h28
    simp only [BitVec.reduceBEq, Bool.false_eq_true, ↓reduceIte]
    cases (bits v 31 12 != 0#20 || bits v 6 3 != 0#4)
    · simp only [Bool.false_eq_true, ↓reduceIte, Pseudo.modify, ctc1_fenr]
      rfl
    · simp only [↓reduceIte, ho, modelOracle, resolve, BitVec.reduceBEq, Bool.false_eq_true, ctc1_fenr']
      rfl
  by_cases h31 : fs = 31#32
  · subst h31
    simp only [BitVec.reduceBEq, Bool.false_eq_true, ↓reduceIte]
    cases hr : (bits v 22 18 != 0#5)
    · have hz : v.extractLsb' 18 5 = 0#5 := by simpa [bits] using hr
      simp only [Bool.false_eq_true, ↓reduceIte, Pseudo.modify]
      rw [show Mips.Fp.writeControl s.fcsr (31#32).toNat v = some (Mips.Fp.readFCSR v) from rfl,
        readFCSR_of_reserved v hz]
      rfl
    · simp only [↓reduceIte, ho, modelOracle, resolve, BitVec.reduceBEq, Bool.false_eq_true,
        ctc1_fcsr' s.fcsr]
      rfl
  have hn : (Mips.Fp.writeControl s.fcsr fs.toNat v).getD s.fcsr = s.fcsr := by
    have := toNat_ne_of_ne h25 (by omega); have := toNat_ne_of_ne h26 (by omega)
    have := toNat_ne_of_ne h28 (by omega); have := toNat_ne_of_ne h31 (by omega)
    unfold Mips.Fp.writeControl; split <;> simp_all
  simp only [beq_iff_eq, h25, h26, h28, h31, ↓reduceIte, ho, modelOracle, resolve, hn]
  rfl

/-- **CTC1 refines**: the write, then `CheckFPException()` on the written FCSR (a register that does
not exist is not written, and the check still runs). -/
theorem ctc1_refines (s : State) (hg : Good s) (rt fs w : W32)
    (hw : enc (.ctc1 rt fs) = some w) :
    Execute modelCtx w (.ctc1 rt fs) (abs s) = some (abs (execInstr s (.ctc1 rt fs))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = rFormat 0x11#32 0x06#32 rt fs 0#32 0#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.CTC1 rt fs) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.ctc1 rt fs) =
      if Mips.Fp.fcsrTrapPending
          ((Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt))).getD s.fcsr) then
        takeException { s with fcsr :=
          (Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt))).getD s.fcsr } excCodeFPE
      else mkNext s { s with fcsr :=
          (Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt))).getD s.fcsr } := by
    show (match Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt)) with
      | none =>
        if Mips.Fp.fcsrTrapPending s.fcsr then takeException s excCodeFPE else mkNext s s
      | some f =>
        if Mips.Fp.fcsrTrapPending f then takeException { s with fcsr := f } excCodeFPE
        else mkNext s { s with fcsr := f }) = _
    cases Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt)) <;> rfl
  rw [hb, ctc1_run s h0, checkFP_run]
  generalize (Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt))).getD s.fcsr = F
  cases Mips.Fp.fcsrTrapPending F
  · simp only [Bool.false_eq_true, ↓reduceIte, complete_plain]
    rw [mkNext, abs_advance _ _ (by rfl)]
    rfl
  · simp only [↓reduceIte]
    exact congrArg some (gep_take { s with fcsr := F } .FloatingPoint rfl excCodeFPE (by decide))

end Refine
