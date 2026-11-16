import Semantics.Refine.BridgeFpuMove

/-!
# Refine.FpuControl — FP control register moves against `execInstr` (7C S4b)

`CFC1` and `CTC1`: the FCCR/FEXR/FENR/FCSR views of the manual's Operation (MD00086 Vol II-A Rev 6.06,
CFC1 p.129-130, CTC1 p.149-150) against `Mips.Fp.readControl`/`writeControl`, the UNPREDICTABLE arms
under `modelOracle` (`ctc1Unpredictable` writes the page's value with the reserved bits ignored,
Reserved Instruction for `FRE`/`NFRE`; `CFC1` of `FRE` signals Reserved Instruction on both sides, W7), and `CTC1`'s `CheckFPException()`
after the write ("The register is written before the exception occurs", p.149) against
`Mips.Fp.fcsrTrapPending`. Release 6 (R6-5): `UFR`/`UNFR` and every register that does not exist
raise Reserved Instruction on both sides ("Release 6 traps"; the manual transcribes the Release 6 arms).

`ctc1_refines` assumes `FcsrReservedZero s` (the stored FCSR holds only its R/W fields): the manual
writes `FCSRWrite` of a word built from the old FCSR, which drops the non-R/W bits, while the model's
`writeControl` keeps the old ones. `cfc1_refines` keeps that hypothesis but no longer needs it
(`FCSRRead` is the model's `readFCSR` for every FCSR).
-/

namespace Refine

open Manual

theorem fir_model : modelCtx.impl.FIR = 0x00F30000#32 := rfl

/-- `Ops.CFC1` under the model's choices: the model's `readControl`, Reserved Instruction for
`none`. -/
theorem cfc1_run (s : State) (rt fs : W32) :
    (Ops.CFC1 rt fs).run modelCtx { arch := abs s } =
      match Mips.Fp.readControl s.fcsr fs.toNat with
      | some v => (.ok (), { arch := writeGPR (abs s) (reg rt) v })
      | none => (.signal .ReservedInstruction, { arch := abs s }) := by
  simp only [Pseudo.run, Ops.CFC1, bind, Pseudo.get, Pseudo.impl, fcsrRead_abs]
  by_cases h0 : fs = 0#32
  · subst h0; simp only [beq_self_eq_true, ↓reduceIte, fir_model]; rfl
  by_cases h1 : fs = 1#32
  · subst h1; rfl
  by_cases h4 : fs = 4#32
  · subst h4; rfl
  by_cases h5 : fs = 5#32
  · subst h5; rfl
  by_cases h25 : fs = 25#32
  · subst h25; simp only [BitVec.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
      cfc1_fccr]; rfl
  by_cases h26 : fs = 26#32
  · subst h26; simp only [BitVec.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
      cfc1_fexr]; rfl
  by_cases h28 : fs = 28#32
  · subst h28; simp only [BitVec.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
      cfc1_fenr]; rfl
  by_cases h31 : fs = 31#32
  · subst h31; rfl
  have hn : Mips.Fp.readControl s.fcsr fs.toNat = none := by
    have := toNat_ne_of_ne h0 (by omega); have := toNat_ne_of_ne h5 (by omega)
    have := toNat_ne_of_ne h25 (by omega); have := toNat_ne_of_ne h26 (by omega)
    have := toNat_ne_of_ne h28 (by omega); have := toNat_ne_of_ne h31 (by omega)
    unfold Mips.Fp.readControl; split <;> simp_all
  simp only [beq_iff_eq, h0, h1, h4, h5, h25, h26, h28, h31, ↓reduceIte, hn]
  rfl

/-- **CFC1 refines** (for the states of `Inv`; `FcsrReservedZero` is not used since R6-5). -/
theorem cfc1_refines (s : State) (hg : Good s) (_hres : FcsrReservedZero s) (rt fs w : W32)
    (hw : enc (.cfc1 rt fs) = some w) :
    Execute modelCtx w (.cfc1 rt fs) (abs s) = some (abs (execInstr s (.cfc1 rt fs))) := by
  obtain ⟨hsz, -, -⟩ := hg
  have hw' : w = rFormat 0x11#32 0x02#32 rt fs 0#32 0#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.CFC1 rt fs) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.cfc1 rt fs) =
      match Mips.Fp.readControl s.fcsr fs.toNat with
      | some v => mkNext s (writeReg s (regIdx rt) v)
      | none => takeException s excCodeRI := rfl
  rw [hb, cfc1_run]
  cases Mips.Fp.readControl s.fcsr fs.toNat with
  | some v =>
    simp only
    rw [abs_mkNext_writeReg _ _ _ hsz, complete_plain, regIdx_eq_reg]
  | none =>
    exact congrArg some (gep_take s .ReservedInstruction rfl excCodeRI (by decide))

/-- The write part of `CTC1` (before `CheckFPException()`), under `modelOracle` and for an FCSR
holding only its R/W fields: the model's `Mips.Fp.writeControl`, Reserved Instruction for `none`. -/
theorem ctc1_run (s : State) (h0 : readReg s 0 = 0#32) (hres : FcsrReservedZero s) (rt fs : W32) :
    (Ops.CTC1 rt fs).run modelCtx { arch := abs s } =
      match Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt)) with
      | some F => CheckFPException modelCtx { arch := { abs s with FCSR := F } }
      | none => (.signal .ReservedInstruction, { arch := abs s }) := by
  have hrz : RZ s.fcsr := hres
  simp only [Pseudo.run, Ops.CTC1, bind, Pseudo.get, Pseudo.oracle, GPR,
    readGPR_abs s h0, low_32, ← regIdx_eq_reg]
  generalize readReg s (regIdx rt) = v
  have ho : modelCtx.oracle = modelOracle := rfl
  by_cases h1 : fs = 1#32
  · subst h1; rfl
  by_cases h4 : fs = 4#32
  · subst h4; rfl
  by_cases h5 : fs = 5#32
  · subst h5; rfl
  by_cases h6 : fs = 6#32
  · subst h6; rfl
  by_cases h25 : fs = 25#32
  · subst h25
    simp only [BitVec.reduceBEq, Bool.false_eq_true, Bool.or_false, ↓reduceIte,
      beq_self_eq_true]
    cases (bits v 31 8 != 0#24)
    · simp only [Bool.false_eq_true, ↓reduceIte, Pseudo.modify, abs_FCSR, ctc1_fccr _ _ hrz]
      rfl
    · simp only [↓reduceIte, ho, modelOracle, resolve, beq_self_eq_true]
      rfl
  by_cases h26 : fs = 26#32
  · subst h26
    simp only [BitVec.reduceBEq, Bool.false_eq_true, Bool.or_false, ↓reduceIte]
    cases (bits v 31 18 != 0#14 || bits v 11 7 != 0#5 || bits v 2 0 != 0#3)
    · simp only [Bool.false_eq_true, ↓reduceIte, Pseudo.modify, abs_FCSR, ctc1_fexr _ _ hrz]
      rfl
    · simp only [↓reduceIte, ho, modelOracle, resolve, BitVec.reduceBEq, Bool.false_eq_true,
        abs_FCSR, ctc1_fexr' _ _ hrz]
      rfl
  by_cases h28 : fs = 28#32
  · subst h28
    simp only [BitVec.reduceBEq, Bool.false_eq_true, Bool.or_false, ↓reduceIte]
    cases (bits v 31 12 != 0#20 || bits v 6 3 != 0#4)
    · simp only [Bool.false_eq_true, ↓reduceIte, Pseudo.modify, abs_FCSR, ctc1_fenr _ _ hrz]
      rfl
    · simp only [↓reduceIte, ho, modelOracle, resolve, BitVec.reduceBEq, Bool.false_eq_true,
        abs_FCSR, ctc1_fenr' _ _ hrz]
      rfl
  by_cases h31 : fs = 31#32
  · subst h31
    simp only [BitVec.reduceBEq, Bool.false_eq_true, Bool.or_false, ↓reduceIte]
    cases (bits v 22 18 != 0#5)
    · simp only [Bool.false_eq_true, ↓reduceIte, Pseudo.modify]
      rfl
    · simp only [↓reduceIte, ho, modelOracle, resolve, BitVec.reduceBEq, Bool.false_eq_true]
      rfl
  have hn : Mips.Fp.writeControl s.fcsr fs.toNat v = none := by
    have := toNat_ne_of_ne h25 (by omega); have := toNat_ne_of_ne h26 (by omega)
    have := toNat_ne_of_ne h28 (by omega); have := toNat_ne_of_ne h31 (by omega)
    unfold Mips.Fp.writeControl; split <;> simp_all
  simp only [beq_false_of_ne h1, beq_false_of_ne h4, beq_false_of_ne h5, beq_false_of_ne h6,
    beq_false_of_ne h25, beq_false_of_ne h26, beq_false_of_ne h28, beq_false_of_ne h31, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hn]
  rfl

/-- **CTC1 refines**: the write, then `CheckFPException()` on the written FCSR; Reserved Instruction
for a register that is not writable in Release 6. R6-5: assumes `FcsrReservedZero s` (part of `Inv`). -/
theorem ctc1_refines (s : State) (hg : Good s) (hres : FcsrReservedZero s) (rt fs w : W32)
    (hw : enc (.ctc1 rt fs) = some w) :
    Execute modelCtx w (.ctc1 rt fs) (abs s) = some (abs (execInstr s (.ctc1 rt fs))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = rFormat 0x11#32 0x06#32 rt fs 0#32 0#32 := Option.some.inj (hw.symm.trans rfl)
  subst hw'
  apply cop1_execute s _ _ (Ops.CTC1 rt fs) rfl (by simp [InCop1Space, opcode_rFormat])
    (by simp [InCop0Space, opcode_rFormat]) rfl rfl rfl rfl
  intro _
  have hb : execBody s (.ctc1 rt fs) =
      match Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt)) with
      | none => takeException s excCodeRI
      | some f =>
        if Mips.Fp.fcsrTrapPending f then takeException { s with fcsr := f } excCodeFPE
        else mkNext s { s with fcsr := f } := rfl
  rw [hb, ctc1_run s h0 hres]
  cases Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt)) with
  | none => exact congrArg some (gep_take s .ReservedInstruction rfl excCodeRI (by decide))
  | some F =>
    simp only [checkFP_run]
    cases Mips.Fp.fcsrTrapPending F
    · simp only [Bool.false_eq_true, ↓reduceIte, complete_plain]
      rw [mkNext, abs_advance _ _ (by rfl)]
      rfl
    · simp only [↓reduceIte]
      exact congrArg some (gep_take { s with fcsr := F } .FloatingPoint rfl excCodeFPE (by decide))

end Refine
