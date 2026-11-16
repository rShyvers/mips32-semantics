import Semantics.Exec.Base

/-!
# Exec.FpuControl — CFC1 and CTC1

The execution of CFC1 and CTC1 (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of CFC1 and CTC1; `none` for every other instruction. -/
def execFpuControl (s : State) : Instruction → Option State
  -- `cfc1` (MD00086 Vol II-A Rev 6.06, CFC1, p.129-130): FIR (0), FCCR (25),
  -- FEXR (26), FENR (28), FCSR (31) via `Mips.Fp.readControl`. Any other
  -- register number is UNPREDICTABLE; pinned to read 0.
  | .cfc1 rt fs => some <|
    mkNext s (writeReg s (regIdx rt) ((Mips.Fp.readControl s.fcsr fs.toNat).getD 0#32))
  -- `ctc1` (MD00086 Vol II-A Rev 6.06, CTC1, p.149-151): the register is
  -- written (`Mips.Fp.writeControl`: reserved bits of the written value,
  -- UNPREDICTABLE if nonzero, are ignored; FIR is read-only), then
  -- `CheckFPException()`: "The register is written before the exception
  -- occurs". Any other register number is UNPREDICTABLE; pinned to no write,
  -- but the Operation's `CheckFPException()` still follows the UNPREDICTABLE
  -- arm (CTC1 p.150: only the `UFR`/`UNFR` arm is marked "end of
  -- instruction"), so an FCSR already holding an enabled Cause bit (or
  -- `Cause.E`) traps (7C S4b; SPEC-NOTES §9 item 13, `ctc1` pins).
  | .ctc1 rt fs => some <|
    match Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt)) with
    | none =>
      if Mips.Fp.fcsrTrapPending s.fcsr then takeException s excCodeFPE else mkNext s s
    | some f =>
      if Mips.Fp.fcsrTrapPending f then takeException { s with fcsr := f } excCodeFPE
      else mkNext s { s with fcsr := f }
  | _ => none
