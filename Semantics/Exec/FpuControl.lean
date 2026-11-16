import Semantics.Exec.Base

/-!
# Exec.FpuControl — CFC1 and CTC1

The execution of CFC1 and CTC1 (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of CFC1 and CTC1; `none` for every other instruction. -/
def execFpuControl (s : State) : Instruction → Option State
  -- `cfc1` (MD00086 Vol II-A Rev 6.06, CFC1, p.129-130, Release 6): FIR (0), FCCR (25),
  -- FEXR (26), FENR (28), FCSR (31) via `Mips.Fp.readControl`; `FRE` (5) reads `UNPREDICTABLE`,
  -- pinned to 0; every other register number raises Reserved Instruction ("Release 6 traps").
  -- The page's final `if Config2AR < 2 then GPR[rt] ← temp` would never write `GPR[rt]` in Release
  -- 6; read as the unconditional write of the earlier releases (misprint, SPEC-NOTES).
  | .cfc1 rt fs => some <|
    match Mips.Fp.readControl s.fcsr fs.toNat with
    | some v => mkNext s (writeReg s (regIdx rt) v)
    | none => takeException s excCodeRI
  -- `ctc1` (MD00086 Vol II-A Rev 6.06, CTC1, p.149-151, Release 6): the register is
  -- written (`Mips.Fp.writeControl`: reserved bits of the written value,
  -- UNPREDICTABLE if nonzero, are ignored; FCCR's FCC bits are reserved), then
  -- `CheckFPException()`: "The register is written before the exception
  -- occurs". FIR, `UFR`/`UNFR`, `FRE`/`NFRE` (UNPREDICTABLE, pinned) and every register that does
  -- not exist raise Reserved Instruction ("Release 6 traps").
  | .ctc1 rt fs => some <|
    match Mips.Fp.writeControl s.fcsr fs.toNat (readReg s (regIdx rt)) with
    | none => takeException s excCodeRI
    | some f =>
      if Mips.Fp.fcsrTrapPending f then takeException { s with fcsr := f } excCodeFPE
      else mkNext s { s with fcsr := f }
  | _ => none
