import Semantics.Exec.Base

/-!
# Exec.FpuMove — the FPU moves (MFC1, MTC1, MFHC1, MTHC1, MOV.fmt)

The execution of the FPU moves (MFC1, MTC1, MFHC1, MTHC1, MOV.fmt) (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of the FPU moves (MFC1, MTC1, MFHC1, MTHC1, MOV.fmt); `none` for every other instruction. -/
def execFpuMove (s : State) : Instruction → Option State
  -- Coprocessor 1 (FPU). Every arm below is reached only with
  -- `Status.CU1 = 1` (the `usesCop1` check above).
  -- Raw moves between GPRs and FPRs: no conversion, FCSR untouched.
  | .mfc1 rt fs => some <|
    mkNext s (writeReg s (regIdx rt) (readFpReg s (regIdx fs)))
  | .mtc1 rt fs => some <|
    mkNext s (writeFpReg s (regIdx fs) (readReg s (regIdx rt)))
  -- `mfhc1`/`mthc1`: the high word of the double in `fs` is `FPR[fs+1]`
  -- (FR = 0). "The results are UNPREDICTABLE if Status.FR = 0 and fs is odd"
  -- (MD00086 Vol II-A Rev 6.06, MFHC1 p.271, MTHC1 p.295); pinned to the
  -- same `fs + 1` register.
  | .mfhc1 rt fs => some <|
    mkNext s (writeReg s (regIdx rt) (readFpReg s (regIdx (fs + 1#32))))
  | .mthc1 rt fs => some <|
    mkNext s (writeFpReg s (regIdx (fs + 1#32)) (readReg s (regIdx rt)))
  -- `mov.fmt` is non-arithmetic: raw copy, FCSR untouched.
  | .movS fd fs => some <|
    mkNext s (writeFpReg s (regIdx fd) (readFpReg s (regIdx fs)))
  | .movD fd fs => some <| mkNext s (writeFpD s fd (readFpD s fs))
  | _ => none
