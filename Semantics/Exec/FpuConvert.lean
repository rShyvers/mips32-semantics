import Semantics.Exec.Base

/-!
# Exec.FpuConvert — the FPU conversions

The execution of the FPU conversions (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of the FPU conversions; `none` for every other instruction. -/
def execFpuConvert (s : State) : Instruction → Option State
  -- Float → word: fixed rounding direction for round/trunc/ceil/floor,
  -- FCSR.RM for `cvt.w`.
  | .roundWS fd fs => some <| fpFinishS s fd (Mips.Fp.f32ToW32 .RN (readFpReg s (regIdx fs)))
  | .truncWS fd fs => some <| fpFinishS s fd (Mips.Fp.f32ToW32 .RZ (readFpReg s (regIdx fs)))
  | .ceilWS fd fs => some <| fpFinishS s fd (Mips.Fp.f32ToW32 .RP (readFpReg s (regIdx fs)))
  | .floorWS fd fs => some <| fpFinishS s fd (Mips.Fp.f32ToW32 .RM (readFpReg s (regIdx fs)))
  | .cvtWS fd fs => some <|
    fpFinishS s fd (Mips.Fp.f32ToW32 (Mips.Fp.getRM s.fcsr) (readFpReg s (regIdx fs)))
  | .cvtDS fd fs => some <| fpFinishD s fd (Mips.Fp.f32ToF64 (readFpReg s (regIdx fs)))
  | .cvtSW fd fs => some <| fpFinishS s fd (Mips.Fp.w32ToF32 (fpEnv s) (readFpReg s (regIdx fs)))
  | .cvtDW fd fs => some <| fpFinishD s fd (Mips.Fp.w32ToF64F (readFpReg s (regIdx fs)))
  | .roundWD fd fs => some <| fpFinishS s fd (Mips.Fp.f64ToW32 .RN (readFpD s fs))
  | .truncWD fd fs => some <| fpFinishS s fd (Mips.Fp.f64ToW32 .RZ (readFpD s fs))
  | .ceilWD fd fs => some <| fpFinishS s fd (Mips.Fp.f64ToW32 .RP (readFpD s fs))
  | .floorWD fd fs => some <| fpFinishS s fd (Mips.Fp.f64ToW32 .RM (readFpD s fs))
  | .cvtWD fd fs => some <| fpFinishS s fd (Mips.Fp.f64ToW32 (Mips.Fp.getRM s.fcsr) (readFpD s fs))
  | .cvtSD fd fs => some <| fpFinishS s fd (Mips.Fp.f64ToF32 (fpEnv s) (readFpD s fs))
  | _ => none
