import Semantics.Exec.Base

/-!
# Exec.FpuConvert — the FPU conversions

The execution of the FPU conversions (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of the FPU conversions; `none` for every other instruction. -/
def execFpuConvert (s : State) : Instruction → Option State
  -- Float → word / longword: fixed rounding direction for round/trunc/ceil/floor, FCSR.RM for
  -- `cvt.w`/`cvt.l`; the operand flushed per FCSR.FS (`Mips.Fp.Format.flushIn`).
  | .roundWS fd fs => some <| fpFinishS s fd (Mips.Fp.f32ToW32 .RN (fpEnv s).flush (readFpReg s (regIdx fs)))
  | .truncWS fd fs => some <| fpFinishS s fd (Mips.Fp.f32ToW32 .RZ (fpEnv s).flush (readFpReg s (regIdx fs)))
  | .ceilWS fd fs => some <| fpFinishS s fd (Mips.Fp.f32ToW32 .RP (fpEnv s).flush (readFpReg s (regIdx fs)))
  | .floorWS fd fs => some <| fpFinishS s fd (Mips.Fp.f32ToW32 .RM (fpEnv s).flush (readFpReg s (regIdx fs)))
  | .cvtWS fd fs => some <|
    fpFinishS s fd (Mips.Fp.f32ToW32 (fpEnv s).rm (fpEnv s).flush (readFpReg s (regIdx fs)))
  | .cvtDS fd fs => some <| fpFinishD s fd (Mips.Fp.f32ToF64 (fpEnv s).flush (readFpReg s (regIdx fs)))
  | .cvtSW fd fs => some <| fpFinishS s fd (Mips.Fp.w32ToF32 (fpEnv s) (readFpReg s (regIdx fs)))
  | .cvtDW fd fs => some <| fpFinishD s fd (Mips.Fp.w32ToF64F (readFpReg s (regIdx fs)))
  | .roundWD fd fs => some <| fpFinishS s fd (Mips.Fp.f64ToW32 .RN (fpEnv s).flush (readFpD s fs))
  | .truncWD fd fs => some <| fpFinishS s fd (Mips.Fp.f64ToW32 .RZ (fpEnv s).flush (readFpD s fs))
  | .ceilWD fd fs => some <| fpFinishS s fd (Mips.Fp.f64ToW32 .RP (fpEnv s).flush (readFpD s fs))
  | .floorWD fd fs => some <| fpFinishS s fd (Mips.Fp.f64ToW32 .RM (fpEnv s).flush (readFpD s fs))
  | .cvtWD fd fs => some <| fpFinishS s fd (Mips.Fp.f64ToW32 (fpEnv s).rm (fpEnv s).flush (readFpD s fs))
  | .cvtSD fd fs => some <| fpFinishS s fd (Mips.Fp.f64ToF32 (fpEnv s) (readFpD s fs))
  -- BEGIN R6-5
  | .roundLS fd fs => some <| fpFinishD s fd (Mips.Fp.f32ToW64 .RN (fpEnv s).flush (readFpReg s (regIdx fs)))
  | .truncLS fd fs => some <| fpFinishD s fd (Mips.Fp.f32ToW64 .RZ (fpEnv s).flush (readFpReg s (regIdx fs)))
  | .ceilLS fd fs => some <| fpFinishD s fd (Mips.Fp.f32ToW64 .RP (fpEnv s).flush (readFpReg s (regIdx fs)))
  | .floorLS fd fs => some <| fpFinishD s fd (Mips.Fp.f32ToW64 .RM (fpEnv s).flush (readFpReg s (regIdx fs)))
  | .cvtLS fd fs => some <|
    fpFinishD s fd (Mips.Fp.f32ToW64 (fpEnv s).rm (fpEnv s).flush (readFpReg s (regIdx fs)))
  | .roundLD fd fs => some <| fpFinishD s fd (Mips.Fp.f64ToW64 .RN (fpEnv s).flush (readFpD s fs))
  | .truncLD fd fs => some <| fpFinishD s fd (Mips.Fp.f64ToW64 .RZ (fpEnv s).flush (readFpD s fs))
  | .ceilLD fd fs => some <| fpFinishD s fd (Mips.Fp.f64ToW64 .RP (fpEnv s).flush (readFpD s fs))
  | .floorLD fd fs => some <| fpFinishD s fd (Mips.Fp.f64ToW64 .RM (fpEnv s).flush (readFpD s fs))
  | .cvtLD fd fs => some <| fpFinishD s fd (Mips.Fp.f64ToW64 (fpEnv s).rm (fpEnv s).flush (readFpD s fs))
  | .cvtSL fd fs => some <| fpFinishS s fd (Mips.Fp.w64ToF32 (fpEnv s) (readFpD s fs))
  | .cvtDL fd fs => some <| fpFinishD s fd (Mips.Fp.w64ToF64 (fpEnv s) (readFpD s fs))
  -- END R6-5
  | _ => none
