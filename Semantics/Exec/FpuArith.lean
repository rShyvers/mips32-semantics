import Semantics.Exec.Base

/-!
# Exec.FpuArith — the FPU arithmetic instructions

The execution of the FPU arithmetic instructions (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of the FPU arithmetic instructions; `none` for every other instruction. -/
def execFpuArith (s : State) : Instruction → Option State
  -- Single-precision arithmetic: `Mips.Fp` on the raw bit patterns, under
  -- the FCSR environment; `fpFinishS` records the exceptions / traps.
  | .addS fd fs ft => some <|
    fpFinishS s fd (Mips.Fp.f32Add (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .subS fd fs ft => some <|
    fpFinishS s fd (Mips.Fp.f32Sub (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .mulS fd fs ft => some <|
    fpFinishS s fd (Mips.Fp.f32Mul (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .divS fd fs ft => some <|
    fpFinishS s fd (Mips.Fp.f32Div (fpEnv s) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
  | .sqrtS fd fs => some <|
    fpFinishS s fd (Mips.Fp.f32Sqrt (fpEnv s) (readFpReg s (regIdx fs)))
  -- `abs`/`neg` are arithmetic (`FIR.Has2008 = 0`): a NaN signals Invalid.
  | .absS fd fs => some <| fpFinishS s fd (Mips.Fp.f32Abs (readFpReg s (regIdx fs)))
  | .negS fd fs => some <| fpFinishS s fd (Mips.Fp.f32Neg (readFpReg s (regIdx fs)))
  | .recipS fd fs => some <|
    fpFinishS s fd (Mips.Fp.f32Recip (fpEnv s) (readFpReg s (regIdx fs)))
  | .rsqrtS fd fs => some <|
    fpFinishS s fd (Mips.Fp.f32Rsqrt (fpEnv s) (readFpReg s (regIdx fs)))
  -- Double-precision arithmetic, on the register pairs.
  | .addD fd fs ft => some <|
    fpFinishD s fd (Mips.Fp.f64Add (fpEnv s) (readFpD s fs) (readFpD s ft))
  | .subD fd fs ft => some <|
    fpFinishD s fd (Mips.Fp.f64Sub (fpEnv s) (readFpD s fs) (readFpD s ft))
  | .mulD fd fs ft => some <|
    fpFinishD s fd (Mips.Fp.f64Mul (fpEnv s) (readFpD s fs) (readFpD s ft))
  | .divD fd fs ft => some <|
    fpFinishD s fd (Mips.Fp.f64Div (fpEnv s) (readFpD s fs) (readFpD s ft))
  | .sqrtD fd fs => some <| fpFinishD s fd (Mips.Fp.f64Sqrt (fpEnv s) (readFpD s fs))
  | .absD fd fs => some <| fpFinishD s fd (Mips.Fp.f64Abs (readFpD s fs))
  | .negD fd fs => some <| fpFinishD s fd (Mips.Fp.f64Neg (readFpD s fs))
  | .recipD fd fs => some <| fpFinishD s fd (Mips.Fp.f64Recip (fpEnv s) (readFpD s fs))
  | .rsqrtD fd fs => some <| fpFinishD s fd (Mips.Fp.f64Rsqrt (fpEnv s) (readFpD s fs))
  | _ => none
