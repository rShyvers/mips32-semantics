import Semantics.Exec.Base

/-!
# Exec.Immediate — the integer instructions with an immediate operand

The execution of the integer instructions with an immediate operand (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of the integer instructions with an immediate operand; `none` for every other instruction. -/
def execImmediate (s : State) : Instruction → Option State
  | .addiu rs rt imm => some <|
    mkNext s (writeReg s (regIdx rt) (readReg s (regIdx rs) + signExt16 imm))
  | .slti rs rt imm => some <|
    let v := if asSigned (readReg s (regIdx rs)) < asSigned (signExt16 imm)
             then 1#32 else 0#32
    mkNext s (writeReg s (regIdx rt) v)
  | .sltiu rs rt imm => some <|
    let v := if (readReg s (regIdx rs)).toNat < (signExt16 imm).toNat
             then 1#32 else 0#32
    mkNext s (writeReg s (regIdx rt) v)
  | .andi rs rt imm => some <|
    mkNext s (writeReg s (regIdx rt) (readReg s (regIdx rs) &&& zeroExt16 imm))
  | .ori rs rt imm => some <|
    mkNext s (writeReg s (regIdx rt) (readReg s (regIdx rs) ||| zeroExt16 imm))
  | .xori rs rt imm => some <|
    mkNext s (writeReg s (regIdx rt) (readReg s (regIdx rs) ^^^ zeroExt16 imm))
  -- AUI (MD00086 Vol II-A Rev 6.06, AUI, p.47): `GPR[rt] ← GPR[rs] + sign_extend(immediate << 16)`;
  -- with `rs = 0` this is LUI (p.47, LUI p.233).
  | .aui rs rt imm => some <|
    mkNext s (writeReg s (regIdx rt) (readReg s (regIdx rs) + (zeroExt16 imm <<< 16)))
  | _ => none
