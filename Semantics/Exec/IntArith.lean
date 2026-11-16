import Semantics.Exec.Base

/-!
# Exec.IntArith — the integer register-register arithmetic and logic instructions

The execution of the integer register-register arithmetic and logic instructions (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of the integer register-register arithmetic and logic instructions; `none` for every other instruction. -/
def execIntArith (s : State) : Instruction → Option State
  | .add rs rt rd => some <|
    let av := readReg s (regIdx rs)
    let bv := readReg s (regIdx rt)
    let sumBV := av + bv
    if addOverflows (asSigned av) (asSigned bv) (asSigned sumBV) then
      takeException s excCodeOv
    else
      mkNext s (writeReg s (regIdx rd) sumBV)
  | .addu rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) + readReg s (regIdx rt)))
  | .sub rs rt rd => some <|
    let av := readReg s (regIdx rs)
    let bv := readReg s (regIdx rt)
    let diffBV := av - bv
    if subOverflows (asSigned av) (asSigned bv) (asSigned diffBV) then
      takeException s excCodeOv
    else
      mkNext s (writeReg s (regIdx rd) diffBV)
  | .subu rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) - readReg s (regIdx rt)))
  | .and rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) &&& readReg s (regIdx rt)))
  | .or rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) ||| readReg s (regIdx rt)))
  | .xor rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) ^^^ readReg s (regIdx rt)))
  | .nor rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd) (~~~(readReg s (regIdx rs) ||| readReg s (regIdx rt))))
  | .slt rs rt rd => some <|
    let v := if asSigned (readReg s (regIdx rs)) < asSigned (readReg s (regIdx rt))
             then 1#32 else 0#32
    mkNext s (writeReg s (regIdx rd) v)
  | .sltu rs rt rd => some <|
    let v := if (readReg s (regIdx rs)).toNat < (readReg s (regIdx rt)).toNat
             then 1#32 else 0#32
    mkNext s (writeReg s (regIdx rd) v)
  | _ => none
