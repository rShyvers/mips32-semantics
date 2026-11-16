import Semantics.Exec.Base

/-!
# Exec.IntArith — the integer register-register arithmetic and logic instructions

The execution of the integer register-register arithmetic and logic instructions (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

-- BEGIN R6-4
/-- The high word of the signed 64-bit product (`MUH`, MD00086 Vol II-A Rev 6.06, p.301). -/
def mulHiS (x y : W32) : W32 := (x.signExtend 64 * y.signExtend 64).extractLsb' 32 32

/-- The high word of the unsigned 64-bit product (`MUHU`, p.301). -/
def mulHiU (x y : W32) : W32 := (x.zeroExtend 64 * y.zeroExtend 64).extractLsb' 32 32

/-- The value `DIV`/`MOD`/`DIVU`/`MODU` write (MD00086 Vol II-A Rev 6.06, DIV MOD DIVU MODU,
p.168-169): `op x y` for a nonzero divisor; for a zero divisor, whose result is UNPREDICTABLE
(Restrictions, p.168), the model's pin is the result of dividing by 1: the quotient forms give the
dividend `x`, the remainder forms 0 (`zeroVal`). -/
def divOr (op : W32 → W32 → W32) (zeroVal : W32 → W32) (x y : W32) : W32 :=
  if y = 0#32 then zeroVal x else op x y
-- END R6-4

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
  -- BEGIN R6-4
  -- Release 6 same-width multiply and divide (MUL MUH MULU MUHU p.300-301; DIV MOD DIVU MODU
  -- p.168-169): no exceptions, no HI/LO.
  | .mul rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) * readReg s (regIdx rt)))
  | .muh rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd) (mulHiS (readReg s (regIdx rs)) (readReg s (regIdx rt))))
  | .mulu rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rs) * readReg s (regIdx rt)))
  | .muhu rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd) (mulHiU (readReg s (regIdx rs)) (readReg s (regIdx rt))))
  | .div rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd) (divOr BitVec.sdiv id (readReg s (regIdx rs)) (readReg s (regIdx rt))))
  | .mod rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd)
      (divOr BitVec.srem (fun _ => 0#32) (readReg s (regIdx rs)) (readReg s (regIdx rt))))
  | .divu rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd) (divOr (· / ·) id (readReg s (regIdx rs)) (readReg s (regIdx rt))))
  | .modu rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd)
      (divOr (· % ·) (fun _ => 0#32) (readReg s (regIdx rs)) (readReg s (regIdx rt))))
  -- SELEQZ/SELNEZ (p.369): `$rs` if `$rt` is zero / nonzero, else 0.
  | .seleqz rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd) (if readReg s (regIdx rt) = 0#32 then readReg s (regIdx rs) else 0#32))
  | .selnez rs rt rd => some <|
    mkNext s (writeReg s (regIdx rd) (if readReg s (regIdx rt) = 0#32 then 0#32 else readReg s (regIdx rs)))
  -- LSA (p.232): `($rs << (sa+1)) + $rt`, `sa` the 2-bit field.
  | .lsa rs rt rd sa => some <|
    mkNext s (writeReg s (regIdx rd)
      ((readReg s (regIdx rs) <<< ((sa &&& 3#32).toNat + 1)) + readReg s (regIdx rt)))
  -- END R6-4
  | _ => none
