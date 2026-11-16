import Semantics.Exec.Base

/-!
# Exec.Immediate — the integer instructions with an immediate operand

Including the Release 6 PC-relative instructions (`addiupc`, `auipc`, `aluipc`, `lwpc`), whose
immediate is added to the PC.

The execution of the integer instructions with an immediate operand (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

-- BEGIN R6-4
/-- Sign-extend the low 19 bits of a word to 32 bits: the 19-bit `immediate`/`offset` of the Release 6
`ADDIUPC`/`LWPC` (MD00086 Vol II-A Rev 6.06, ADDIUPC p.37, LWPC p.246). -/
def signExt19 (w : W32) : W32 :=
  (w.extractLsb 18 0).signExtend 32
-- END R6-4

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
  -- BEGIN R6-4
  -- The Release 6 PC-relative instructions (PCREL): `s.pc` is the address of the instruction itself,
  -- also in a delay slot (they are not control transfers). ADDIUPC p.37, AUIPC p.48, ALUIPC p.43,
  -- LWPC p.246 (a word load at `PC + sign_extend(offset) << 2`; `PC` is word-aligned, so the
  -- alignment check never fires).
  | .addiupc rs imm => some <|
    mkNext s (writeReg s (regIdx rs) (s.pc + (signExt19 imm <<< 2)))
  | .auipc rs imm => some <|
    mkNext s (writeReg s (regIdx rs) (s.pc + (zeroExt16 imm <<< 16)))
  | .aluipc rs imm => some <|
    mkNext s (writeReg s (regIdx rs) ((s.pc + (zeroExt16 imm <<< 16)) &&& ~~~0xFFFF#32))
  | .lwpc rs off => some <|
    let addr := s.pc + (signExt19 off <<< 2)
    match readMemWord s addr with
    | none => takeAddressException s excCodeAdEL addr
    | some v => mkNext s (writeReg s (regIdx rs) v)
  -- END R6-4
  | _ => none
