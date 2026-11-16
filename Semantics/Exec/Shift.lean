import Semantics.Exec.Base

/-!
# Exec.Shift — the shifts and rotates

The execution of the shifts and rotates (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of the shifts and rotates; `none` for every other instruction. -/
def execShift (s : State) : Instruction → Option State
  -- R-type shifts
  -- The shift amount is the 5-bit `sa` field (`s ← sa`, MD00086 Vol II-A Rev
  -- 6.06, SLL p.376, SRL p.385, SRA p.383): `% 32` of the constructor value
  -- (which `decode` always produces below 32).
  | .sll rd rt shamt => some <|
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt) <<< (shamt.toNat % 32)))
  | .srl rd rt shamt => some <|
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt) >>> (shamt.toNat % 32)))
  | .sra rd rt shamt => some <|
    mkNext s (writeReg s (regIdx rd) ((readReg s (regIdx rt)).sshiftRight (shamt.toNat % 32)))
  -- R-type variable shifts (MIPS32): the shift amount comes from `$rs`'s
  -- low 5 bits (`extractLsb 4 0`), not a fixed `shamt` field \u2014 so e.g. a
  -- shift-amount register holding 33 (0b100001) behaves identically to one
  -- holding 1, per the real MIPS32 ISA (docs/spec/MIPS-COVERAGE-GAPS.md §3.4).
  | .sllv rd rt rs => some <|
    let amt := ((readReg s (regIdx rs)).extractLsb 4 0).toNat
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt) <<< amt))
  | .srlv rd rt rs => some <|
    let amt := ((readReg s (regIdx rs)).extractLsb 4 0).toNat
    mkNext s (writeReg s (regIdx rd) (readReg s (regIdx rt) >>> amt))
  | .srav rd rt rs => some <|
    let amt := ((readReg s (regIdx rs)).extractLsb 4 0).toNat
    mkNext s (writeReg s (regIdx rd) ((readReg s (regIdx rt)).sshiftRight amt))
  -- R-type rotate (MIPS32r2): bits shifted off the bottom wrap around to the
  -- top, unlike `srl`/`srlv`'s zero-fill on the same input
  -- (docs/spec/MIPS-COVERAGE-GAPS.md section 3.4). `BitVec.rotateRight` already
  -- reduces its shift amount mod the bitvector width, matching the real
  -- MIPS32 `sa`/`$rs & 0x1f` range (0-31) exactly.
  | .rotr rd rt sa => some <|
    mkNext s (writeReg s (regIdx rd) ((readReg s (regIdx rt)).rotateRight (sa.toNat % 32)))
  | .rotrv rd rt rs => some <|
    let amt := ((readReg s (regIdx rs)).extractLsb 4 0).toNat
    mkNext s (writeReg s (regIdx rd) ((readReg s (regIdx rt)).rotateRight amt))
  | _ => none
