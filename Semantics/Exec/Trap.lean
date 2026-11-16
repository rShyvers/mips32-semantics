import Semantics.Exec.Base

/-!
# Exec.Trap — the register traps and BREAK

The execution of the register traps and BREAK (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of the register traps and BREAK; `none` for every other instruction. -/
def execTrap (s : State) : Instruction → Option State
  -- Trap-on-condition (coprocessor-0 exception model, real MIPS32 ISA; see
  -- `takeException` above and `docs/spec/INSTRUCTION-REF.md`). Trap-not-taken
  -- behaves like an ordinary instruction: `mkNext s` falls through to
  -- `pc + 4` with no CP0 state touched at all.
  | .teq rs rt _ => some <|
    if readReg s (regIdx rs) == readReg s (regIdx rt) then takeException s excCodeTr else mkNext s s
  | .tne rs rt _ => some <|
    if readReg s (regIdx rs) ≠ readReg s (regIdx rt) then takeException s excCodeTr else mkNext s s
  | .tlt rs rt _ => some <|
    if asSigned (readReg s (regIdx rs)) < asSigned (readReg s (regIdx rt))
    then takeException s excCodeTr else mkNext s s
  | .tge rs rt _ => some <|
    if asSigned (readReg s (regIdx rs)) ≥ asSigned (readReg s (regIdx rt))
    then takeException s excCodeTr else mkNext s s
  | .tltu rs rt _ => some <|
    if (readReg s (regIdx rs)).toNat < (readReg s (regIdx rt)).toNat
    then takeException s excCodeTr else mkNext s s
  | .tgeu rs rt _ => some <|
    if (readReg s (regIdx rs)).toNat ≥ (readReg s (regIdx rt)).toNat
    then takeException s excCodeTr else mkNext s s
  -- break: unconditional trap (coprocessor-0 exception model).
  | .break _ => some <| takeException s excCodeBp
  | _ => none
