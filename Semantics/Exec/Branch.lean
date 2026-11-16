import Semantics.Exec.Base

/-!
# Exec.Branch — the conditional branches with a delay slot, NAL and BAL

The execution of the conditional branches with a delay slot, NAL and BAL (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of the conditional branches with a delay slot, NAL and BAL; `none` for every other instruction. -/
def execBranch (s : State) : Instruction → Option State
  -- Control flow: one architectural delay slot per branch/jump (SPEC-NOTES
  -- §9 item 1; INSTRUCTION-REF Global rule 3). No branch/jump changes `pc`
  -- to its target: it moves to `pcNext = pc + 4` (the delay-slot
  -- instruction) and records where control goes after that instruction in
  -- `pendingBranch` — the target `pcNext + (signExt16 imm <<< 2)` if taken,
  -- the fall-through address `pc + 8` if not. `advance`/`mkNext` commits it
  -- when the delay-slot instruction retires; `exceptionEntry` abandons it if
  -- that instruction faults. Jumps schedule a target whose top 4 bits come
  -- from `pcNext`.
  | .beq rs rt imm => some <|
    let pcNext := s.pc + 4#32
    if readReg s (regIdx rs) == readReg s (regIdx rt) then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bne rs rt imm => some <|
    let pcNext := s.pc + 4#32
    if readReg s (regIdx rs) == readReg s (regIdx rt) then
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
    else
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
  | .blez rs imm => some <|
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) ≤ 0 then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bgtz rs imm => some <|
    let pcNext := s.pc + 4#32
    if 0 < asSigned (readReg s (regIdx rs)) then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  -- REGIMM zero-comparison branches (opcode 0x01; MD00086 Rev 2.50 §3.2,
  -- Table 3-2). `bltz`/`bgez` are plain conditional branches, same shape as
  -- `blez`/`bgtz` above. `bltzal`/`bgezal` additionally link `$ra` to
  -- `pcNext + 4` (`pc + 8`, past the delay slot, same convention as `jal`)
  -- -- real MIPS32 performs this link **unconditionally**, on every
  -- execution of the instruction, regardless of whether the branch itself
  -- is taken; only the branch transfer is conditional.
  | .bltz rs imm => some <|
    let pcNext := s.pc + 4#32
    if asSigned (readReg s (regIdx rs)) < 0 then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  | .bgez rs imm => some <|
    let pcNext := s.pc + 4#32
    if 0 ≤ asSigned (readReg s (regIdx rs)) then
      { s with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
    else
      { s with pc := pcNext, pendingBranch := some (s.pc + 8#32) }
  -- NAL (MD00086 Vol II-A Rev 6.06, NAL, p.306): `GPR[31] ← PC + 8`; "NAL is considered to be a
  -- not-taken branch, with a delay slot": the next instruction is in a delay slot whose transfer is
  -- the fall-through `pc + 8`.
  | .nal _ => some <|
    let s' := writeReg s 31 (s.pc + 8#32)
    { s' with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }
  -- BAL (MD00086 Vol II-A Rev 6.06, BAL, p.50): `I: target_offset ← sign_extend(offset || 0^2);
  -- GPR[31] ← PC + 8; I+1: PC ← PC + target_offset`.
  | .bal imm => some <|
    let pcNext := s.pc + 4#32
    let s' := writeReg s 31 (pcNext + 4#32)
    { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
  | _ => none
