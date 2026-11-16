import Semantics.Exec.Base

/-!
# Exec.Jump — the jumps (J, JAL, JALR, JALR.HB)

The execution of the jumps (J, JAL, JALR, JALR.HB) (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of the jumps (J, JAL, JALR, JALR.HB); `none` for every other instruction. -/
def execJump (s : State) : Instruction → Option State
  -- `instr_index` is the 26-bit field of the J format (MD00086 Vol II-A Rev 6.06, J p.194, JAL
  -- p.195: "PC <- PC_{GPRLEN-1..28} || instr_index || 0^2"): only the low 26 bits of `target`
  -- are used (`decode` produces nothing wider; an `Instruction` built by hand may hold more).
  | .j target => some <|
    let pcNext := s.pc + 4#32
    { s with pc := pcNext,
             pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| ((target &&& 0x3FFFFFF#32) <<< 2)) }
  | .jal target => some <|
    -- `$ra` links to `pc + 8` — past the delay slot — not `pcNext` (`pc + 4`):
    -- real MIPS32's `jal` link value is the address of the instruction
    -- *after* the delay slot, since the delay-slot instruction itself still
    -- executes before control reaches `$ra` on return.
    let pcNext := s.pc + 4#32
    let linkVal := pcNext + 4#32
    let s' := writeReg s 31 linkVal
    { s' with pc := pcNext,
              pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| ((target &&& 0x3FFFFFF#32) <<< 2)) }
  | .jalr rs rd => some <|
    -- `$rd` links to `pc + 8` — past the delay slot — the same `jal` link-value
    -- convention as above. The link target is read before `$rd` is written,
    -- so `jalr $rs, $rs` (rd = rs) still reads the pre-write `$rs` value.
    let pcNext := s.pc + 4#32
    let linkVal := pcNext + 4#32
    let target := readReg s (regIdx rs)
    let s' := writeReg s (regIdx rd) linkVal
    { s' with pc := pcNext, pendingBranch := some target }
  | .jalrHb rs rd => some <|
    let pcNext := s.pc + 4#32
    let linkVal := pcNext + 4#32
    let target := readReg s (regIdx rs)
    let s' := writeReg s (regIdx rd) linkVal
    { s' with pc := pcNext, pendingBranch := some target }
  | _ => none
