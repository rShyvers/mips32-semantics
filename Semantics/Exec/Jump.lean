import Semantics.Exec.Base

/-!
# Exec.Jump — the jumps (J, JAL, JALR, JALR.HB, JIC, JIALC)

The execution of the jumps (J, JAL, JALR, JALR.HB and the Release 6 compact jumps JIC, JIALC)
(`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot or forbidden
slot; coprocessor usable); `none` for every instruction of another family.
-/

/-- The effect of the jumps (J, JAL, JALR, JALR.HB, JIC, JIALC); `none` for every other
instruction. -/
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
  -- JIC/JIALC (MD00086 Vol II-A Rev 6.06, JIC p.205, JIALC p.203): `temp ← GPR[rt] +
  -- sign_extend(offset)` (the offset is not shifted), JIALC `GPR[31] ← PC + 4`, then `PC ← temp` at
  -- once ("has neither a delay slot nor a forbidden slot"; `Config3.ISA = Config1.CA = 0`, MIPS32
  -- only). `temp` is read before the link is written, so `jialc $31, off` jumps to the old `$31`.
  | .jic rt off => some
    { s with pc := readReg s (regIdx rt) + signExt16 off, pendingBranch := none }
  | .jialc rt off => some <|
    let temp := readReg s (regIdx rt) + signExt16 off
    { writeReg s 31 (s.pc + 4#32) with pc := temp, pendingBranch := none }
  | _ => none
