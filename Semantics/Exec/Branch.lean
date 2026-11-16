import Semantics.Exec.Base

/-!
# Exec.Branch — the branches: with a delay slot, NAL, BAL, and the Release 6 compact branches

The execution of the conditional branches with a delay slot, NAL and BAL, and of the Release 6
compact branches (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot or forbidden
slot; coprocessor usable); `none` for every instruction of another family.

**Compact branches** (Release 6; MD00082 Vol I-A Rev 6.01 §5.3.2, p.62; MD00086 Vol II-A Rev 6.06,
BC p.53, BALC p.52, B<cond>C p.82-85, B{LE,GE,GT,LT,EQ,NE}ZALC p.77-79, BOVC/BNVC p.107-108) have no
delay slot: taken, `pc` becomes the target at once (`compactBranch%`). The conditional ones have a
**forbidden slot**: not taken, the next instruction runs as if in the delay slot of a not-taken branch
(`pendingBranch := some (pc + 8)`): a control transfer there raises Reserved Instruction
(`execInstr`), and an exception there is reported with `EPC` = the compact branch and `Cause.BD = 1`
(`exceptionEntry`; MD00082 Vol I-A Rev 6.01 §5.3.2.2, p.62: "If an exception or interrupt prevents
the completion of an instruction in a delay slot or forbidden slot, the hardware reports an Exception
PC (CP0 EPC) of the branch, with a status bit set ... to indicate that the exception was for the
instruction in the delay slot of the branch"; DECISIONS D6, a pin: MD00090 Vol III Rev 6.02 §6.2.3,
p.87, tests only `InstructionInBranchDelaySlot`). Under that pin a forbidden slot behaves exactly as
the delay slot of a not-taken branch, so it is represented as one and needs no state of its own.
-/

-- BEGIN R6-3
/-- Sign-extend the low 21 bits of a word (the `offset` of `BEQZC`/`BNEZC`). -/
def signExt21 (w : W32) : W32 := (w.extractLsb 20 0).signExtend 32

/-- Sign-extend the low 26 bits of a word (the `offset` of `BC`/`BALC`). -/
def signExt26 (w : W32) : W32 := (w.extractLsb 25 0).signExtend 32

/-- **A conditional compact branch** at `p` (the branch's `pc`) with condition `c` and byte offset `o`
(already sign-extended and shifted), on the state `s` (the branch's other effects): taken,
`PC ← p + 4 + o` with no delay slot; not taken, the next instruction is in the forbidden slot
(`pendingBranch := some (p + 8)`, see the module doc). A local macro, not a function: each arm then
*is* the plain `if` on a record update, which the proofs that case over every instruction
(`exec_unfold`) handle as they handle the branches with a delay slot. -/
local macro "compactBranch% " s:term:max p:term:max c:term:max o:term:max : term =>
  `(if $c then { $s with pc := $p + 4#32 + $o, pendingBranch := none }
    else { $s with pc := $p + 4#32, pendingBranch := some ($p + 8#32) })

/-- `GPR[31] ← PC + 4`: the link of `BALC` and the B*ZALC (the address of the instruction after the
branch: "The return link is the address of the instruction immediately following the branch", BALC
p.52, B{LE,GE,GT,LT,EQ,NE}ZALC p.77). A local macro, as `compactBranch%`. -/
local macro "compactLink% " s:term:max : term => `(writeReg $s 31 (($s).pc + 4#32))
-- END R6-3

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
  -- BEGIN R6-3
  -- Compact branches: the condition of each page's Operation, then `compactBranch`. Comparisons are
  -- signed (`asSigned`) except BLTUC/BGEUC (`BitVec.ult`). BOVC/BNVC: signed 32-bit overflow of
  -- `GPR[rs] + GPR[rt]` (`addOverflows`, as `add`). The B*ZALC write the link first, then read
  -- `GPR[rt]` (the order of their Operation, p.78; `rt = 31` is UNPREDICTABLE there).
  | .bc off => some { s with pc := s.pc + 4#32 + (signExt26 off <<< 2), pendingBranch := none }
  | .balc off => some { compactLink% s with pc := s.pc + 4#32 + (signExt26 off <<< 2), pendingBranch := none }
  | .beqc rs rt off => some <|
    compactBranch% s s.pc (readReg s (regIdx rs) == readReg s (regIdx rt)) (signExt16 off <<< 2)
  | .bnec rs rt off => some <|
    compactBranch% s s.pc (readReg s (regIdx rs) != readReg s (regIdx rt)) (signExt16 off <<< 2)
  | .bltc rs rt off => some <|
    compactBranch% s s.pc (decide (asSigned (readReg s (regIdx rs)) < asSigned (readReg s (regIdx rt))))
      (signExt16 off <<< 2)
  | .bgec rs rt off => some <|
    compactBranch% s s.pc (decide (asSigned (readReg s (regIdx rt)) ≤ asSigned (readReg s (regIdx rs))))
      (signExt16 off <<< 2)
  | .bltuc rs rt off => some <|
    compactBranch% s s.pc (BitVec.ult (readReg s (regIdx rs)) (readReg s (regIdx rt))) (signExt16 off <<< 2)
  | .bgeuc rs rt off => some <|
    compactBranch% s s.pc (!BitVec.ult (readReg s (regIdx rs)) (readReg s (regIdx rt))) (signExt16 off <<< 2)
  | .blezc rt off => some <|
    compactBranch% s s.pc (decide (asSigned (readReg s (regIdx rt)) ≤ 0)) (signExt16 off <<< 2)
  | .bgezc rt off => some <|
    compactBranch% s s.pc (decide (0 ≤ asSigned (readReg s (regIdx rt)))) (signExt16 off <<< 2)
  | .bgtzc rt off => some <|
    compactBranch% s s.pc (decide (0 < asSigned (readReg s (regIdx rt)))) (signExt16 off <<< 2)
  | .bltzc rt off => some <|
    compactBranch% s s.pc (decide (asSigned (readReg s (regIdx rt)) < 0)) (signExt16 off <<< 2)
  | .beqzc rs off => some <|
    compactBranch% s s.pc (readReg s (regIdx rs) == 0#32) (signExt21 off <<< 2)
  | .bnezc rs off => some <|
    compactBranch% s s.pc (readReg s (regIdx rs) != 0#32) (signExt21 off <<< 2)
  | .blezalc rt off => some <|
    compactBranch% (compactLink% s) s.pc (decide (asSigned (readReg (compactLink% s) (regIdx rt)) ≤ 0))
      (signExt16 off <<< 2)
  | .bgezalc rt off => some <|
    compactBranch% (compactLink% s) s.pc (decide (0 ≤ asSigned (readReg (compactLink% s) (regIdx rt))))
      (signExt16 off <<< 2)
  | .bgtzalc rt off => some <|
    compactBranch% (compactLink% s) s.pc (decide (0 < asSigned (readReg (compactLink% s) (regIdx rt))))
      (signExt16 off <<< 2)
  | .bltzalc rt off => some <|
    compactBranch% (compactLink% s) s.pc (decide (asSigned (readReg (compactLink% s) (regIdx rt)) < 0))
      (signExt16 off <<< 2)
  | .beqzalc rt off => some <|
    compactBranch% (compactLink% s) s.pc (readReg (compactLink% s) (regIdx rt) == 0#32) (signExt16 off <<< 2)
  | .bnezalc rt off => some <|
    compactBranch% (compactLink% s) s.pc (readReg (compactLink% s) (regIdx rt) != 0#32) (signExt16 off <<< 2)
  | .bovc rs rt off => some <|
    let a := readReg s (regIdx rs)
    let b := readReg s (regIdx rt)
    compactBranch% s s.pc (addOverflows (asSigned a) (asSigned b) (asSigned (a + b))) (signExt16 off <<< 2)
  | .bnvc rs rt off => some <|
    let a := readReg s (regIdx rs)
    let b := readReg s (regIdx rt)
    compactBranch% s s.pc (!addOverflows (asSigned a) (asSigned b) (asSigned (a + b))) (signExt16 off <<< 2)
  -- END R6-3
  | _ => none
