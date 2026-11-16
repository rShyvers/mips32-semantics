import Semantics.Tests.StepFixtures

/-!
# `step` tests: branches, `nal`/`bal`, jumps, delay slots, `pause`, `run`

Moved verbatim out of `Semantics/Step.lean` (reviewability restructuring): the definition file now holds definitions only.
Every check that calls `step`/`run` is a `#guard` (see `StepFixtures.lean` for why).
-/

open StepTest

-- ### beq/bne/blez/bgtz: taken schedules a `pendingBranch` and falls
-- through to the delay slot; not-taken behaves exactly as before (SPEC-NOTES
-- §9 item 1). `stepThroughDelaySlot` executes the branch *and* an inert
-- delay-slot instruction, landing on the real target.

-- `beq` taken: the branch's own step falls through to `pcNext` with the
-- real target recorded in `pendingBranch`, not yet applied to `pc`.
#guard (match hstep (prog1 (.beq 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false)
-- ... and the delay-slot instruction's own step is what actually lands on
-- the target.
#guard stepThroughDelaySlot textBase (.beq 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 5#32)])
  = some (textBase + 4#32 + 12#32)
#guard nextPcEq (hstep (prog1 (.beq 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  (textBase + 4#32)
-- not taken: still in a delay slot -- the pending target is the fall-through `pc + 8`
#guard nextPendingEq (hstep (prog1 (.beq 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  (some (textBase + 8#32))
#guard stepThroughDelaySlot textBase (.beq 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 6#32)])
  = some (textBase + 8#32)

#guard stepThroughDelaySlot textBase (.bne 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 6#32)])
  = some (textBase + 4#32 + 12#32)
#guard nextPcEq (hstep (prog1 (.bne 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]))
  (textBase + 4#32)

#guard stepThroughDelaySlot textBase (.blez 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])  -- -5 ≤ 0
  = some (textBase + 4#32 + 8#32)
#guard stepThroughDelaySlot textBase (.blez 8#32 2#32) (setRegs regs0 [(8, 0#32)])  -- 0 ≤ 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (hstep (prog1 (.blez 8#32 2#32)) (setRegs regs0 [(8, 5#32)]))  -- 5 ≤ 0 is false
  (textBase + 4#32)
#guard stepThroughDelaySlot textBase (.bgtz 8#32 2#32) (setRegs regs0 [(8, 5#32)])  -- 5 > 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (hstep (prog1 (.bgtz 8#32 2#32)) (setRegs regs0 [(8, 0#32)]))  -- 0 > 0 is false
  (textBase + 4#32)

-- ### bltz/bgez (REGIMM, opcode 0x01): same `pendingBranch`
-- delay-slot scheduling as blez/bgtz, taken/not-taken for each; the `al`
-- (Release 6: the `al` variants exist only with rs = 0, as `nal`/`bal`, below.)

-- bltz: taken on a negative $rs, not taken on zero/positive
#guard stepThroughDelaySlot textBase (.bltz 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])  -- -5 < 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (hstep (prog1 (.bltz 8#32 2#32)) (setRegs regs0 [(8, 0#32)]))  -- 0 < 0 is false
  (textBase + 4#32)
#guard nextPcEq (hstep (prog1 (.bltz 8#32 2#32)) (setRegs regs0 [(8, 5#32)]))  -- 5 < 0 is false
  (textBase + 4#32)

-- bgez: taken on zero/positive $rs, not taken on negative
#guard stepThroughDelaySlot textBase (.bgez 8#32 2#32) (setRegs regs0 [(8, 0#32)])  -- 0 >= 0
  = some (textBase + 4#32 + 8#32)
#guard stepThroughDelaySlot textBase (.bgez 8#32 2#32) (setRegs regs0 [(8, 5#32)])  -- 5 >= 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (hstep (prog1 (.bgez 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)]))  -- -5 >= 0 is false
  (textBase + 4#32)

-- nal: links $ra to pc + 8 and is a not-taken branch with a delay slot (NAL p.306): after the
-- delay slot, control falls through to pc + 8.
#guard nextRegEq (hstep (prog1 (.nal 2#32)) regs0) 31 (textBase + 8#32)
#guard stepThroughDelaySlot textBase (.nal 2#32) regs0 = some (textBase + 8#32)
-- bal: links $ra to pc + 8 and always branches (BAL p.50).
#guard nextRegEq (hstep (prog1 (.bal 2#32)) regs0) 31 (textBase + 8#32)
#guard stepThroughDelaySlot textBase (.bal 2#32) regs0 = some (textBase + 4#32 + 8#32)

-- Release 6 removed the branch-likely family (BEQL ... BGEZALL): no delay slot is ever
-- nullified, and their encodings do not decode (`Tests/InstructionTests.lean`).

-- ### j/jal: exact targets including top-4-bit preservation from `pc_next`;
-- jal $ra links to `pc + 8` (past the delay slot), not `pc + 4`

private def crossRegionState : State := { regs0 with pc := 0x90400000#32 }
-- `j`'s own step falls through to the delay slot, scheduling the target.
#guard (match hstep (progAt 0x90400000#32 (.j 0x1000#32)) crossRegionState with
        | .next s => s.pc == 0x90400004#32 && s.pendingBranch == some 0x90004000#32
        | .halt _ => false)
#guard stepThroughDelaySlot 0x90400000#32 (.j 0x1000#32) crossRegionState = some 0x90004000#32
-- `jal`: `$ra` is `pc + 8`, and the target lands the same way as `j` after
-- the delay slot.
#guard nextRegEq (hstep (progAt 0x90400000#32 (.jal 0x1000#32)) crossRegionState) 31 0x90400008#32
#guard stepThroughDelaySlot 0x90400000#32 (.jal 0x1000#32) crossRegionState = some 0x90004000#32

-- ### jr/jalr: register-indirect jump/call, same one-delay-slot scheduling
-- as j/jal, but the target comes from a register read. `jr $ra` is the
-- canonical function-return idiom; `jalr $rd, $rs` additionally links `$rd`
-- to `pc + 8`, exactly like `jal`'s link-value convention.

-- `jr`'s own step falls through to the delay slot, scheduling `$rs`'s raw
-- value as the target (no top-4-bit composition, unlike `j`).
#guard (match hstep (progAt 0x90400000#32 (.jalr 8#32 0#32)) (setRegs crossRegionState [(8, 0x80020000#32)]) with
        | .next s => s.pc == 0x90400004#32 && s.pendingBranch == some 0x80020000#32
        | .halt _ => false)
#guard stepThroughDelaySlot 0x90400000#32 (.jalr 8#32 0#32) (setRegs crossRegionState [(8, 0x80020000#32)])
  = some 0x80020000#32
-- the classic `jr $ra` function-return idiom: landing on whatever address
-- was previously linked into `$ra`.
#guard stepThroughDelaySlot textBase (.jalr 31#32 0#32) (setRegs regs0 [(31, 0x00400040#32)])
  = some 0x00400040#32

-- `jalr $rd, $rs`: `$rd` is `pc + 8` (past the delay slot, same convention
-- as `jal`), and the target lands the same way as `jr` after the delay slot.
#guard nextRegEq (hstep (progAt 0x90400000#32 (.jalr 8#32 9#32)) (setRegs crossRegionState [(8, 0x80020000#32)]))
  9 0x90400008#32
#guard stepThroughDelaySlot 0x90400000#32 (.jalr 8#32 9#32) (setRegs crossRegionState [(8, 0x80020000#32)])
  = some 0x80020000#32
-- `jalr $t9, $t9` (rd = rs): the link value overwrites `$rs` only *after*
-- its pre-write value has been captured as the jump target.
#guard nextRegEq (hstep (progAt 0x90400000#32 (.jalr 9#32 9#32)) (setRegs crossRegionState [(9, 0x80020000#32)]))
  9 0x90400008#32
#guard stepThroughDelaySlot 0x90400000#32 (.jalr 9#32 9#32) (setRegs crossRegionState [(9, 0x80020000#32)])
  = some 0x80020000#32

-- a `jr` target that isn't 4-byte-aligned is not special-cased: the branch
-- step itself still schedules it as an ordinary `pendingBranch`, and the
-- misalignment only surfaces as an Address Error (AdEL) exception on the
-- *next* fetch attempt, once `pc` actually becomes that value.
#guard stepThroughDelaySlot 0x90400000#32 (.jalr 8#32 0#32) (setRegs crossRegionState [(8, 0x80020001#32)])
  = some 0x80020001#32
#guard (match stepState (buildProg 0x90400000#32 [.jalr 8#32 0#32, nopInstr])
          (setRegs crossRegionState [(8, 0x80020001#32)]) with
        | some s1 =>
          (match stepState (buildProg 0x90400000#32 [.jalr 8#32 0#32, nopInstr]) s1 with
           | some s2 => raisesAddr (hstep (buildProg 0x90400000#32 [.jalr 8#32 0#32, nopInstr]) s2) excCodeAdEL 0x80020001#32
           | none => false)
        | none => false)

-- ### control transfer in a delay slot: Reserved Instruction (pin)

-- A branch immediately following a *taken* branch (i.e. itself occupying
-- the delay slot) raises Reserved Instruction, taken in the delay slot
-- (`EPC` = the first branch, `Cause.BD = 1`): UNPREDICTABLE / UNDEFINED in
-- the architecture, pinned to RI (INSTRUCTION-REF Global rule 3).
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isRiInDelaySlot
            (hstep (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32]) s1)
        | none => false)
-- A branch following a *not-taken* branch is in a delay slot just the same
-- (the delay slot exists whether or not the branch is taken), so it raises
-- Reserved Instruction identically.
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 6#32)]) with
        | some s1 =>
          isRiInDelaySlot
            (hstep (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32]) s1)
        | none => false)
-- ... as does `eret` in a delay slot (taken or not).
#guard (match stepState (buildProg textBase [.j 0x100#32, .eret]) regs0 with
        | some s1 => isRiInDelaySlot (hstep (buildProg textBase [.j 0x100#32, .eret]) s1)
        | none => false)
-- `j` right after a taken `beq` does the same.
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .j 0x1000#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isRiInDelaySlot (hstep (buildProg textBase [.beq 8#32 9#32 1#32, .j 0x1000#32]) s1)
        | none => false)
-- `bltz` right after a taken `beq` does the same (confirms the REGIMM
-- branches are included in `isBranchLike`).
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .bltz 8#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isRiInDelaySlot
            (hstep (buildProg textBase [.beq 8#32 9#32 1#32, .bltz 8#32 0#32]) s1)
        | none => false)
-- `nal`, `bal` and `pause` right after a taken `beq` do the same (Release 6: they are CTIs in
-- `isBranchLike`; PAUSE p.317: "Implementations are required to signal a Reserved Instruction
-- exception if PAUSE is encountered in the delay slot").
#guard [Instruction.nal 0#32, .bal 0#32, .pause].all fun i =>
  match stepState (buildProg textBase [.beq 8#32 9#32 1#32, i]) (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
  | some s1 => isRiInDelaySlot (hstep (buildProg textBase [.beq 8#32 9#32 1#32, i]) s1)
  | none => false


-- ### `run`: a short program that computes something and exits

-- addiu $t0,$zero,5 ; addiu $t1,$zero,7 ; add $t2,$t0,$t1 ; add $a0,$t2,$zero ;
-- addiu $v0,$zero,1 ; syscall (print 12) ; addiu $v0,$zero,10 ; syscall (exit)

private def sumProg : Program :=
  buildProg textBase
    [ .addiu 0#32 8#32 5#32
    , .addiu 0#32 9#32 7#32
    , .add  8#32 9#32 10#32
    , .add  10#32 0#32 4#32
    , .addiu 0#32 2#32 1#32
    , (.syscall 0#32)
    , .addiu 0#32 2#32 10#32
    , (.syscall 0#32) ]

#guard (match trun sumProg regs0 20 with
        | .halted .exit h steps => h.out == "12" && steps == 8
        | _ => false)

-- `limitReached`: a two-instruction infinite self-loop
-- (`beq $zero,$zero,-1` with a `nop` delay slot) — with delay slots the
-- loop body is the branch *plus* its delay-slot instruction, so each
-- iteration costs 2 steps, but it still never halts.
private def loopProg : Program := buildProg textBase [.beq 0#32 0#32 0xffff#32, nopInstr]
#guard (match trun loopProg regs0 5 with
        | .limitReached _ steps => steps == 5
        | _ => false)

-- ### pause (MD00086 Vol II-A Rev 6.06, PAUSE p.317): with `LLbit` set, `EPC ← pc + 4` and the
-- processor enters standby at the next instruction; with `LLbit` clear it is a no-op.
#guard (match stepState (prog1 .pause) { regs0 with llBit := true } with
        | some s => s.standby && s.cp0Epc == textBase + 4#32 && s.pc == textBase + 4#32
        | none => false)
#guard (match stepState (prog1 .pause) regs0 with
        | some s => !s.standby && s.cp0Epc == regs0.cp0Epc && s.pc == textBase + 4#32
        | none => false)
