import Semantics.Tests.StepFixtures

/-!
# `step` tests: branches, branch-likely, jumps, delay slots, `run`

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
#guard (match step (prog1 (.beq 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)
        | .halt _ => false)
-- ... and the delay-slot instruction's own step is what actually lands on
-- the target.
#guard stepThroughDelaySlot textBase (.beq 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 5#32)])
  = some (textBase + 4#32 + 12#32)
#guard nextPcEq (step (prog1 (.beq 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  (textBase + 4#32)
-- not taken: still in a delay slot -- the pending target is the fall-through `pc + 8`
#guard nextPendingEq (step (prog1 (.beq 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  (some (textBase + 8#32))
#guard stepThroughDelaySlot textBase (.beq 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 6#32)])
  = some (textBase + 8#32)

#guard stepThroughDelaySlot textBase (.bne 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 6#32)])
  = some (textBase + 4#32 + 12#32)
#guard nextPcEq (step (prog1 (.bne 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]))
  (textBase + 4#32)

#guard stepThroughDelaySlot textBase (.blez 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])  -- -5 ≤ 0
  = some (textBase + 4#32 + 8#32)
#guard stepThroughDelaySlot textBase (.blez 8#32 2#32) (setRegs regs0 [(8, 0#32)])  -- 0 ≤ 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.blez 8#32 2#32)) (setRegs regs0 [(8, 5#32)]))  -- 5 ≤ 0 is false
  (textBase + 4#32)
#guard stepThroughDelaySlot textBase (.bgtz 8#32 2#32) (setRegs regs0 [(8, 5#32)])  -- 5 > 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bgtz 8#32 2#32)) (setRegs regs0 [(8, 0#32)]))  -- 0 > 0 is false
  (textBase + 4#32)

-- ### bltz/bgez/bltzal/bgezal (REGIMM, opcode 0x01): same `pendingBranch`
-- delay-slot scheduling as blez/bgtz, taken/not-taken for each; the `al`
-- variants additionally link `$ra` unconditionally.

-- bltz: taken on a negative $rs, not taken on zero/positive
#guard stepThroughDelaySlot textBase (.bltz 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])  -- -5 < 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bltz 8#32 2#32)) (setRegs regs0 [(8, 0#32)]))  -- 0 < 0 is false
  (textBase + 4#32)
#guard nextPcEq (step (prog1 (.bltz 8#32 2#32)) (setRegs regs0 [(8, 5#32)]))  -- 5 < 0 is false
  (textBase + 4#32)

-- bgez: taken on zero/positive $rs, not taken on negative
#guard stepThroughDelaySlot textBase (.bgez 8#32 2#32) (setRegs regs0 [(8, 0#32)])  -- 0 >= 0
  = some (textBase + 4#32 + 8#32)
#guard stepThroughDelaySlot textBase (.bgez 8#32 2#32) (setRegs regs0 [(8, 5#32)])  -- 5 >= 0
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bgez 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)]))  -- -5 >= 0 is false
  (textBase + 4#32)

-- bltzal: link into $ra is unconditional (pc + 8, past the delay slot),
-- whether or not the branch itself is taken.
#guard nextRegEq (step (prog1 (.bltzal 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)])) 31
  (textBase + 8#32)  -- taken: -5 < 0
#guard nextRegEq (step (prog1 (.bltzal 8#32 2#32)) (setRegs regs0 [(8, 5#32)])) 31
  (textBase + 8#32)  -- not taken: 5 < 0 is false, $ra still linked
#guard stepThroughDelaySlot textBase (.bltzal 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bltzal 8#32 2#32)) (setRegs regs0 [(8, 5#32)]))
  (textBase + 4#32)

-- bgezal: same unconditional-link convention as bltzal, >= 0 condition.
#guard nextRegEq (step (prog1 (.bgezal 8#32 2#32)) (setRegs regs0 [(8, 5#32)])) 31
  (textBase + 8#32)  -- taken: 5 >= 0
#guard nextRegEq (step (prog1 (.bgezal 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)])) 31
  (textBase + 8#32)  -- not taken: -5 >= 0 is false, $ra still linked
#guard stepThroughDelaySlot textBase (.bgezal 8#32 2#32) (setRegs regs0 [(8, 5#32)])
  = some (textBase + 4#32 + 8#32)
#guard nextPcEq (step (prog1 (.bgezal 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)]))
  (textBase + 4#32)

-- ### Branch-likely family (deprecated in MIPS32, removed in Release 6).
-- A **taken** instance behaves exactly like its non-likely counterpart
-- (`stepThroughDelaySlot`); a **not-taken** instance nullifies its own
-- delay-slot instruction: its single `step` moves `pc` straight to `pc + 8`
-- with no pending branch, so the delay-slot word is never fetched, decoded
-- or executed -- even if it is undecodable garbage.

-- `beql` taken: identical two-step shape to `beq` taken.
#guard stepThroughDelaySlot textBase (.beql 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 5#32)])
  = some (textBase + 4#32 + 12#32)
-- `beql` not taken: one bare `step` skips the delay slot.
#guard (match step (prog1 (.beql 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)

-- The nullified delay-slot word is never looked at: here it is undecodable
-- garbage (it would raise Reserved Instruction if executed) followed by an
-- `addiu`. Two bare `step`s execute the `beql` and then the `addiu` at
-- `pc + 8`; no exception is raised (`EXL` stays 0). `run` (which is just
-- `step` iterated) agrees.
private def squashGarbageWord : W32 := (0x11#32 <<< 26) ||| (0x1f#32 <<< 21)  -- undecodable: COP1 fmt 0x1f
private def beqlNotTakenGarbageProg : Program :=
  (((∅ : Program).insert textBase (encode (.beql 8#32 9#32 3#32))).insert (textBase + 4#32) squashGarbageWord).insert
    (textBase + 8#32) (encode (.addiu 0#32 10#32 7#32))
#guard decode squashGarbageWord = none
#guard (match stepState beqlNotTakenGarbageProg (setRegs regs0 [(8, 5#32), (9, 6#32)]) with
        | some s1 =>
          (match step beqlNotTakenGarbageProg s1 with
           | .next s2 => s2.pc == textBase + 12#32 && readReg s2 10 == 7#32 && s2.cp0Status == statusCu1Mask
           | .halt _ => false)
        | none => false)
#guard (match run beqlNotTakenGarbageProg (setRegs regs0 [(8, 5#32), (9, 6#32)]) 2 with
        | .limitReached s2 steps => steps == 2 && s2.pc == textBase + 12#32 && readReg s2 10 == 7#32
        | .halted _ _ _ => false)

-- `bnel`: opposite polarity to `beql`, same mechanism.
#guard stepThroughDelaySlot textBase (.bnel 8#32 9#32 3#32) (setRegs regs0 [(8, 5#32), (9, 6#32)])
  = some (textBase + 4#32 + 12#32)
#guard (match step (prog1 (.bnel 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)

-- `blezl`/`bgtzl`: same conditions as `blez`/`bgtz`, squash instead of
-- ordinary fallthrough when not taken.
#guard stepThroughDelaySlot textBase (.blezl 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])  -- -5 \u2264 0
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.blezl 8#32 2#32)) (setRegs regs0 [(8, 5#32)]) with  -- 5 \u2264 0 is false
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)
#guard stepThroughDelaySlot textBase (.bgtzl 8#32 2#32) (setRegs regs0 [(8, 5#32)])  -- 5 > 0
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bgtzl 8#32 2#32)) (setRegs regs0 [(8, 0#32)]) with  -- 0 > 0 is false
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)

-- `bltzl`/`bgezl` (REGIMM): same conditions as `bltz`/`bgez`.
#guard stepThroughDelaySlot textBase (.bltzl 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])  -- -5 < 0
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bltzl 8#32 2#32)) (setRegs regs0 [(8, 0#32)]) with  -- 0 < 0 is false
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)
#guard stepThroughDelaySlot textBase (.bgezl 8#32 2#32) (setRegs regs0 [(8, 0#32)])  -- 0 >= 0
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bgezl 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)]) with  -- -5>=0 false
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)

-- `bltzall`/`bgezall` (REGIMM): same unconditional-`$ra`-link convention as
-- `bltzal`/`bgezal` -- the link happens whether the branch is taken or
-- squashed.
#guard nextRegEq (step (prog1 (.bltzall 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)])) 31
  (textBase + 8#32)  -- taken: -5 < 0
#guard nextRegEq (step (prog1 (.bltzall 8#32 2#32)) (setRegs regs0 [(8, 5#32)])) 31
  (textBase + 8#32)  -- squashed: 5 < 0 is false, $ra still linked
#guard stepThroughDelaySlot textBase (.bltzall 8#32 2#32) (setRegs regs0 [(8, 0xfffffffb#32)])
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bltzall 8#32 2#32)) (setRegs regs0 [(8, 5#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)
#guard nextRegEq (step (prog1 (.bgezall 8#32 2#32)) (setRegs regs0 [(8, 5#32)])) 31
  (textBase + 8#32)  -- taken: 5 >= 0
#guard nextRegEq (step (prog1 (.bgezall 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)])) 31
  (textBase + 8#32)  -- squashed: -5 >= 0 is false, $ra still linked
#guard stepThroughDelaySlot textBase (.bgezall 8#32 2#32) (setRegs regs0 [(8, 5#32)])
  = some (textBase + 4#32 + 8#32)
#guard (match step (prog1 (.bgezall 8#32 2#32)) (setRegs regs0 [(8, 0xfffffffb#32)]) with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch == none
        | .halt _ => false)

-- ### j/jal: exact targets including top-4-bit preservation from `pc_next`;
-- jal $ra links to `pc + 8` (past the delay slot), not `pc + 4`

private def crossRegionState : State := { regs0 with pc := 0x90400000#32 }
-- `j`'s own step falls through to the delay slot, scheduling the target.
#guard (match step (progAt 0x90400000#32 (.j 0x1000#32)) crossRegionState with
        | .next s => s.pc == 0x90400004#32 && s.pendingBranch == some 0x90004000#32
        | .halt _ => false)
#guard stepThroughDelaySlot 0x90400000#32 (.j 0x1000#32) crossRegionState = some 0x90004000#32
-- `jal`: `$ra` is `pc + 8`, and the target lands the same way as `j` after
-- the delay slot.
#guard nextRegEq (step (progAt 0x90400000#32 (.jal 0x1000#32)) crossRegionState) 31 0x90400008#32
#guard stepThroughDelaySlot 0x90400000#32 (.jal 0x1000#32) crossRegionState = some 0x90004000#32

-- ### jr/jalr: register-indirect jump/call, same one-delay-slot scheduling
-- as j/jal, but the target comes from a register read. `jr $ra` is the
-- canonical function-return idiom; `jalr $rd, $rs` additionally links `$rd`
-- to `pc + 8`, exactly like `jal`'s link-value convention.

-- `jr`'s own step falls through to the delay slot, scheduling `$rs`'s raw
-- value as the target (no top-4-bit composition, unlike `j`).
#guard (match step (progAt 0x90400000#32 (.jr 8#32)) (setRegs crossRegionState [(8, 0x80020000#32)]) with
        | .next s => s.pc == 0x90400004#32 && s.pendingBranch == some 0x80020000#32
        | .halt _ => false)
#guard stepThroughDelaySlot 0x90400000#32 (.jr 8#32) (setRegs crossRegionState [(8, 0x80020000#32)])
  = some 0x80020000#32
-- the classic `jr $ra` function-return idiom: landing on whatever address
-- was previously linked into `$ra`.
#guard stepThroughDelaySlot textBase (.jr 31#32) (setRegs regs0 [(31, 0x00400040#32)])
  = some 0x00400040#32

-- `jalr $rd, $rs`: `$rd` is `pc + 8` (past the delay slot, same convention
-- as `jal`), and the target lands the same way as `jr` after the delay slot.
#guard nextRegEq (step (progAt 0x90400000#32 (.jalr 8#32 9#32)) (setRegs crossRegionState [(8, 0x80020000#32)]))
  9 0x90400008#32
#guard stepThroughDelaySlot 0x90400000#32 (.jalr 8#32 9#32) (setRegs crossRegionState [(8, 0x80020000#32)])
  = some 0x80020000#32
-- `jalr $t9, $t9` (rd = rs): the link value overwrites `$rs` only *after*
-- its pre-write value has been captured as the jump target.
#guard nextRegEq (step (progAt 0x90400000#32 (.jalr 9#32 9#32)) (setRegs crossRegionState [(9, 0x80020000#32)]))
  9 0x90400008#32
#guard stepThroughDelaySlot 0x90400000#32 (.jalr 9#32 9#32) (setRegs crossRegionState [(9, 0x80020000#32)])
  = some 0x80020000#32

-- a `jr` target that isn't 4-byte-aligned is not special-cased: the branch
-- step itself still schedules it as an ordinary `pendingBranch`, and the
-- misalignment only surfaces as an Address Error (AdEL) exception on the
-- *next* fetch attempt, once `pc` actually becomes that value.
#guard stepThroughDelaySlot 0x90400000#32 (.jr 8#32) (setRegs crossRegionState [(8, 0x80020001#32)])
  = some 0x80020001#32
#guard (match stepState (buildProg 0x90400000#32 [.jr 8#32, nopInstr])
          (setRegs crossRegionState [(8, 0x80020001#32)]) with
        | some s1 =>
          (match stepState (buildProg 0x90400000#32 [.jr 8#32, nopInstr]) s1 with
           | some s2 => raisesAddr (step (buildProg 0x90400000#32 [.jr 8#32, nopInstr]) s2) excCodeAdEL 0x80020001#32
           | none => false)
        | none => false)

-- ### branch/jump in a delay slot: diagnosable halt, not arbitrary behavior

-- A branch immediately following a *taken* branch (i.e. itself occupying
-- the delay slot) halts rather than silently scheduling/overwriting
-- anything — real MIPS32 leaves this architecturally discouraged/
-- implementation-defined (INSTRUCTION-REF Global rule 3).
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isHaltBranchInDelaySlot
            (step (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32]) s1)
        | none => false)
-- A branch following a *not-taken* branch is in a delay slot just the same
-- (the delay slot exists whether or not the branch is taken), so it halts
-- identically.
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 6#32)]) with
        | some s1 =>
          isHaltBranchInDelaySlot
            (step (buildProg textBase [.beq 8#32 9#32 1#32, .beq 0#32 0#32 0#32]) s1)
        | none => false)
-- ... as do `eret` and `bc1t`/`bc1f` in a delay slot (taken or not).
#guard (match stepState (buildProg textBase [.j 0x100#32, .eret]) regs0 with
        | some s1 => isHaltBranchInDelaySlot (step (buildProg textBase [.j 0x100#32, .eret]) s1)
        | none => false)
#guard (match stepState (buildProg textBase [.bne 0#32 0#32 1#32, .bc1t 0#32 1#32]) regs0 with
        | some s1 => isHaltBranchInDelaySlot (step (buildProg textBase [.bne 0#32 0#32 1#32, .bc1t 0#32 1#32]) s1)
        | none => false)
#guard (match stepState (buildProg textBase [.jr 31#32, .bc1f 0#32 1#32]) regs0 with
        | some s1 => isHaltBranchInDelaySlot (step (buildProg textBase [.jr 31#32, .bc1f 0#32 1#32]) s1)
        | none => false)
-- `j` right after a taken `beq` halts the same way.
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .j 0x1000#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isHaltBranchInDelaySlot (step (buildProg textBase [.beq 8#32 9#32 1#32, .j 0x1000#32]) s1)
        | none => false)
-- `bltz` right after a taken `beq` halts the same way (confirms the REGIMM
-- branches are included in `isBranchLike`).
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .bltz 8#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isHaltBranchInDelaySlot
            (step (buildProg textBase [.beq 8#32 9#32 1#32, .bltz 8#32 0#32]) s1)
        | none => false)
-- `beql` right after a taken `beq` halts the same way (confirms the
-- branch-likely family is included in `isBranchLike`, same `pendingBranch`
-- condition as every other branch/jump).
#guard (match stepState (buildProg textBase [.beq 8#32 9#32 1#32, .beql 8#32 8#32 0#32])
          (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          isHaltBranchInDelaySlot
            (step (buildProg textBase [.beq 8#32 9#32 1#32, .beql 8#32 8#32 0#32]) s1)
        | none => false)


-- ### `run`: a short program that computes something and exits

-- addi $t0,$zero,5 ; addi $t1,$zero,7 ; add $t2,$t0,$t1 ; add $a0,$t2,$zero ;
-- addi $v0,$zero,1 ; syscall (print 12) ; addi $v0,$zero,10 ; syscall (exit)
private def sumProg : Program :=
  buildProg textBase
    [ .addi 0#32 8#32 5#32
    , .addi 0#32 9#32 7#32
    , .add  8#32 9#32 10#32
    , .add  10#32 0#32 4#32
    , .addi 0#32 2#32 1#32
    , (.syscall 0#32)
    , .addi 0#32 2#32 10#32
    , (.syscall 0#32) ]

#guard (match run sumProg regs0 20 with
        | .halted .exit s steps => s.out == "12" && steps == 8
        | _ => false)

-- `limitReached`: a two-instruction infinite self-loop
-- (`beq $zero,$zero,-1` with a `nop` delay slot) — with delay slots the
-- loop body is the branch *plus* its delay-slot instruction, so each
-- iteration costs 2 steps, but it still never halts.
private def loopProg : Program := buildProg textBase [.beq 0#32 0#32 0xffff#32, nopInstr]
#guard (match run loopProg regs0 5 with
        | .limitReached _ steps => steps == 5
        | _ => false)
