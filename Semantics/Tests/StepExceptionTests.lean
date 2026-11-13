import Semantics.Tests.StepFixtures

/-!
# `step` tests: syscalls, traps, CP0, exception entry, `eret`, Reserved Instruction

Moved verbatim out of `Semantics/Step.lean` (reviewability restructuring): the definition file now holds definitions only.
Every check that calls `step`/`run` is a `#guard` (see `StepFixtures.lean` for why).
-/

open StepTest

-- ### syscalls

#guard hstepOut (prog1 (.syscall 0#32)) (setRegs regs0 [(2, 1#32), (4, 5#32)])
  = some "5"
#guard hstepOut (prog1 (.syscall 0#32)) (setRegs regs0 [(2, 1#32), (4, 0xfffffffb#32)])
  = some "-5"
private def syscall4State : State :=
  { (setRegs regs0 [(2, 4#32), (4, 0x10010000#32)]) with
      mem := (((∅ : Std.HashMap W32 UInt8).insert 0x10010000#32 0x48).insert 0x10010001#32 0x69)
               |>.insert 0x10010002#32 0 }
#guard hstepOut (prog1 (.syscall 0#32)) syscall4State = some "Hi"
private def syscall4EmptyState : State :=
  { (setRegs regs0 [(2, 4#32), (4, 0x10010000#32)]) with
      mem := (∅ : Std.HashMap W32 UInt8).insert 0x10010000#32 0 }
#guard hstepOut (prog1 (.syscall 0#32)) syscall4EmptyState = some ""
#guard isHaltExit (hstep (prog1 (.syscall 0#32)) (setRegs regs0 [(2, 10#32)]))
#guard hstepOut (prog1 (.syscall 0#32)) (setRegs regs0 [(2, 11#32), (4, 0x41#32)])
  = some "A"
#guard raises (hstep (prog1 (.syscall 0#32)) (setRegs regs0 [(2, 999#32)])) excCodeSys
-- The bare processor (`step`, no hosted services): `syscall` is the System Call exception
-- whatever `$v0` selects.
#guard (let s := step (loadImage (prog1 (.syscall 0#32)) (setRegs regs0 [(2, 1#32), (4, 5#32)]))
        causeExcCode s == excCodeSys && s.cp0Epc == textBase && s.pc == exceptionVectorAddr)
#guard (match hostStep { image := prog1 (.syscall 0#32), services := false }
          { machine := loadImage (prog1 (.syscall 0#32)) (setRegs regs0 [(2, 10#32)]) } with
        | .next h => causeExcCode h.machine == excCodeSys && h.out == ""
        | .halt _ => false)

-- ### Traps / exceptions (coprocessor 0): teq/tne/tlt/tge/tltu/tgeu/break

private def cp0Eq (r : Outcome) (epc cause status pc : W32) : Bool :=
  match r with
  | .next s => s.cp0Epc == epc && s.cp0Cause == cause && s.cp0Status == status && s.pc == pc
  | .halt _ => false

private def cp0Untouched (r : Outcome) (before : State) : Bool :=
  match r with
  | .next s => s.cp0Epc == before.cp0Epc && s.cp0Cause == before.cp0Cause
                 && s.cp0Status == before.cp0Status
  | .halt _ => false

-- teq: trap-taken from `textBase` sets `EPC = textBase` (the trapping
-- instruction's own address, not `pc + 4`), `Cause.ExcCode = excCodeTr`
-- packed into bits 6..2 (`excCodeTr <<< 2`), `Status.EXL` (bit 1) set, and
-- `pc = exceptionVectorAddr`.
#guard cp0Eq (hstep (prog1 (.teq 8#32 9#32 0#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr
-- teq: trap-not-taken behaves like an ordinary instruction (falls through
-- to `pc + 4`) and leaves all CP0 state untouched.
#guard nextPcEq (hstep (prog1 (.teq 8#32 9#32 0#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  (textBase + 4#32)
#guard cp0Untouched (hstep (prog1 (.teq 8#32 9#32 0#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)])) regs0

-- tne: trap on not-equal (opposite condition from teq)
#guard cp0Eq (hstep (prog1 (.tne 8#32 9#32 0#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr
#guard isNext (hstep (prog1 (.tne 8#32 9#32 0#32)) (setRegs regs0 [(8, 5#32), (9, 5#32)]))

-- tlt/tge: signed comparison (negative `$rs` is less than positive `$rt`)
#guard cp0Eq (hstep (prog1 (.tlt 8#32 9#32 0#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr  -- -1 < 1
#guard isNext (hstep (prog1 (.tlt 8#32 9#32 0#32)) (setRegs regs0 [(8, 1#32), (9, 0xffffffff#32)]))  -- 1 < -1 false
#guard cp0Eq (hstep (prog1 (.tge 8#32 9#32 0#32)) (setRegs regs0 [(8, 1#32), (9, 0xffffffff#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr  -- 1 >= -1
#guard isNext (hstep (prog1 (.tge 8#32 9#32 0#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))  -- -1 >= 1 false

-- tltu/tgeu: unsigned comparison (0xffffffff is the largest unsigned value,
-- so it is never `<u` anything and always `>=u` everything)
#guard isNext (hstep (prog1 (.tltu 8#32 9#32 0#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
#guard cp0Eq (hstep (prog1 (.tgeu 8#32 9#32 0#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr

-- ### Trap-immediate family (REGIMM, real MIPS32 ISA;
-- docs/spec/MIPS-COVERAGE-GAPS.md §3.8): teqi/tnei/tgei/tgeiu/tlti/tltiu,
-- the sign-extended-16-bit-immediate counterpart of teq/tne/tlt/tge/tltu/tgeu.

-- teqi: trap-taken when `$rs == sext16(imm)`; trap-not-taken behaves like
-- an ordinary instruction and leaves all CP0 state untouched.
#guard cp0Eq (hstep (prog1 (.teqi 8#32 5#32)) (setRegs regs0 [(8, 5#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr
#guard isNext (hstep (prog1 (.teqi 8#32 5#32)) (setRegs regs0 [(8, 6#32)]))
#guard cp0Untouched (hstep (prog1 (.teqi 8#32 5#32)) (setRegs regs0 [(8, 6#32)])) regs0

-- tnei: trap on not-equal (opposite condition from teqi)
#guard cp0Eq (hstep (prog1 (.tnei 8#32 5#32)) (setRegs regs0 [(8, 6#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr
#guard isNext (hstep (prog1 (.tnei 8#32 5#32)) (setRegs regs0 [(8, 5#32)]))

-- tgei/tlti: signed comparison against `sext16(imm)`; imm = 0xffff sign-
-- extends to -1.
#guard cp0Eq (hstep (prog1 (.tgei 8#32 0xffff#32)) (setRegs regs0 [(8, 0xffffffff#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr  -- -1 >= -1
#guard isNext (hstep (prog1 (.tgei 8#32 0xffff#32)) (setRegs regs0 [(8, 0xfffffffe#32)]))  -- -2 >= -1 false
#guard cp0Eq (hstep (prog1 (.tlti 8#32 1#32)) (setRegs regs0 [(8, 0xffffffff#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr  -- -1 < 1
#guard isNext (hstep (prog1 (.tlti 8#32 1#32)) (setRegs regs0 [(8, 1#32)]))  -- 1 < 1 false

-- tgeiu/tltiu: the immediate is sign-extended to 32 bits first, *then* the
-- comparison is unsigned on the resulting bit pattern -- same convention
-- `sltiu` already uses. Edge case where the signed and unsigned
-- interpretations of the same `$rs` bit pattern disagree: $rs = 0xffffffff
-- (signed -1, unsigned max) against imm = 1 (sext16(1) = 1); unsigned
-- 0xffffffff >=u 1 is true (traps), even though a signed read of the same
-- bits (-1 >= 1) would be false.
#guard cp0Eq (hstep (prog1 (.tgeiu 8#32 1#32)) (setRegs regs0 [(8, 0xffffffff#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr
#guard isNext (hstep (prog1 (.tltiu 8#32 1#32)) (setRegs regs0 [(8, 0xffffffff#32)]))  -- 0xffffffff <u 1 false
#guard cp0Eq (hstep (prog1 (.tltiu 8#32 1#32)) (setRegs regs0 [(8, 0#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr  -- 0 <u 1 true

-- a negative-immediate edge case: imm = 0xffff (sext16 = -1, i.e. bit
-- pattern 0xffffffff) compared *unsigned* against $rs = 1 does NOT trap
-- (1 >=u 0xffffffff is false) under tgeiu, unlike the signed tgei case
-- with the exact same operands (1 >= -1 is true, traps) -- demonstrating
-- tgeiu really does compare unsigned, not just sign-extend-and-reuse-tgei.
#guard isNext (hstep (prog1 (.tgeiu 8#32 0xffff#32)) (setRegs regs0 [(8, 1#32)]))
#guard cp0Eq (hstep (prog1 (.tgei 8#32 0xffff#32)) (setRegs regs0 [(8, 1#32)]))
  textBase (excCodeTr <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr

-- break: unconditional trap, distinct `ExcCode` (`excCodeBp` ≠ `excCodeTr`)
-- from the same starting state/address as the teq case above.
#guard excCodeBp ≠ excCodeTr
#guard cp0Eq (hstep (prog1 (.break 0#32)) regs0)
  textBase (excCodeBp <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr

-- a second trap from a nonzero `pc` records that instruction's own address
-- in `EPC`, not `textBase`/`pc + 4`.
private def trapAtState : State := { regs0 with pc := textBase + 0x100#32 }
#guard cp0Eq (hstep (progAt (textBase + 0x100#32) (.break 0#32)) trapAtState)
  (textBase + 0x100#32) (excCodeBp <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr

-- no handler loaded at the vector: the hosted run's *next* step from the post-trap
-- state finds `pc` outside the loaded image while `EXL = 1`, and stops with
-- `unhandledException ExcCode EPC BadVAddr` (an environment convention, Env.lean).
#guard (match stepState (prog1 (.break 0#32)) regs0 with
        | some s' => isHaltUnhandled (hstep (prog1 (.break 0#32)) s') excCodeBp textBase 0#32
        | none => false)
-- an aligned `pc` outside the loaded image, with no exception pending, stops the
-- hosted run with `noInstruction` (the processor itself would fetch 0 = `nop`).
#guard (let s := step regs0; s.pc == textBase + 4#32 && s.regs == regs0.regs)
#guard isHaltNoInstr (hstep (∅ : Program) regs0) textBase

-- if a real handler word *is* present at the vector address, it executes
-- normally after the trap (e.g. an `addi` landing there).
private def vectorHandlerProg : Program :=
  (prog1 (.break 0#32)).insert exceptionVectorAddr (encode (.addi 0#32 8#32 42#32))
#guard (match stepState vectorHandlerProg regs0 with
        | some s' => nextRegEq (hstep vectorHandlerProg s') 8 42#32
        | none => false)

-- ### Coprocessor 0 (CP0): mfc0/mtc0/eret/wait (docs/spec/MIPS-COVERAGE-GAPS.md
-- §3.10A)

-- mfc0 reads back Status/Cause/EPC, selected by `rd` (12/13/14).
#guard nextRegEq (hstep (prog1 (.mfc0 8#32 12#32 0#32)) { regs0 with cp0Status := 0x2#32 }) 8 0x2#32
#guard nextRegEq (hstep (prog1 (.mfc0 8#32 13#32 0#32)) { regs0 with cp0Cause := 0x34#32 }) 8 0x34#32
#guard nextRegEq (hstep (prog1 (.mfc0 8#32 14#32 0#32)) { regs0 with cp0Epc := 0x3000#32 }) 8 0x3000#32

-- mtc0 writes Status/EPC from a GPR (Cause/BadVAddr/ErrorEPC: see below).
#guard (match stepState (prog1 (.mtc0 8#32 12#32 0#32)) (setRegs regs0 [(8, 0x2#32)]) with
        | some s' => s'.cp0Status == 0x2#32
        | none => false)
-- `mtc0` to Cause writes only DC (27), IV (23) and IP1..0 (9:8); ExcCode/BD
-- and every other bit keep their old value.
#guard (match stepState (prog1 (.mtc0 8#32 13#32 0#32)) (setRegs regs0 [(8, 0xffffffff#32)]) with
        | some s' => s'.cp0Cause == 0x08800300#32
        | none => false)
#guard (match stepState (prog1 (.mtc0 8#32 13#32 0#32))
          { (setRegs regs0 [(8, 0#32)]) with cp0Cause := 0x80c00334#32 } with
        | some s' => s'.cp0Cause == 0x80400034#32
        | none => false)
-- `mtc0` to Status keeps only IE, EXL, ERL, IM7..0, BEV, CU1.
#guard (match stepState (prog1 (.mtc0 8#32 12#32 0#32)) (setRegs regs0 [(8, 0xffffffff#32)]) with
        | some s' => s'.cp0Status == 0x2040ff07#32
        | none => false)
-- BadVAddr (8) is read-only: `mtc0` to it is ignored; `mfc0` reads it.
#guard (match stepState (prog1 (.mtc0 8#32 8#32 0#32)) { (setRegs regs0 [(8, 0x1234#32)]) with cp0BadVAddr := 0x77#32 } with
        | some s' => s'.cp0BadVAddr == 0x77#32 && s'.pc == textBase + 4#32
        | none => false)
#guard nextRegEq (hstep (prog1 (.mfc0 8#32 8#32 0#32)) { regs0 with cp0BadVAddr := 0x10010001#32 }) 8 0x10010001#32
-- ErrorEPC (30) is fully readable/writable.
#guard (match stepState (prog1 (.mtc0 8#32 30#32 0#32)) (setRegs regs0 [(8, 0x3000#32)]) with
        | some s' => s'.cp0ErrorEpc == 0x3000#32
        | none => false)
#guard nextRegEq (hstep (prog1 (.mfc0 8#32 30#32 0#32)) { regs0 with cp0ErrorEpc := 0x3004#32 }) 8 0x3004#32
#guard (match stepState (prog1 (.mtc0 8#32 14#32 0#32)) (setRegs regs0 [(8, 0x3000#32)]) with
        | some s' => s'.cp0Epc == 0x3000#32
        | none => false)

-- mtc0 then mfc0 reads back the written value through the register's write
-- mask (Status: 0xabcd &&& 0x2040ff07; Cause: 0xabcd &&& 0x00800300; EPC: all).
#guard (match stepState (prog1 (.mtc0 8#32 12#32 0#32)) (setRegs regs0 [(8, 0xabcd#32)]) with
        | some s' => nextRegEq (hstep (prog1 (.mfc0 9#32 12#32 0#32)) { s' with pc := textBase }) 9
            0xab05#32
        | none => false)
#guard (match stepState (prog1 (.mtc0 8#32 13#32 0#32)) (setRegs regs0 [(8, 0xabcd#32)]) with
        | some s' => nextRegEq (hstep (prog1 (.mfc0 9#32 13#32 0#32)) { s' with pc := textBase }) 9
            0x0300#32
        | none => false)
#guard (match stepState (prog1 (.mtc0 8#32 14#32 0#32)) (setRegs regs0 [(8, 0xabcd#32)]) with
        | some s' => nextRegEq (hstep (prog1 (.mfc0 9#32 14#32 0#32)) { s' with pc := textBase }) 9
            0xabcd#32
        | none => false)

-- mfc0/mtc0 naming a CP0 register the model does not have (anything but
-- 8/12/13/14/30, sel 0) do not decode, so they raise Reserved Instruction.
#guard raises (hstep (prog1 (.mfc0 8#32 0#32 0#32)) regs0) excCodeRI
#guard raises (hstep (prog1 (.mtc0 8#32 0#32 0#32)) (setRegs regs0 [(8, 1#32)])) excCodeRI

-- eret: restores `pc` from `cp0Epc` and clears `Status.EXL` (bit 1, the same
-- bit `takeException` sets) in a *single* `step` call -- no delay-slot
-- scheduling (`pendingBranch` stays `none`, confirming `eret` bypasses
-- `mkNext` entirely rather than landing one instruction later).
private def eretReadyState : State :=
  { regs0 with cp0Epc := 0x3000#32, cp0Status := statusExlMask, pendingBranch := none }
#guard nextPcEq (hstep (prog1 .eret) eretReadyState) 0x3000#32
#guard (match stepState (prog1 .eret) eretReadyState with
        | some s' => s'.cp0Status == 0#32 && s'.pendingBranch == none
        | none => false)

-- full round trip: `teq` traps from `textBase` to `exceptionVectorAddr`
-- (confirming `cp0Epc`/`pc` land at the expected places, same as the
-- existing teq tests above), then `eret` placed at the vector returns
-- `pc` exactly to the original trapping instruction's address and clears
-- `Status.EXL`.
private def teqEretProg : Program :=
  ((∅ : Program).insert textBase (encode (.teq 8#32 9#32 0#32))).insert exceptionVectorAddr (encode .eret)
#guard (match stepState teqEretProg (setRegs regs0 [(8, 5#32), (9, 5#32)]) with
        | some s1 =>
          s1.cp0Epc == textBase && s1.pc == exceptionVectorAddr && s1.cp0Status == (statusCu1Mask ||| statusExlMask) &&
            (match stepState teqEretProg s1 with
             | some s2 => s2.pc == textBase && s2.cp0Status == statusCu1Mask
             | none => false)
        | none => false)

-- ### Exception entry: the general exception sequence (MD00090)

-- Exception in a branch delay slot (taken branch): `EPC` = the *branch's*
-- address, `Cause.BD` = 1, the pending branch is abandoned, and the handler
-- then runs sequentially from the vector (it does not jump to the old
-- branch target).
private def bdProg : Program :=
  ((buildProg textBase [.beq 0#32 0#32 0x10#32, (.break 0#32)]).insert exceptionVectorAddr
      (encode (.addiu 0#32 8#32 1#32))).insert (exceptionVectorAddr + 4#32) (encode (.addiu 0#32 9#32 2#32))
#guard (match stepN bdProg 2 regs0 with
        | some s2 => s2.cp0Epc == textBase && s2.cp0Cause == (causeBdMask ||| (excCodeBp <<< 2))
            && s2.pc == exceptionVectorAddr && s2.pendingBranch == none && s2.cp0Status == (statusCu1Mask ||| statusExlMask)
        | none => false)
#guard (match stepN bdProg 4 regs0 with
        | some s4 => s4.pc == exceptionVectorAddr + 8#32 && readReg s4 8 == 1#32 && readReg s4 9 == 2#32
        | none => false)
-- Same after a *not-taken* branch: the instruction is still in a delay slot.
#guard (match stepN (buildProg textBase [.bne 0#32 0#32 0x10#32, (.break 0#32)]) 2 regs0 with
        | some s2 => s2.cp0Epc == textBase && s2.cp0Cause == (causeBdMask ||| (excCodeBp <<< 2))
            && s2.pendingBranch == none
        | none => false)
-- Not in a delay slot: `EPC = pc`, and `Cause.BD` is *cleared* if it was set.
#guard cp0Eq (hstep (prog1 (.break 0#32)) { regs0 with cp0Cause := causeBdMask })
  textBase (excCodeBp <<< 2) (statusCu1Mask ||| statusExlMask) exceptionVectorAddr
-- `Status.EXL = 1` already: `EPC` and `Cause.BD` are left unchanged; only
-- `ExcCode` is updated.
#guard cp0Eq (hstep (prog1 (.break 0#32))
    { regs0 with cp0Status := statusExlMask, cp0Epc := 0x1234#32, cp0Cause := causeBdMask ||| (excCodeTr <<< 2) })
  0x1234#32 (causeBdMask ||| (excCodeBp <<< 2)) statusExlMask exceptionVectorAddr
-- Only `ExcCode` (bits 6..2) is written: IV (bit 23) and IP1..0 (bits 9:8)
-- survive. `Cause = 0x00800300` becomes `0x00800324` on `break`.
#guard cp0Eq (hstep (prog1 (.break 0#32)) { regs0 with cp0Cause := 0x00800300#32 })
  textBase 0x00800324#32 (statusCu1Mask ||| statusExlMask) exceptionVectorAddr
-- `Status.BEV = 1` selects the bootstrap vector `0xBFC00380`.
#guard cp0Eq (hstep (prog1 (.break 0#32)) { regs0 with cp0Status := statusBevMask })
  textBase (excCodeBp <<< 2) (statusBevMask ||| statusExlMask) exceptionVectorBevAddr

-- ### Integer Overflow / Address Error / Reserved Instruction / Syscall are
-- exceptions, not halts

-- `add` overflow with a handler installed at the vector: the handler runs,
-- `Cause.ExcCode = 12`, `EPC` = the `add`, and `$rd` was not written.
private def ovHandlerProg : Program :=
  (prog1 (.add 8#32 9#32 10#32)).insert exceptionVectorAddr (encode (.mfc0 26#32 13#32 0#32))
private def ovState : State := setRegs regs0 [(8, 0x7fffffff#32), (9, 1#32), (10, 0x55#32)]
#guard (match stepN ovHandlerProg 2 ovState with
        | some s2 => readReg s2 26 == (excCodeOv <<< 2) && s2.cp0Epc == textBase
            && readReg s2 10 == 0x55#32 && s2.pc == exceptionVectorAddr + 4#32
        | none => false)
-- ... and with no handler: `unhandledException 12 EPC BadVAddr`.
#guard (match trun (prog1 (.add 8#32 9#32 10#32)) ovState 10 with
        | .halted (.unhandledException c epc _) h steps =>
            c == 12#32 && epc == textBase && steps == 2 && readReg h.machine 10 == 0x55#32
        | _ => false)
-- Address errors report the failing address in the stop reason when unhandled.
#guard (match trun (prog1 (.lw 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)]) 10 with
        | .halted (.unhandledException c epc bad) _ _ => c == 4#32 && epc == textBase && bad == 0x10010001#32
        | _ => false)
#guard (match trun (prog1 (.sw 8#32 9#32 2#32)) (setRegs regs0 [(8, 0x10010000#32)]) 10 with
        | .halted (.unhandledException c epc bad) _ _ => c == 5#32 && epc == textBase && bad == 0x10010002#32
        | _ => false)
-- A failed store leaves memory untouched; like every exception entry it
-- clears `llBit`.
#guard (match stepState (prog1 (.sw 8#32 9#32 2#32)) { (setRegs regs0 [(8, 0x10010000#32), (9, 0xff#32)]) with llBit := true } with
        | some s' => s'.llBit == false && readMemWord s' 0x10010000#32 == some 0#32
        | none => false)
-- Undecodable word, unhandled: ExcCode 10.
#guard (match trun ((∅ : Program).insert textBase ((0x11#32 <<< 26) ||| (0x1f#32 <<< 21))) regs0 10 with
        | .halted (.unhandledException c epc _) _ _ => c == 10#32 && epc == textBase
        | _ => false)
-- `syscall` selecting no hosted service: the processor's System Call exception, ExcCode 8.
#guard (match trun (prog1 (.syscall 0#32)) (setRegs regs0 [(2, 999#32)]) 10 with
        | .halted (.unhandledException c epc _) _ _ => c == 8#32 && epc == textBase
        | _ => false)
-- Misaligned fetch: AdEL with `EPC = BadVAddr = pc`.
#guard (match trun (∅ : Program) misalignedState 10 with
        | .halted (.unhandledException c epc bad) _ _ => c == 4#32 && epc == textBase + 1#32 && bad == textBase + 1#32
        | _ => false)

-- ### eret: ERL selects ErrorEPC; LLbit is always cleared

#guard (match stepState (prog1 .eret)
          { regs0 with cp0Epc := 0x3000#32, cp0ErrorEpc := 0x4000#32, cp0Status := statusErlMask ||| statusExlMask } with
        | some s' => s'.pc == 0x4000#32 && s'.cp0Status == statusExlMask
        | none => false)
#guard (match stepState (prog1 .eret) { eretReadyState with llBit := true } with
        | some s' => s'.llBit == false
        | none => false)
-- `ll` / (exception) / `eret` / `sc`: the `sc` fails -- `$rt = 0` and memory
-- is not written.
private def llEretScProg : Program :=
  (buildProg textBase [.ll 8#32 9#32 0#32, (.break 0#32), .sc 8#32 10#32 0#32]).insert exceptionVectorAddr (encode .eret)
#guard (match stepN llEretScProg 2 (setRegs regs0 [(8, llscAddr), (10, 0xdeadbeef#32)]) with
        | some s2 =>
          -- handler: skip the `break` (EPC += 4 by hand), then `eret`, then `sc`
          (match stepN llEretScProg 2 { s2 with cp0Epc := s2.cp0Epc + 4#32 } with
           | some s4 => readReg s4 10 == 0#32 && s4.llBit == false && readMemWord s4 llscAddr == some 0#32
           | none => false)
        | none => false)

-- Exception entry clears `llBit`: `ll` / `break` / (handler returns by a plain
-- `jr`, not `eret`) / `sc` still fails.
#guard (match stepState (prog1 (.break 0#32)) { regs0 with llBit := true } with
        | some s' => s'.llBit == false
        | none => false)
-- `wait` in a delay slot raises Reserved Instruction, like `eret` (pin).
#guard (match stepState (buildProg textBase [.j 0x100#32, (.wait 0#32)]) regs0 with
        | some s1 => isRiInDelaySlot (hstep (buildProg textBase [.j 0x100#32, (.wait 0#32)]) s1)
        | none => false)


-- ### Undecodable word → Reserved Instruction exception

-- opcode 0x11 (COP1) is implemented for the fmt/funct combinations decoded
-- in `Instruction.lean`; fmt=0x1f is not one of them, so this word is still
-- genuinely undecodable.
private def badWord : W32 := (0x11#32 <<< 26) ||| (0x1f#32 <<< 21)
private def badProg : Program := (∅ : Program).insert textBase badWord
#guard raises (hstep badProg regs0) excCodeRI


-- ### CP0 additions: PRId / Config / Config1 / EBase, di / ei, Cause.DC
#guard nextRegEq (hstep (prog1 (.mfc0 9#32 15#32 0#32)) regs0) 9 0x00010000#32
#guard nextRegEq (hstep (prog1 (.mfc0 9#32 16#32 0#32)) regs0) 9 0x80008402#32
#guard nextRegEq (hstep (prog1 (.mfc0 9#32 16#32 1#32)) regs0) 9 0x00000001#32
#guard nextRegEq (hstep (prog1 (.mfc0 9#32 15#32 1#32)) regs0) 9 0x80000000#32
-- the read-only registers ignore writes
#guard (match hstep (prog1 (.mtc0 9#32 16#32 0#32)) (setRegs regs0 [(9, 0xffffffff#32)]) with
        | .next s => nextRegEq (hstep (prog1 (.mfc0 10#32 16#32 0#32)) { s with pc := textBase }) 10
            0x80008402#32
        | .halt _ => false)
-- EBase: only bits 29..12 are writable; bits 31..30 stay `10`
#guard (match hstep (prog1 (.mtc0 9#32 15#32 1#32)) (setRegs regs0 [(9, 0xffffffff#32)]) with
        | .next s => s.cp0EBase == 0xbffff000#32 && exceptionVector s == 0xbffff180#32
        | .halt _ => false)
#guard (match hstep (prog1 (.mtc0 9#32 15#32 1#32)) (setRegs regs0 [(9, 0x00012345#32)]) with
        | .next s => s.cp0EBase == 0x80012000#32
        | .halt _ => false)
-- exceptions vector through EBase when BEV = 0, and through 0xBFC00380 when BEV = 1
#guard (match hstep (prog1 (.break 0#32)) { regs0 with cp0EBase := 0x80012000#32 } with
        | .next s => s.pc == 0x80012180#32
        | .halt _ => false)
#guard (match hstep (prog1 (.break 0#32))
          { regs0 with cp0EBase := 0x80012000#32, cp0Status := statusBevMask } with
        | .next s => s.pc == 0xbfc00380#32
        | .halt _ => false)
-- di / ei: $rt receives the old Status; IE is cleared / set
#guard (match hstep (prog1 (.di 9#32)) { regs0 with cp0Status := 0x2000ff01#32 } with
        | .next s => readReg s 9 == 0x2000ff01#32 && s.cp0Status == 0x2000ff00#32
        | .halt _ => false)
#guard (match hstep (prog1 (.ei 9#32)) regs0 with
        | .next s => readReg s 9 == 0x20000000#32 && s.cp0Status == 0x20000001#32
        | .halt _ => false)
#guard (match hstep (prog1 (.ei 0#32)) regs0 with
        | .next s => readReg s 0 == 0#32 && s.cp0Status == 0x20000001#32
        | .halt _ => false)
-- Cause.DC (bit 27) is writable, WP (22) is not
#guard (match hstep (prog1 (.mtc0 9#32 13#32 0#32)) (setRegs regs0 [(9, 0xffffffff#32)]) with
        | .next s => s.cp0Cause == 0x08800300#32
        | .halt _ => false)
