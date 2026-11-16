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
      -- physical: data VA 0x1001_xxxx is PA 0x5001_xxxx (kuseg + 1 GB while ERL = 0)
      physMem := (((∅ : Std.HashMap W32 UInt8).insert 0x50010000#32 0x48).insert 0x50010001#32 0x69)
               |>.insert 0x50010002#32 0 }
#guard hstepOut (prog1 (.syscall 0#32)) syscall4State = some "Hi"
private def syscall4EmptyState : State :=
  { (setRegs regs0 [(2, 4#32), (4, 0x10010000#32)]) with
      -- physical: data VA 0x1001_xxxx is PA 0x5001_xxxx (kuseg + 1 GB while ERL = 0)
      physMem := (∅ : Std.HashMap W32 UInt8).insert 0x50010000#32 0 }
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

-- (Release 6 removed the trap-immediate family TEQI/TNEI/TGEI/TGEIU/TLTI/TLTIU; their tests are
-- gone.)

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
-- normally after the trap (e.g. an `addiu` landing there).
private def vectorHandlerProg : Program :=
  (prog1 (.break 0#32)).insert exceptionVectorAddr (encode (.addiu 0#32 8#32 42#32))
#guard (match stepState vectorHandlerProg regs0 with
        | some s' => nextRegEq (hstep vectorHandlerProg s') 8 42#32
        | none => false)

-- ### Coprocessor 0 (CP0): mfc0/mtc0/eret/wait (docs/spec/MIPS-COVERAGE-GAPS.md
-- §3.10A)

-- mfc0 reads back Status/Cause/EPC, selected by `rd` (12/13/14). Status reads with the read-only
-- `FR = 1` (bit 26: 64-bit FPU, Release 6; `statusValue`).
#guard nextRegEq (hstep (prog1 (.mfc0 8#32 12#32 0#32)) { regs0 with cp0Status := 0x2#32 }) 8 0x04000002#32
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
-- `mtc0` to Status keeps only IE, EXL, ERL, UM, IM7..0, BEV, CU0, CU1 (bit 3, R0, reads 0).
#guard (match stepState (prog1 (.mtc0 8#32 12#32 0#32)) (setRegs regs0 [(8, 0xffffffff#32)]) with
        | some s' => s'.cp0Status == 0x3040ff17#32
        | none => false)
-- BadVAddr (8) is read-only: `mtc0` to it is ignored; `mfc0` reads it.
#guard (match stepState (prog1 (.mtc0 8#32 8#32 0#32)) { (setRegs regs0 [(8, 0x1234#32)]) with cp0BadVAddr := 0x77#32 } with
        | some s' => s'.cp0BadVAddr == 0x77#32 && s'.pc == textBase + 4#32
        | none => false)
#guard nextRegEq (hstep (prog1 (.mfc0 8#32 8#32 0#32)) { regs0 with cp0BadVAddr := 0x10010001#32 }) 8 0x10010001#32
-- Timer (wave 5, F12): Count (9) and Compare (11) are R/W; Count advances once per step unless
-- Cause.DC = 1; a write to Compare clears Cause.TI; Count = Compare sets TI, read in Cause bit 30
-- and (IPTI = 7 pin) IP7 (bit 15).
#guard (match stepState (prog1 (.mtc0 8#32 9#32 0#32)) (setRegs regs0 [(8, 1000#32)]) with
        | some s' => s'.cp0Count == 1001#32
        | none => false)
#guard (match stepState (prog1 (.mtc0 8#32 9#32 0#32))
          { (setRegs regs0 [(8, 1000#32)]) with cp0Cause := causeDcMask } with
        | some s' => s'.cp0Count == 1000#32
        | none => false)
#guard nextRegEq (hstep (prog1 (.mfc0 8#32 9#32 0#32)) { regs0 with cp0Count := 0x1234#32 }) 8 0x1234#32
#guard (match stepState (prog1 (.mtc0 8#32 11#32 0#32))
          { (setRegs regs0 [(8, 5#32)]) with cp0TimerInt := true, cp0Count := 100#32 } with
        | some s' => s'.cp0Compare == 5#32 && !s'.cp0TimerInt
        | none => false)
#guard nextRegEq (hstep (prog1 (.mfc0 8#32 11#32 0#32)) { regs0 with cp0Compare := 77#32 }) 8 77#32
-- writing Compare = Count + 1 is matched by the same step's tick
#guard (match stepState (prog1 (.mtc0 8#32 11#32 0#32))
          { (setRegs regs0 [(8, 101#32)]) with cp0Count := 100#32 } with
        | some s' => s'.cp0TimerInt
        | none => false)
#guard (match stepState (prog1 nopInstr) { regs0 with cp0Count := 9#32, cp0Compare := 10#32 } with
        | some s' => s'.cp0TimerInt && s'.cp0Count == 10#32
        | none => false)
#guard nextRegEq (hstep (prog1 (.mfc0 8#32 13#32 0#32)) { regs0 with cp0TimerInt := true }) 8 0x40008000#32
-- mtc0 to Cause cannot write TI or IP7
#guard (match stepState (prog1 (.mtc0 8#32 13#32 0#32)) (setRegs regs0 [(8, 0x40008000#32)]) with
        | some s' => causeValue s' == 0#32
        | none => false)
-- HWREna (7): bits 0..3, 5 (XNP) and 29 (ULR) only (F15; Release 6)
#guard (match stepState (prog1 (.mtc0 8#32 7#32 0#32)) (setRegs regs0 [(8, 0xffffffff#32)]) with
        | some s' => s'.cp0HWREna == 0x2000002f#32
        | none => false)
#guard nextRegEq (hstep (prog1 (.mfc0 8#32 7#32 0#32)) { regs0 with cp0HWREna := 0xa#32 }) 8 0xa#32
-- rdhwr in Kernel Mode: CPUNum 0, SYNCI_Step 0, CC = Count, CCRes 1, XNP 1, ULR = UserLocal;
-- 4 (PerfCtr) and 6 (reserved) are RI
#guard nextRegEq (hstep (prog1 (.rdhwr 8#32 0#32 0#32)) (setRegs regs0 [(8, 7#32)])) 8 0#32
#guard nextRegEq (hstep (prog1 (.rdhwr 8#32 1#32 0#32)) (setRegs regs0 [(8, 7#32)])) 8 0#32
#guard nextRegEq (hstep (prog1 (.rdhwr 8#32 2#32 0#32)) { regs0 with cp0Count := 0xabc#32 }) 8 0xabc#32
#guard nextRegEq (hstep (prog1 (.rdhwr 8#32 3#32 0#32)) regs0) 8 1#32
#guard nextRegEq (hstep (prog1 (.rdhwr 8#32 5#32 0#32)) regs0) 8 1#32
#guard nextRegEq (hstep (prog1 (.rdhwr 8#32 29#32 0#32)) { regs0 with cp0UserLocal := 0x77#32 }) 8 0x77#32
#guard raises (hstep (prog1 (.rdhwr 8#32 4#32 0#32)) regs0) excCodeRI
#guard raises (hstep (prog1 (.rdhwr 8#32 6#32 0#32)) regs0) excCodeRI
-- rdhwr in User Mode: only the registers enabled in HWREna; otherwise RI (not CpU)
#guard raises (hstep (prog1 (.rdhwr 8#32 2#32 0#32)) { regs0 with cp0Status := statusUmMask }) excCodeRI
#guard nextRegEq (hstep (prog1 (.rdhwr 8#32 2#32 0#32))
  { regs0 with cp0Status := statusUmMask, cp0HWREna := 4#32, cp0Count := 55#32 }) 8 55#32
#guard raises (hstep (prog1 (.rdhwr 8#32 3#32 0#32))
  { regs0 with cp0Status := statusUmMask, cp0HWREna := 4#32 }) excCodeRI
-- User Mode with Status bit 28 set: Release 6 has no CU0 (bit 28 is the software bit RW), so
-- coprocessor 0 stays disabled and a register not enabled in HWREna is RI
#guard raises (hstep (prog1 (.rdhwr 8#32 3#32 0#32))
  { regs0 with cp0Status := statusUmMask ||| statusCu0Mask }) excCodeRI
-- rdhwr 29 (ULR) from User Mode with HWREna bit 29 set reads UserLocal
#guard nextRegEq (hstep (prog1 (.rdhwr 8#32 29#32 0#32))
  { regs0 with cp0Status := statusUmMask, cp0HWREna := 0x20000000#32, cp0UserLocal := 0x1234#32 })
  8 0x1234#32
-- ErrorEPC (30) is fully readable/writable.
#guard (match stepState (prog1 (.mtc0 8#32 30#32 0#32)) (setRegs regs0 [(8, 0x3000#32)]) with
        | some s' => s'.cp0ErrorEpc == 0x3000#32
        | none => false)
#guard nextRegEq (hstep (prog1 (.mfc0 8#32 30#32 0#32)) { regs0 with cp0ErrorEpc := 0x3004#32 }) 8 0x3004#32
#guard (match stepState (prog1 (.mtc0 8#32 14#32 0#32)) (setRegs regs0 [(8, 0x3000#32)]) with
        | some s' => s'.cp0Epc == 0x3000#32
        | none => false)

-- mtc0 then mfc0 reads back the written value through the register's write
-- mask (Status: 0xabcd &&& 0x3040ff17; Cause: 0xabcd &&& 0x00800300; EPC: all).
#guard (match stepState (prog1 (.mtc0 8#32 12#32 0#32)) (setRegs regs0 [(8, 0xabcd#32)]) with
        | some s' => nextRegEq (hstep (progAt kText (.mfc0 9#32 12#32 0#32)) { s' with pc := kText }) 9
            0x0400ab05#32  -- ERL is now 1; FR reads 1: the second instruction runs from kseg0 (kText)
        | none => false)
#guard (match stepState (prog1 (.mtc0 8#32 13#32 0#32)) (setRegs regs0 [(8, 0xabcd#32)]) with
        | some s' => nextRegEq (hstep (prog1 (.mfc0 9#32 13#32 0#32)) { s' with pc := textBase }) 9
            0x0300#32
        | none => false)
#guard (match stepState (prog1 (.mtc0 8#32 14#32 0#32)) (setRegs regs0 [(8, 0xabcd#32)]) with
        | some s' => nextRegEq (hstep (prog1 (.mfc0 9#32 14#32 0#32)) { s' with pc := textBase }) 9
            0xabcd#32
        | none => false)

-- mfc0/mtc0 naming a CP0 register the model does not have (here (0, 0), Index: no TLB) decode;
-- Release 6: the read returns 0 and the write is ignored (MFC0 p.266, MTC0 p.290).
#guard nextRegEq (hstep (prog1 (.mfc0 8#32 0#32 0#32)) (setRegs regs0 [(8, 0x55#32)])) 8 0#32
#guard (match hstep (prog1 (.mtc0 8#32 0#32 0#32)) (setRegs regs0 [(8, 1#32)]),
              hstep (prog1 (.sll 0#32 0#32 0#32)) (setRegs regs0 [(8, 1#32)]) with
        | .next a, .next b => a.cp0Status == b.cp0Status && a.cp0Cause == b.cp0Cause &&
            a.cp0Epc == b.cp0Epc && a.cp0HWREna == b.cp0HWREna && a.pc == b.pc && a.regs == b.regs &&
            a.llBit == b.llBit && a.cp0UserLocal == b.cp0UserLocal
        | _, _ => false)

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
-- A failed store leaves memory untouched; exception entry does not clear `llBit` (SC p.347:
-- the handler's ERET does).
#guard (match stepState (prog1 (.sw 8#32 9#32 2#32)) { (setRegs regs0 [(8, 0x10010000#32), (9, 0xff#32)]) with llBit := true } with
        | some s' => s'.llBit == true && readMemWord s' 0x10010000#32 == some 0#32
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

#guard (match stepState (progAt kText .eret)
          { regs0 with pc := kText, cp0Epc := 0x3000#32, cp0ErrorEpc := 0x4000#32,
                       cp0Status := statusErlMask ||| statusExlMask } with
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

-- Exception entry keeps `llBit` (MD00086 Vol II-A Rev 6.06, SC, p.347: ERET, not the exception,
-- makes SC fail): `ll` / `break` / (handler returns by `eretnc`) / `sc` succeeds.
#guard (match stepState (prog1 (.break 0#32)) { regs0 with llBit := true } with
        | some s' => s'.llBit == true
        | none => false)
private def llEretncScProg : Program :=
  (buildProg textBase [.ll 8#32 9#32 0#32, (.break 0#32), .sc 8#32 10#32 0#32]).insert exceptionVectorAddr (encode .eretnc)
#guard (match stepN llEretncScProg 2 (setRegs regs0 [(8, llscAddr), (10, 0xdeadbeef#32)]) with
        | some s2 =>
          (match stepN llEretncScProg 2 { s2 with cp0Epc := s2.cp0Epc + 4#32 } with
           | some s4 => readReg s4 10 == 1#32 && readMemWord s4 llscAddr == some 0xdeadbeef#32
           | none => false)
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
-- Config: M=1, K23=2, KU=2, BE=0 (little-endian), AR=2 (Release 6), MT=3 (Fixed Mapping), K0=2
#guard nextRegEq (hstep (prog1 (.mfc0 9#32 16#32 0#32)) regs0) 9 0xA4000982#32
-- Config1: M=1 (Config2 present), FP=1; Config2: M=1 (Config3 present), no L2/L3 cache;
-- Config3 = 0x8C003000 (M, BP, BI, ULRI, RXI); Config4 = 0x80FC0000 (M, KScrExist);
-- Config5 = 0x2010 (XNP, LLB; SBRI = 0) (MD00090 Vol III Rev 6.02 Tables 9.65-9.69, p.237-264)
#guard nextRegEq (hstep (prog1 (.mfc0 9#32 16#32 1#32)) regs0) 9 0x80000001#32
#guard nextRegEq (hstep (prog1 (.mfc0 9#32 16#32 2#32)) regs0) 9 0x80000000#32
#guard nextRegEq (hstep (prog1 (.mfc0 9#32 16#32 3#32)) regs0) 9 0x8C003000#32
#guard nextRegEq (hstep (prog1 (.mfc0 9#32 16#32 4#32)) regs0) 9 0x80FC0000#32
#guard nextRegEq (hstep (prog1 (.mfc0 9#32 16#32 5#32)) regs0) 9 0x00002010#32
-- Config5.SBRI (bit 6) is the one writable bit of Config5
#guard (match hstep (prog1 (.mtc0 9#32 16#32 5#32)) (setRegs regs0 [(9, 0xffffffff#32)]) with
        | .next s => s.cp0Config5SBRI &&
            nextRegEq (hstep (prog1 (.mfc0 10#32 16#32 5#32)) { s with pc := textBase }) 10 0x00002050#32
        | .halt _ => false)
-- Config1/2/3/4 are read-only: an all-ones write changes nothing (the state after it is the state
-- after a `nop`), and they read back their fixed values
#guard [1, 2, 3, 4].all fun (q : Nat) =>
  (match hstep (prog1 (.mtc0 9#32 16#32 (BitVec.ofNat 32 q))) (setRegs regs0 [(9, 0xffffffff#32)]),
         hstep (prog1 (.sll 0#32 0#32 0#32)) (setRegs regs0 [(9, 0xffffffff#32)]) with
   | .next s, .next t => s.cp0ConfigK0 == t.cp0ConfigK0 && s.cp0ConfigK23 == t.cp0ConfigK23 &&
       s.cp0ConfigKU == t.cp0ConfigKU && s.cp0Status == t.cp0Status && s.pc == t.pc &&
       nextRegEq (hstep (prog1 (.mfc0 10#32 16#32 (BitVec.ofNat 32 q))) { s with pc := textBase }) 10
         (if q == 1 then 0x80000001#32 else if q == 2 then 0x80000000#32
          else if q == 3 then 0x8C003000#32 else 0x80FC0000#32)
   | _, _ => false)
-- Every (rd, sel) decodes in Release 6 (Config6, (16,6), is not implemented and reads 0)
#guard decode (encode (.mfc0 9#32 16#32 6#32)) == some (.mfc0 9#32 16#32 6#32)
#guard nextRegEq (hstep (prog1 (.mfc0 9#32 16#32 6#32)) (setRegs regs0 [(9, 0x55#32)])) 9 0#32
#guard nextRegEq (hstep (prog1 (.mfc0 9#32 15#32 1#32)) regs0) 9 0x80000000#32
-- `Config` (16,0): only `K23` (30..28), `KU` (27..25) and `K0` (2..0) are writable (MD00090 Vol III
-- Rev 6.02 Table 9.64, p.233-235; Table A.2, p.317), and only with a supported value, 2 or 3 ("For
-- Release 6, writes of unsupported values are ignored"): all ones (7) changes nothing
#guard (match hstep (prog1 (.mtc0 9#32 16#32 0#32)) (setRegs regs0 [(9, 0xffffffff#32)]) with
        | .next s => nextRegEq (hstep (prog1 (.mfc0 10#32 16#32 0#32)) { s with pc := textBase }) 10
            0xA4000982#32
        | .halt _ => false)
-- K23 = KU = K0 = 3 is accepted; the bits outside K23/KU/K0 are ignored
#guard (match hstep (prog1 (.mtc0 9#32 16#32 0#32)) (setRegs regs0 [(9, 0xB6FFFFFB#32)]) with
        | .next s => nextRegEq (hstep (prog1 (.mfc0 10#32 16#32 0#32)) { s with pc := textBase }) 10
            0xB6000983#32
        | .halt _ => false)
-- each 3-bit K0 value: 2 and 3 read back, the others leave K0 = 2; nothing else changes
#guard (List.range 8).all fun k =>
  (match hstep (prog1 (.mtc0 9#32 16#32 0#32)) (setRegs regs0 [(9, 0xfffffff8#32 ||| BitVec.ofNat 32 k)]) with
    | .next s => nextRegEq (hstep (prog1 (.mfc0 10#32 16#32 0#32)) { s with pc := textBase }) 10
        (0xA4000980#32 ||| (if k == 2 || k == 3 then BitVec.ofNat 32 k else 2#32))
    | .halt _ => false)
#guard (match hstep (prog1 (.mtc0 9#32 16#32 0#32)) (setRegs regs0 [(9, 0#32)]) with
        | .next s => s.cp0ConfigK0 == 2#3 && s.cp0ConfigK23 == 2#3 && s.cp0ConfigKU == 2#3 &&
            s.cp0Status == regs0.cp0Status && s.cp0EBase == regs0.cp0EBase
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
-- di / ei: $rt receives the old Status (as read: FR = 1); IE is cleared / set
#guard (match hstep (prog1 (.di 9#32)) { regs0 with cp0Status := 0x2000ff01#32 } with
        | .next s => readReg s 9 == 0x2400ff01#32 && s.cp0Status == 0x2000ff00#32
        | .halt _ => false)
#guard (match hstep (prog1 (.ei 9#32)) regs0 with
        | .next s => readReg s 9 == 0x24000000#32 && s.cp0Status == 0x20000001#32
        | .halt _ => false)
#guard (match hstep (prog1 (.ei 0#32)) regs0 with
        | .next s => readReg s 0 == 0#32 && s.cp0Status == 0x20000001#32
        | .halt _ => false)
-- Cause.DC (bit 27) is writable, WP (22) is not
#guard (match hstep (prog1 (.mtc0 9#32 13#32 0#32)) (setRegs regs0 [(9, 0xffffffff#32)]) with
        | .next s => s.cp0Cause == 0x08800300#32
        | .halt _ => false)

-- ### Operating modes: User Mode and Coprocessor Unusable for coprocessor 0
-- (MD00090 Vol III Rev 6.02 §3.2-3.5.3, p.21-23; §6.2.22, p.100)

/-- User Mode: `UM = 1`, `EXL = ERL = 0`, `RW` (bit 28) = 0 (CU1 kept so FP is usable). -/
private def userSt : State := { regs0 with cp0Status := 0x20000010#32 }

/-- One step of `instr` at `textBase` from `s`. -/
private def step1 (instr : Instruction) (s : State) : State := step (loadImage (prog1 instr) s)

/-- `s` took Coprocessor Unusable for coprocessor 0 at `textBase` (CE = 0, EPC, BD = 0, EXL set,
UM kept, vector 0x8000_0180) and changed no GPR. -/
private def cp0Unusable (s : State) : Bool :=
  causeExcCode s == excCodeCpU && s.cp0Cause &&& causeCeMask == 0#32 &&
    s.cp0Cause &&& causeBdMask == 0#32 && s.cp0Epc == textBase &&
    s.cp0Status == 0x20000012#32 && s.pc == exceptionVectorAddr && s.regs == userSt.regs

#guard userMode userSt && !kernelMode userSt && !cp0Usable userSt
-- Each coprocessor-0 instruction in User Mode raises CpU (CE = 0).
#guard cp0Unusable (step1 (.mfc0 8#32 12#32 0#32) userSt)
#guard cp0Unusable (step1 (.mtc0 0#32 12#32 0#32) userSt)
#guard cp0Unusable (step1 (.di 8#32) userSt)
#guard cp0Unusable (step1 (.ei 8#32) userSt)
#guard cp0Unusable (step1 .eret userSt)
#guard cp0Unusable (step1 (.wait 0#32) userSt)
#guard cp0Unusable (step1 (.rdpgpr 8#32 9#32) userSt)
#guard cp0Unusable (step1 (.wrpgpr 8#32 9#32) userSt)
-- BEGIN R6-2
#guard cp0Unusable (step1 .eretnc userSt)
#guard cp0Unusable (step1 (.cache 0#32 0x14#32 0#32) userSt)
#guard cp0Unusable (step1 (.mfc0 8#32 0#32 0#32) userSt)   -- an unimplemented register too
-- END R6-2
-- Undecodable COP0 words (rs = 3 reserved; TLBP; rs = 0x0d reserved) and CACHE: CpU in User Mode, RI in
-- Kernel Mode. (RDPGPR, 0x41400000, decodes since wave 6: `rdpgpr $0, $0`.)
#guard (let w := 0x40600000#32
        decode w == none && isCop0Word w &&
        cp0Unusable (step (loadImage ((∅ : Program).insert textBase w) userSt)) &&
        causeExcCode (step (loadImage ((∅ : Program).insert textBase w) regs0)) == excCodeRI)
-- (CACHE, the Release 6 encoding SPECIAL3 funct 0x25, decodes; a CACHE word with bit 6 set,
-- `0x7c000065`, matches no diagram.)
#guard decode 0x7c000025#32 == some (.cache 0#32 0#32 0#32)
#guard [0x42000008#32, 0x41a00000#32, 0x7c000065#32].all fun w =>
        decode w == none && isCop0Word w &&
        cp0Unusable (step (loadImage ((∅ : Program).insert textBase w) userSt)) &&
        causeExcCode (step (loadImage ((∅ : Program).insert textBase w) regs0)) == excCodeRI
-- The pre-Release 6 CACHE opcode (0x2f) is not a COP0 word any more: Reserved Instruction in User
-- Mode too.
#guard (let w := 0xbc000000#32
        decode w == none && !isCop0Word w &&
        causeExcCode (step (loadImage ((∅ : Program).insert textBase w) userSt)) == excCodeRI)
-- Non-CP0 instructions run normally in User Mode (and FP with CU1 = 1).
#guard (let s := step1 (.addiu 0#32 8#32 5#32) userSt
        readReg s 8 == 5#32 && s.pc == textBase + 4#32 && userMode s)
-- User Mode with Status bit 28 set (Release 6 `RW`, no `CU0`): coprocessor 0 is not usable.
#guard (let s := step1 (.mfc0 8#32 12#32 0#32) { userSt with cp0Status := 0x30000010#32 }
        causeExcCode s == excCodeCpU && s.cp0Cause &&& causeCeMask == 0#32 && readReg s 8 == 0#32)
-- UM = 1 with EXL = 1 or ERL = 1 is Kernel Mode: CP0 usable.
#guard (let s := step1 (.mfc0 8#32 12#32 0#32) { userSt with cp0Status := 0x20000012#32 }
        readReg s 8 == 0x24000012#32 && s.pc == textBase + 4#32)
-- (with ERL = 1 the instruction runs from kseg0: executing from kuseg with ERL = 1 is UNDEFINED,
-- MD00090 Vol III Rev 6.02 §A.1.2, p.316)
#guard (let s := step (loadImage (progAt kText (.mfc0 8#32 12#32 0#32))
          { userSt with cp0Status := 0x20000014#32, pc := kText })
        readReg s 8 == 0x24000014#32 && s.pc == kText + 4#32)
-- `eret` in a delay slot is Reserved Instruction in User Mode too (pin; delay-slot check first).
#guard causeExcCode (step1 .eret { userSt with pendingBranch := some 0x400100#32 }) == excCodeRI
-- Any exception from User Mode enters Kernel Mode, UM still 1.
#guard (let s := step1 (.break 0#32) userSt
        causeExcCode s == excCodeBp && kernelMode s && s.cp0Status &&& statusUmMask != 0#32)
-- `eret` from a handler (EXL = 1, UM = 1) returns to User Mode at EPC.
#guard (let s := step1 .eret { userSt with cp0Status := 0x20000012#32, cp0Epc := 0x400100#32 }
        s.pc == 0x400100#32 && userMode s && s.cp0Status == 0x20000010#32)
-- `mtc0` writes UM and RW (bit 28) (Status write mask 0x3040ff17); bit 3 (R0) reads 0; RW does not
-- make coprocessor 0 usable in User Mode.
#guard (let s := step1 (.mtc0 8#32 12#32 0#32) (setRegs regs0 [(8, 0x10000018#32)])
        s.cp0Status == 0x10000010#32 && userMode s && !cp0Usable s)

-- ### Reset (MD00090 Vol III Rev 6.02 §6.2.5, p.89-90)

#guard resetState.pc == 0xbfc00000#32 && resetState.cp0Status == 0x00400004#32 &&
  kernelMode resetState && exceptionVector resetState == 0xbfc00380#32 &&
  ebaseValue resetState == 0x80000000#32 && configValue resetState == 0xA4000982#32 &&
  resetState.cp0ErrorEpc == 0#32 && resetState.cp0Cause == 0#32
-- An exception taken right after reset (BEV = 1) goes to the bootstrap vector 0xBFC0_0380;
-- with ERL = 1 it is still Kernel Mode and CP0 is usable.
#guard (let s := step (loadImage ((∅ : Program).insert 0xbfc00000#32 0x40600000#32) resetState)
        causeExcCode s == excCodeRI && s.pc == 0xbfc00380#32 && s.cp0Epc == 0xbfc00000#32)
-- Reset clears Cause.DC and keeps the other Cause bits; Status keeps UM/RW but sets BEV/ERL.
#guard (let r := resetException { regs0 with cp0Cause := 0x08000300#32, cp0Status := 0x10000010#32 }
        r.cp0Cause == 0x00000300#32 && r.cp0Status == 0x10400014#32 && kernelMode r &&
          r.cp0ErrorEpc == textBase)
-- The hosted start is the reset state followed by the boot convention.
#guard hostedStart.pc == textBase && hostedStart.cp0Status == statusCu1Mask &&
  readReg hostedStart 29 == spInit && kernelMode hostedStart

-- ### Interrupts (MD00090 Vol III Rev 6.02 §6.1, p.72-73; §6.2.26, p.102), standby, IntCtl, SRSCtl

-- Kernel Mode with `IE = 1`, `IM0 = 1` (Status 0x2000_0101) and the software request `IP0` set:
-- the next step takes the Interrupt exception instead of executing the `addiu` at `pc`.
private def swIntSt : State := { regs0 with cp0Status := 0x20000101#32, cp0Cause := 0x00000100#32 }
#guard interruptTaken swIntSt
#guard (let s := step1 (.addiu 0#32 8#32 5#32) swIntSt
        s.pc == 0x80000180#32 && s.cp0Epc == textBase && causeExcCode s == excCodeInt &&
          readReg s 8 == 0#32 && s.cp0Status == 0x20000103#32 && s.cp0Cause &&& causeBdMask == 0#32)
-- `Cause.IV = 1`: the special interrupt vector, offset 0x200 (Table 6.10, p.86).
#guard (step1 (.addiu 0#32 8#32 5#32) { swIntSt with cp0Cause := 0x00800100#32 }).pc == 0x80000200#32
-- BEV = 1: 0xBFC0_0380 (IV = 0) and 0xBFC0_0400 (IV = 1).
#guard interruptVector { swIntSt with cp0Status := 0x20400101#32 } == 0xBFC00380#32
#guard interruptVector { swIntSt with cp0Status := 0x20400101#32, cp0Cause := 0x00800100#32 } ==
  0xBFC00400#32
-- Not taken: `IE = 0`, `IM0 = 0`, `EXL = 1`, `ERL = 1`; the instruction executes.
#guard !interruptTaken { swIntSt with cp0Status := 0x20000105#32 }   -- ERL = 1
#guard [0x20000100#32, 0x20000001#32, 0x20000103#32].all fun st =>
  (let s := step1 (.addiu 0#32 8#32 5#32) { swIntSt with cp0Status := st }
   !interruptTaken { swIntSt with cp0Status := st } && readReg s 8 == 5#32)
-- In a delay slot: EPC = the branch (pc - 4), BD = 1, the pending branch is abandoned.
#guard (let s := step1 nopInstr { swIntSt with pendingBranch := some 0x00400100#32 }
        s.cp0Epc == textBase - 4#32 && s.cp0Cause &&& causeBdMask != 0#32 && s.pendingBranch == none &&
          s.pc == 0x80000180#32)
-- `mtc0 $t0, $13` with `$t0 = 0x200` (IP1) and IM1 = IE = 1: the request appears after the step and
-- the following step takes it with EPC = the instruction after the `mtc0`.
#guard (let p := buildProg textBase [.mtc0 8#32 13#32 0#32, nopInstr]
        let s0 := setRegs { regs0 with cp0Status := 0x20000201#32 } [(8, 0x200#32)]
        let s1 := step (loadImage p s0)
        let s2 := step s1
        s1.pc == textBase + 4#32 && interruptTaken s1 && s2.pc == 0x80000180#32 &&
          s2.cp0Epc == textBase + 4#32 && causeExcCode s2 == excCodeInt)
-- `ei` makes a pending request visible at once (hazard cleared immediately, pin).
#guard (let p := buildProg textBase [.ei 0#32, nopInstr]
        let s1 := step (loadImage p { regs0 with cp0Status := 0x20000100#32, cp0Cause := 0x100#32 })
        interruptTaken s1 && (step s1).cp0Epc == textBase + 4#32)
-- The timer: Count reaches Compare during a step, TI/IP7 is set, and with IM7 = IE = 1 the next
-- step takes the interrupt.
#guard (let s0 := { regs0 with cp0Status := 0x20008001#32, cp0Count := 9#32, cp0Compare := 10#32 }
        let s1 := step1 nopInstr s0
        s1.cp0TimerInt && interruptTaken s1 && (step s1).pc == 0x80000180#32 &&
          causeValue s1 &&& 0x40008000#32 == 0x40008000#32)
-- A hardware line (never asserted by the environment) is seen in IP2..IP7.
#guard causeValue { regs0 with hwInt := 0b000001#6 } == 0x400#32 &&
  interruptTaken { regs0 with hwInt := 0b000001#6, cp0Status := 0x20000401#32 }
-- `wait` enters standby; standby steps only advance Count; the timer request restarts it through
-- the interrupt with EPC = the instruction after the `wait` (WAIT, p.442).
#guard (let p := buildProg textBase [.wait 0#32, nopInstr]
        let s0 := { regs0 with cp0Status := 0x20008001#32, cp0Count := 0#32, cp0Compare := 5#32 }
        let s1 := step (loadImage p s0)
        let s3 := step (step s1)
        s1.standby && s1.pc == textBase + 4#32 && s3.standby && s3.pc == textBase + 4#32 &&
          s3.cp0Count == 3#32 &&
          (let s6 := run s3 3
           !s6.standby && s6.pc == 0x80000180#32 && s6.cp0Epc == textBase + 4#32))
-- With IE = 0 an unmasked request restarts the pipeline (pin), and execution continues after `wait`.
#guard (let s0 := { regs0 with standby := true, pc := textBase + 4#32, cp0Status := 0x20000100#32,
                                cp0Cause := 0x100#32 }
        let s1 := step s0
        !s1.standby && s1.pc == textBase + 4#32)
-- Reset leaves standby.
#guard !(resetException { regs0 with standby := true }).standby
-- IntCtl reads 0xE000_0000 (IPTI = 7), SRSCtl reads 0; writes are ignored.
#guard readReg (step1 (.mfc0 8#32 12#32 1#32) regs0) 8 == 0xE0000000#32
#guard readReg (step1 (.mfc0 8#32 12#32 2#32) regs0) 8 == 0#32
#guard (let s := step1 (.mtc0 8#32 12#32 2#32) (setRegs regs0 [(8, 0xffffffff#32)])
        readReg (step1 (.mfc0 9#32 12#32 2#32) { s with pc := textBase }) 9 == 0#32)
-- `rdpgpr`/`wrpgpr` move between the (only) shadow set 0 and the current GPRs.
#guard readReg (step1 (.rdpgpr 8#32 9#32) (setRegs regs0 [(9, 0x1234#32)])) 8 == 0x1234#32
#guard readReg (step1 (.wrpgpr 8#32 9#32) (setRegs regs0 [(9, 0x5678#32)])) 8 == 0x5678#32
#guard readReg (step1 (.wrpgpr 0#32 9#32) (setRegs regs0 [(9, 0x5678#32)])) 0 == 0#32

-- BEGIN R6-2
-- ### Release 6 CP0 registers and instructions (Wave R6-2)

-- UserLocal (4,2) and KScratch1..6 (31,2..7): what mtc0 writes, mfc0 reads back
-- (MD00090 Vol III Rev 6.02 Table 9.19, p.143; Table 9.84, p.311).
#guard (match hstep (prog1 (.mtc0 9#32 4#32 2#32)) (setRegs regs0 [(9, 0xfeed#32)]) with
        | .next s => s.cp0UserLocal == 0xfeed#32 &&
            nextRegEq (hstep (prog1 (.mfc0 10#32 4#32 2#32)) { s with pc := textBase }) 10 0xfeed#32
        | .halt _ => false)
#guard [2, 3, 4, 5, 6, 7].all fun (q : Nat) =>
  (match hstep (prog1 (.mtc0 9#32 31#32 (BitVec.ofNat 32 q))) (setRegs regs0 [(9, BitVec.ofNat 32 (100 + q))]) with
   | .next s => nextRegEq (hstep (prog1 (.mfc0 10#32 31#32 (BitVec.ofNat 32 q))) { s with pc := textBase }) 10
       (BitVec.ofNat 32 (100 + q)) &&
       -- the other KScratch registers are untouched
       [2, 3, 4, 5, 6, 7].all fun (r : Nat) => r == q ||
         nextRegEq (hstep (prog1 (.mfc0 10#32 31#32 (BitVec.ofNat 32 r))) { s with pc := textBase }) 10 0#32
   | .halt _ => false)
-- KScratch at (31,0) and (31,1) is not implemented (Config4.KScrExist = 0xFC): reads 0, write ignored.
#guard (match hstep (prog1 (.mtc0 9#32 31#32 1#32)) (setRegs regs0 [(9, 0xfeed#32)]) with
        | .next s => (List.finRange 6).all (fun k => s.cp0KScratch k == 0#32) &&
            nextRegEq (hstep (prog1 (.mfc0 10#32 31#32 1#32)) { s with pc := textBase }) 10 0#32
        | .halt _ => false)
-- LLAddr (17,0): reads LLbit in bit 0; writing 0 clears LLbit, writing 1 never sets it
-- (Table 9.72, p.270).
#guard nextRegEq (hstep (prog1 (.mfc0 9#32 17#32 0#32)) { regs0 with llBit := true }) 9 1#32
#guard nextRegEq (hstep (prog1 (.mfc0 9#32 17#32 0#32)) regs0) 9 0#32
#guard (match stepState (prog1 (.mtc0 9#32 17#32 0#32)) { (setRegs regs0 [(9, 0#32)]) with llBit := true } with
        | some s => s.llBit == false
        | none => false)
#guard (match stepState (prog1 (.mtc0 9#32 17#32 0#32)) (setRegs regs0 [(9, 1#32)]) with
        | some s => s.llBit == false
        | none => false)
#guard (match stepState (prog1 (.mtc0 9#32 17#32 0#32)) { (setRegs regs0 [(9, 1#32)]) with llBit := true } with
        | some s => s.llBit == true
        | none => false)
-- BadInstr after a Reserved Instruction: the faulting word; BadInstrP = 0 outside a delay slot
-- (§9.25, p.179; §9.26, p.181).
#guard (let s := step1 (.sigrie 0x1234#32) regs0
        causeExcCode s == excCodeRI && s.cp0BadInstr == encode (.sigrie 0x1234#32) &&
          s.cp0BadInstrP == 0#32 &&
          nextRegEq (hstep (prog1 (.mfc0 9#32 8#32 1#32)) { s with pc := textBase }) 9
            (encode (.sigrie 0x1234#32)))
-- An undecodable word is captured too.
#guard (let s := step (loadImage badProg regs0)
        causeExcCode s == excCodeRI && s.cp0BadInstr == badWord)
-- BadInstrP in a delay slot: the branch before the faulting instruction.
#guard (let p := buildProg textBase [.beq 0#32 0#32 0x10#32, .break 0#32]
        let s1 := step (loadImage p regs0)
        let s2 := step s1
        causeExcCode s2 == excCodeBp && s2.cp0Cause &&& causeBdMask != 0#32 &&
          s2.cp0BadInstr == encode (.break 0#32) &&
          s2.cp0BadInstrP == encode (.beq 0#32 0#32 0x10#32))
-- BadInstr / BadInstrP are read-only: mtc0 changes nothing.
#guard (match stepState (prog1 (.mtc0 9#32 8#32 1#32)) (setRegs { regs0 with cp0BadInstr := 7#32 } [(9, 1#32)]) with
        | some s => s.cp0BadInstr == 7#32
        | none => false)
-- An interrupt does not set BadInstr / BadInstrP.
#guard (let s := step1 (.addiu 0#32 8#32 5#32)
          { swIntSt with cp0BadInstr := 0x11#32, cp0BadInstrP := 0x22#32 }
        causeExcCode s == excCodeInt && s.cp0BadInstr == 0x11#32 && s.cp0BadInstrP == 0x22#32)
-- sigrie raises Reserved Instruction in User Mode too (not a coprocessor instruction).
#guard causeExcCode (step1 (.sigrie 0#32) userSt) == excCodeRI
-- eretnc returns like eret but keeps LLbit (ERETNC p.179).
#guard (match stepState (prog1 .eretnc) { eretReadyState with llBit := true } with
        | some s' => s'.llBit == true && s'.pc == 0x3000#32 && s'.cp0Status == 0#32
        | none => false)
#guard (match stepState (progAt kText .eretnc)
          { regs0 with pc := kText, cp0Epc := 0x3000#32, cp0ErrorEpc := 0x4000#32,
                       cp0Status := statusErlMask ||| statusExlMask, llBit := true } with
        | some s' => s'.pc == 0x4000#32 && s'.cp0Status == statusExlMask && s'.llBit
        | none => false)
-- eretnc in a delay slot: Reserved Instruction.
#guard (match stepState (buildProg textBase [.j 0x100#32, .eretnc]) regs0 with
        | some s1 => isRiInDelaySlot (hstep (buildProg textBase [.j 0x100#32, .eretnc]) s1)
        | none => false)
-- cache in Kernel Mode is a no-op (CACHE p.119: "should perform no operation").
#guard (let s := step1 (.cache 8#32 0x14#32 0x1f8#32) (setRegs regs0 [(8, 0x10010000#32)])
        s.pc == textBase + 4#32 && s.regs == (setRegs regs0 [(8, 0x10010000#32)]).regs &&
          s.cp0Cause == regs0.cp0Cause)
-- wait with a request pending and not masked out does not enter standby (WAIT p.442-443).
#guard (step1 (.wait 0#32) { regs0 with cp0Status := 0x20000100#32, cp0Cause := 0x00000100#32 }).standby
  == false
#guard (step1 (.wait 0#32) regs0).standby
-- Config5.SBRI is cleared by the Reset exception.
#guard (resetException { regs0 with cp0Config5SBRI := true }).cp0Config5SBRI == false
-- END R6-2
