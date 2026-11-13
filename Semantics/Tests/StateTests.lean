import Semantics.State

/-!
# Tests for `Semantics/State.lean`

Moved verbatim out of `Semantics/State.lean` (reviewability restructuring): the definition file now holds definitions only.
-/


-- `initialState`: sp init, all others zero, pc as given, empty mem/out
example : (initialState textBase).pc = textBase := by decide
example : (initialState textBase).regs[29]! = spInit := by decide
example : (initialState textBase).regs[0]! = 0#32 := by decide
example : (initialState textBase).regs[1]! = 0#32 := by decide
example : (initialState textBase).regs[31]! = 0#32 := by decide
example : (initialState textBase).hi = 0#32 := by decide
example : (initialState textBase).lo = 0#32 := by decide
example : (initialState textBase).fpRegs.size = 32 := by decide
example : (initialState textBase).fpRegs[0]! = 0#32 := by decide
example : (initialState textBase).fpRegs[31]! = 0#32 := by decide
example : (initialState textBase).fcsr = 0#32 := by decide
example : (initialState textBase).pendingBranch = none := by decide
example : (initialState textBase).llBit = false := by decide
-- `Std.HashMap` has no `DecidableEq`, and its operations are not kernel-reducible
-- (`decide`/`rfl`); check emptiness via a lookup checked with `#guard` instead.
#guard (initialState textBase).regs[29]! = spInit
#guard (initialState textBase).regs[0]! = 0#32
#guard (initialState textBase).fpRegs.size = 32
#guard (initialState textBase).mem.get? 0x10010000#32 = none

-- `readReg` / `writeReg`: `$zero` write-ignore
example : readReg (initialState textBase) 0 = 0#32 := by decide
example : readReg (writeReg (initialState textBase) 0 0xdeadbeef#32) 0 = 0#32 := by decide
-- writes to `$zero` leave the register file unchanged (checked field-by-field,
-- since `State`/`Std.HashMap` have no `DecidableEq`)
example :
    (writeReg (initialState textBase) 0 0xdeadbeef#32).regs
      = (initialState textBase).regs := by rfl
#guard readReg (initialState textBase) 0 = 0#32
#guard (writeReg (initialState textBase) 0 0xdeadbeef#32).regs = (initialState textBase).regs

-- `writeReg` / `readReg` round-trip for a non-zero register
example : readReg (writeReg (initialState textBase) 8 0x12345678#32) 8 = 0x12345678#32 := by
  decide
#guard readReg (writeReg (initialState textBase) 8 0x12345678#32) 8 = 0x12345678#32

-- writing one register leaves others untouched
example :
    readReg (writeReg (initialState textBase) 8 0x12345678#32) 9 = 0#32 := by decide

-- `readFpReg` / `writeFpReg`: round-trip, no `$f0` write-ignore (unlike GPRs)
example : readFpReg (initialState textBase) 0 = 0#32 := by decide
example : readFpReg (writeFpReg (initialState textBase) 0 0x3f800000#32) 0 = 0x3f800000#32 := by
  decide
example :
    readFpReg (writeFpReg (initialState textBase) 31 0x40400000#32) 31 = 0x40400000#32 := by
  decide
-- writing one FP register leaves others untouched
example : readFpReg (writeFpReg (initialState textBase) 8 0x12345678#32) 9 = 0#32 := by decide
#guard readFpReg (writeFpReg (initialState textBase) 0 0x3f800000#32) 0 = 0x3f800000#32

-- Instruction fetch is `readMemWord s s.pc`: alignment failure, a loaded word, unloaded memory
-- (reads as 0). The word is placed big-endian with `writeMemWord`.
def testFetchState : State :=
  (writeMemWord (initialState textBase) textBase 0xdeadbeef#32).getD (initialState textBase)
-- alignment failure short-circuits before touching the map, so `decide` works;
-- the others require evaluating the (cbv_opaque) `Std.HashMap`, so they are
-- checked only with `#guard` (compiled evaluation).
example : readMemWord (initialState textBase) (textBase + 1#32) = none := by decide
#guard readMemWord testFetchState (textBase + 1#32) = none
#guard readMemWord testFetchState textBase = some 0xdeadbeef#32
#guard readMemWord testFetchState (textBase + 4#32) = some 0#32

-- `readMemByte`: absent bytes read as 0
#guard readMemByte (initialState textBase) 0x10010000#32 = some 0

-- big-endian composition for half: bytes 0x12,0x34 at a,a+1 → 0x1234
def halfTestState : State :=
  { (initialState textBase) with
      mem := ((∅ : Std.HashMap W32 UInt8).insert 0x10010000#32 0x12)
               |>.insert 0x10010001#32 0x34 }
#guard readMemHalf halfTestState 0x10010000#32 = some 0x1234#32

-- half misalignment rejected
example : readMemHalf halfTestState 0x10010001#32 = none := by decide
#guard readMemHalf halfTestState 0x10010001#32 = none

-- big-endian composition for word: bytes 0x12,0x34,0x56,0x78 at a..a+3 → 0x12345678
def wordTestState : State :=
  { (initialState textBase) with
      mem := (((∅ : Std.HashMap W32 UInt8).insert 0x10010000#32 0x12).insert 0x10010001#32 0x34
                |>.insert 0x10010002#32 0x56).insert 0x10010003#32 0x78 }
#guard readMemWord wordTestState 0x10010000#32 = some 0x12345678#32

-- word misalignment rejected
example : readMemWord wordTestState 0x10010002#32 = none := by decide
#guard readMemWord wordTestState 0x10010002#32 = none

-- `writeMemByte`/`writeMemHalf`/`writeMemWord` round-trips
-- all memory writes/round-trips exercise the (cbv_opaque) `Std.HashMap`, so
-- these are checked with `#guard` (compiled evaluation) rather than `decide`.
#guard (writeMemByte (initialState textBase) 0x10010000#32 0x7f).bind
        (fun s => readMemByte s 0x10010000#32) = some 0x7f

#guard (writeMemHalf (initialState textBase) 0x10010000#32 0x1234#32).bind
        (fun s => readMemHalf s 0x10010000#32) = some 0x1234#32

#guard (writeMemWord (initialState textBase) 0x10010000#32 0x12345678#32).bind
        (fun s => readMemWord s 0x10010000#32) = some 0x12345678#32

-- big-endian byte layout after a word write: MSB at addr, LSB at addr+3
#guard (writeMemWord (initialState textBase) 0x10010000#32 0x12345678#32).bind
        (fun s => readMemByte s 0x10010000#32) = some 0x12
#guard (writeMemWord (initialState textBase) 0x10010000#32 0x12345678#32).bind
        (fun s => readMemByte s 0x10010003#32) = some 0x78

-- misaligned writes rejected
example : writeMemHalf (initialState textBase) 0x10010001#32 0x1234#32 = none := by decide
example : writeMemWord (initialState textBase) 0x10010001#32 0x12345678#32 = none := by decide
#guard writeMemHalf (initialState textBase) 0x10010001#32 0x1234#32 = none
#guard writeMemWord (initialState textBase) 0x10010001#32 0x12345678#32 = none

-- `initialState`: `Status` has only `CU1` set; the other CP0 registers start
-- zero (no exception has occurred), `EBase` at its reset value
example : (initialState textBase).cp0Status = 0x20000000#32 := by decide
example : (initialState textBase).cp0EBase = 0x80000000#32 := by decide
example : (initialState textBase).llAddr = 0#32 := by decide
example : (initialState textBase).cp0Cause = 0#32 := by decide
example : (initialState textBase).cp0Epc = 0#32 := by decide
example : (initialState textBase).cp0BadVAddr = 0#32 := by decide
example : (initialState textBase).cp0ErrorEpc = 0#32 := by decide
#guard (initialState textBase).cp0Status = statusCu1Mask
