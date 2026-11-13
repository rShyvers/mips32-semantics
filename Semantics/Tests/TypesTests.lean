import Semantics.Types

/-!
# Tests for `Semantics/Types.lean`

Moved verbatim out of `Semantics/Types.lean` (reviewability restructuring): the definition file now holds definitions only.
-/


-- `mkRT`: rs=5, rt=6, rd=7, shamt=3, funct=0x20 (add)
-- 000000 00101 00110 00111 00011 100000
example :
    mkRT (5#32) (6#32) (7#32) (3#32) (0x20#32)
      = 0b00000000101001100011100011100000#32 := by decide
#guard mkRT (5#32) (6#32) (7#32) (3#32) (0x20#32)
    = 0b00000000101001100011100011100000#32

-- masking: out-of-range field bits are discarded
example : mkRT (0xff#32) (0#32) (0#32) (0#32) (0#32) = field 5 21 (0xff#32) := by decide

-- `mkIT`: opcode=0x23 (lw), rs=29 ($sp), rt=8 ($t0), imm=0x1234
example :
    mkIT (0x23#32) (29#32) (8#32) (0x1234#32)
      = 0b100011_11101_01000_0001001000110100#32 := by decide
#guard mkIT (0x23#32) (29#32) (8#32) (0x1234#32)
    = 0b100011_11101_01000_0001001000110100#32

-- `mkJT`: target = 0x3ffffff (all 26 bits set)
example : mkJT (0x3ffffff#32) = 0x3ffffff#32 := by decide
#guard mkJT (0xffffffff#32) = 0x3ffffff#32

-- `State` construction and field read-back
def sampleState : State :=
  { pc := textBase
    regs := (Array.replicate 32 (0#32)).set! 29 spInit
    hi := 0#32
    lo := 0#32
    fpRegs := Array.replicate 32 (0#32)
    fcsr := 0#32
    physMem := ∅
    cp0Status := 0#32
    cp0Cause := 0#32
    cp0Epc := 0#32 }

example : sampleState.pc = textBase := by decide
example : sampleState.regs.size = 32 := by decide
example : sampleState.regs[29]! = spInit := by decide
example : sampleState.fpRegs.size = 32 := by decide
example : sampleState.fpRegs[0]! = 0#32 := by decide
example : sampleState.fcsr = 0#32 := by decide
#guard sampleState.pc = textBase
#guard sampleState.regs.size = 32
#guard sampleState.regs[29]! = spInit
#guard sampleState.fpRegs.size = 32
#guard sampleState.fcsr = 0#32


-- `State.pendingBranch` defaults to `none` when omitted from a literal
example : sampleState.pendingBranch = none := by decide
#guard sampleState.pendingBranch = none
-- `State.llBit` defaults to `false` when omitted from a literal
example : sampleState.llBit = false := by decide
#guard sampleState.llBit = false
-- the two CP0 registers with defaults
example : sampleState.cp0BadVAddr = 0#32 := by decide
example : sampleState.cp0ErrorEpc = 0#32 := by decide
example : sampleState.llAddr = 0#32 := by decide
example : sampleState.cp0EBase = 0x80000000#32 := by decide
example : excCodeFPE = 15#32 := by decide
example : causeCeMask = 3#32 <<< 28 := by decide
example : ebaseFixedBits ||| exceptionVectorOffset = exceptionVectorAddr := by decide
-- CP0 fields: `sampleState` reads back the zero-initialized fields; the
-- exception constants are distinct small values as documented.
example : sampleState.cp0Status = 0#32 := by decide
example : sampleState.cp0Cause = 0#32 := by decide
example : sampleState.cp0Epc = 0#32 := by decide
#guard sampleState.cp0Status = 0#32
example : exceptionVectorAddr = 0x80000180#32 := by decide
example : excCodeBp ≠ excCodeTr := by decide
example : excCodeBp = 9#32 := by decide
example : excCodeTr = 13#32 := by decide
example : statusExlMask = 2#32 := by decide
example : exceptionVectorBevAddr = 0xbfc00380#32 := by decide
example : statusWriteMask = statusIeMask ||| statusExlMask ||| statusErlMask ||| statusUmMask
    ||| statusImMask ||| statusBevMask ||| statusCu0Mask ||| statusCu1Mask := by decide
example : statusUmMask = 1#32 <<< 4 := by decide
example : statusCu0Mask = 1#32 <<< 28 := by decide
example : causeDcMask = 1#32 <<< 27 := by decide
example : resetVector = 0xbfc00000#32 := by decide
example : causeWriteMask = (1#32 <<< 27) ||| (1#32 <<< 23) ||| (3#32 <<< 8) := by decide
example : causeExcCodeMask = 0x1f#32 <<< 2 := by decide
