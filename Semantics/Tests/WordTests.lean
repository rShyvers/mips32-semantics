import Semantics.Word

/-!
# Tests for `Semantics/Word.lean`

Moved verbatim out of `Semantics/Word.lean` (reviewability restructuring): the definition file now holds definitions only.
-/


-- `signExt16`
example : signExt16 (0x00007fff#32) = 0x00007fff#32 := by decide
example : signExt16 (0x00008000#32) = 0xffff8000#32 := by decide
example : signExt16 (0x0000ffff#32) = 0xffffffff#32 := by decide
#guard signExt16 (0x00007fff#32) = 0x00007fff#32
#guard signExt16 (0x00008000#32) = 0xffff8000#32
#guard signExt16 (0x0000ffff#32) = 0xffffffff#32

-- `asSigned` / `ofInt32` round-trips
example : asSigned (0x00000000#32) = 0 := by decide
example : asSigned (0x00000001#32) = 1 := by decide
example : asSigned (0xffffffff#32) = -1 := by decide
example : asSigned (0x80000000#32) = -(2 ^ 31 : Int) := by decide
example : ofInt32 (-1) = 0xffffffff#32 := by decide
example : ofInt32 ((-2 ^ 31 : Int)) = 0x80000000#32 := by decide
example : ofInt32 (42 : Int) = 42#32 := by decide
-- wrap-around: values outside the 32-bit signed range wrap modulo 2^32
example : ofInt32 ((2 ^ 32 : Int) + 5) = 5#32 := by decide
example : asSigned (ofInt32 (-1)) = -1 := by decide
example : ofInt32 (asSigned (0xdeadbeef#32)) = 0xdeadbeef#32 := by decide
#guard asSigned (0x80000000#32) = -(2 ^ 31 : Int)
#guard ofInt32 (-1 : Int) = 0xffffffff#32

-- `zeroExt16`
example : zeroExt16 (0x0000ffff#32) = 0x0000ffff#32 := by decide
example : zeroExt16 (0xffff8000#32) = 0x00008000#32 := by decide
#guard zeroExt16 (0xffffffff#32) = 0x0000ffff#32

-- `maskLow`
example : maskLow 5 (0xffffffff#32) = 0x1f#32 := by decide
example : maskLow 6 (0b111111#32) = 0b111111#32 := by decide
example : maskLow 5 (0b100000#32) = 0#32 := by decide
#guard maskLow 16 (0xffffffff#32) = 0x0000ffff#32
