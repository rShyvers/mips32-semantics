import Semantics.Tests.StepFixtures

/-!
# `step` tests: integer arithmetic, logic, shifts, multiply/divide, bit manipulation, immediates

Moved verbatim out of `Semantics/Step.lean` (reviewability restructuring): the definition file now holds definitions only.
Every check that calls `step`/`run` is a `#guard` (see `StepFixtures.lean` for why).
-/

open StepTest

-- ### Pure-arithmetic helper sanity (`by decide`/`by rfl`, no `Program`/`mem`)

example : regIdx (5#32) = (5 : Fin 32) := by decide
example : regIdx (31#32) = (31 : Fin 32) := by decide
example : (advance (initialState textBase) (initialState textBase)).pc = textBase + 4#32 := by decide
example : addOverflows 0x7fffffff (1 : Int) (-0x80000000 : Int) = true := by decide
example : addOverflows 5 7 12 = false := by decide
example : subOverflows (-0x80000000 : Int) 1 0x7fffffff = true := by decide
example : subOverflows 10 3 7 = false := by decide
example : signExtByte 0x80 = 0xffffff80#32 := by decide
example : zeroExtByte 0x80 = 0x00000080#32 := by decide
example : signExtLowByte 0x00000080#32 = 0xffffff80#32 := by decide
example : signExtLowByte 0x0000007f#32 = 0x0000007f#32 := by decide
example : countLeadingZeros 0#32 = 32 := by decide
example : countLeadingZeros 0xffffffff#32 = 0 := by decide
example : countLeadingZeros 0x80000000#32 = 0 := by decide
example : countLeadingZeros 1#32 = 31 := by decide
example : countLeadingZeros 0x0000ffff#32 = 16 := by decide
example : countLeadingOnes 0xffffffff#32 = 32 := by decide
example : countLeadingOnes 0#32 = 0 := by decide
example : countLeadingOnes 0xffff0000#32 = 16 := by decide
example : countLeadingOnes 0x7fffffff#32 = 0 := by decide  -- MSB clear -> zero leading ones
-- PC wraparound (W32 arithmetic): pc+4 wraps past 0xffffffff.
example : (0xfffffffc#32 : W32) + 4#32 = 0#32 := by decide

-- Misaligned instruction fetch short-circuits before touching `Program`
-- (same reasoning as `fetchWord`'s own tests in State.lean), so this is
-- provable by `decide` even though `step`'s signature takes a `Program`.
example : raisesAddr (hstep (∅ : Program) misalignedState) excCodeAdEL (textBase + 1#32) = true := by decide

-- ### R-type reg/reg/reg: one basic case each, plus `$zero` write-ignore

#guard nextRegEq (hstep (prog1 (.add 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 7#32)]))
  10 12#32
#guard nextRegEq (hstep (prog1 (.addu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 2#32)]))
  10 1#32
#guard nextRegEq (hstep (prog1 (.sub 8#32 9#32 10#32)) (setRegs regs0 [(8, 10#32), (9, 3#32)]))
  10 7#32
#guard nextRegEq (hstep (prog1 (.subu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0#32), (9, 1#32)]))
  10 0xffffffff#32
#guard nextRegEq (hstep (prog1 (.and 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]))
  10 0x0f000f00#32
#guard nextRegEq (hstep (prog1 (.or 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]))
  10 0xff0fff0f#32
#guard nextRegEq (hstep (prog1 (.xor 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)]))
  10 0xf00ff00f#32
#guard nextRegEq (hstep (prog1 (.nor 8#32 9#32 10#32)) (setRegs regs0 [(8, 0#32), (9, 0#32)]))
  10 0xffffffff#32
#guard nextRegEq (hstep (prog1 (.slt 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
  10 1#32  -- signed: -1 < 1
#guard nextRegEq (hstep (prog1 (.sltu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 1#32)]))
  10 0#32  -- unsigned: 0xffffffff is not < 1
-- `$rd = $zero` write-ignore, observed through `step` (and pc still advances)
#guard (match hstep (prog1 (.add 8#32 9#32 0#32)) (setRegs regs0 [(8, 5#32), (9, 7#32)]) with
        | .next s' => readReg s' 0 == 0#32 && s'.pc == textBase + 4#32
        | .halt _ => false)

-- ### movn/movz: conditional move -- the "condition fails" case must leave
-- `$rd` at its *preset* value (99 below), not zero it (a real no-op, per
-- docs/spec/INSTRUCTION-REF.md's movn/movz entries).
#guard nextRegEq (hstep (prog1 (.movn 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 1#32), (10, 99#32)]))
  10 5#32   -- movn, $rt != 0: moves
#guard nextRegEq (hstep (prog1 (.movn 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 0#32), (10, 99#32)]))
  10 99#32  -- movn, $rt == 0: $rd unchanged
#guard nextRegEq (hstep (prog1 (.movz 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 0#32), (10, 99#32)]))
  10 5#32   -- movz, $rt == 0: moves
#guard nextRegEq (hstep (prog1 (.movz 8#32 9#32 10#32)) (setRegs regs0 [(8, 5#32), (9, 1#32), (10, 99#32)]))
  10 99#32  -- movz, $rt != 0: $rd unchanged

-- ### add/sub overflow traps

#guard raises (hstep (prog1 (.add 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x7fffffff#32), (9, 1#32)])) excCodeOv
#guard raises (hstep (prog1 (.sub 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 1#32)])) excCodeOv
-- addu/subu never trap on the same operands
#guard isNext (hstep (prog1 (.addu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x7fffffff#32), (9, 1#32)]))
#guard isNext (hstep (prog1 (.subu 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 1#32)]))

-- ### Shifts: shamt 0 and 31; sra sign-fill

#guard nextRegEq (hstep (prog1 (.sll 10#32 8#32 0#32)) (setRegs regs0 [(8, 0x12345678#32)])) 10 0x12345678#32
#guard nextRegEq (hstep (prog1 (.sll 10#32 8#32 31#32)) (setRegs regs0 [(8, 1#32)])) 10 0x80000000#32
#guard nextRegEq (hstep (prog1 (.srl 10#32 8#32 0#32)) (setRegs regs0 [(8, 0x12345678#32)])) 10 0x12345678#32
#guard nextRegEq (hstep (prog1 (.srl 10#32 8#32 31#32)) (setRegs regs0 [(8, 0x80000000#32)])) 10 1#32
#guard nextRegEq (hstep (prog1 (.sra 10#32 8#32 0#32)) (setRegs regs0 [(8, 0x80000000#32)])) 10 0x80000000#32
#guard nextRegEq (hstep (prog1 (.sra 10#32 8#32 31#32)) (setRegs regs0 [(8, 0x80000000#32)])) 10 0xffffffff#32

-- ### slt vs sltu with a negative operand; slti/sltiu

#guard nextRegEq (hstep (prog1 (.slti 8#32 9#32 0x0000#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 9 1#32  -- -1 < 0
#guard nextRegEq (hstep (prog1 (.sltiu 8#32 9#32 0x0000#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 9 0#32 -- 0xffffffff </u 0 is false

-- ### mult / multu / div / divu / mflo / mfhi

-- mult: positive × positive
#guard nextHiLoEq (hstep (prog1 (.mult 8#32 9#32)) (setRegs regs0 [(8, 6#32), (9, 7#32)])) 0#32 42#32
-- mult: negative × negative, hi ≠ 0
#guard nextHiLoEq (hstep (prog1 (.mult 8#32 9#32)) (setRegs regs0 [(8, 0x88ca6c00#32), (9, 0x88ca6c00#32)]))
  0x3782dace#32 0x9d900000#32
-- mflo/mfhi read both halves back out
#guard (match stepState (prog1 (.mult 8#32 9#32)) (setRegs regs0 [(8, 0x88ca6c00#32), (9, 0x88ca6c00#32)]) with
        | some s' =>
          let s'' := { s' with pc := textBase }
          nextRegEq (hstep (prog1 (.mflo 10#32)) s'') 10 0x9d900000#32 &&
          nextRegEq (hstep (prog1 (.mfhi 11#32)) s'') 11 0x3782dace#32
        | none => false)
-- multu: both operands > 2^31
#guard nextHiLoEq (hstep (prog1 (.multu 8#32 9#32)) (setRegs regs0 [(8, 0xb2d05e00#32), (9, 0xb2d05e00#32)]))
  0x7ce66c50#32 0xe2840000#32

-- div: positive dividend
#guard nextHiLoEq (hstep (prog1 (.div 8#32 9#32)) (setRegs regs0 [(8, 17#32), (9, 5#32)])) 2#32 3#32
-- div: negative dividend — remainder takes the dividend's sign
#guard nextHiLoEq (hstep (prog1 (.div 8#32 9#32)) (setRegs regs0 [(8, 0xffffffef#32), (9, 5#32)]))
  0xfffffffe#32 0xfffffffd#32  -- hi = -2, lo = -3  (tdiv(-17,5)=-3, tmod(-17,5)=-2)
-- div: zero divisor with pre-seeded hi/lo — unchanged, no exception
private def seededHiLo : State := { regs0 with hi := 0xdeadbeef#32, lo := 0xcafef00d#32 }
#guard isNext (hstep (prog1 (.div 8#32 9#32)) (setRegs seededHiLo [(8, 10#32), (9, 0#32)]))
#guard nextHiLoEq (hstep (prog1 (.div 8#32 9#32)) (setRegs seededHiLo [(8, 10#32), (9, 0#32)]))
  0xdeadbeef#32 0xcafef00d#32
-- div: INT_MIN / -1 wraps silently (no exception, no overflow concept for div)
#guard nextHiLoEq (hstep (prog1 (.div 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 0xffffffff#32)]))
  0#32 0x80000000#32
-- divu: basic
#guard nextHiLoEq (hstep (prog1 (.divu 8#32 9#32)) (setRegs regs0 [(8, 17#32), (9, 5#32)])) 2#32 3#32
-- divu: zero divisor unchanged, no exception
#guard isNext (hstep (prog1 (.divu 8#32 9#32)) (setRegs seededHiLo [(8, 10#32), (9, 0#32)]))

-- ### mul (MIPS32 SPECIAL2 GPR multiply; docs/spec/MIPS-COVERAGE-GAPS.md §3.5)
-- `mul`'s result must match the low 32 bits `mult`+`mflo` would produce, for
-- the same operand pairs already exercised above -- including one whose
-- 64-bit product overflows 32 bits signed, confirming the wraparound -- and
-- `mul` must leave `hi`/`lo` unchanged (the pinned dialect choice).
#guard nextRegEq (hstep (prog1 (.mul 8#32 9#32 10#32)) (setRegs regs0 [(8, 6#32), (9, 7#32)])) 10 42#32  -- matches mult/mflo's lo above (0#32 42#32)
#guard nextRegEq (hstep (prog1 (.mul 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x88ca6c00#32), (9, 0x88ca6c00#32)]))
  10 0x9d900000#32  -- matches mult/mflo's lo above (overflows 32-bit signed: hi was nonzero, 0x3782dace)
#guard nextHiLoEq (hstep (prog1 (.mul 8#32 9#32 10#32)) (setRegs seededHiLo [(8, 6#32), (9, 7#32)]))
  0xdeadbeef#32 0xcafef00d#32  -- hi/lo unchanged by mul
#guard nextRegEq (hstep (prog1 (.mul 8#32 9#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32), (9, 2#32)])) 10 0xfffffffe#32  -- (-1) * 2 = -2, wraps

-- ### madd/maddu/msub/msubu/mthi/mtlo (MIPS32 multiply-accumulate and HI/LO
-- register moves; docs/spec/MIPS-COVERAGE-GAPS.md §3.5). The key property
-- that distinguishes these from mult/multu/mul: starting from a nonzero
-- `seededHiLo` accumulator, the result must be the *sum* (or difference) of
-- the prior accumulator and the product, never just the product alone.

-- madd: positive × positive (product 42, same pair as the plain mult test
-- above) accumulated on top of seededHiLo instead of overwriting it
#guard nextHiLoEq (hstep (prog1 (.madd 8#32 9#32)) (setRegs seededHiLo [(8, 6#32), (9, 7#32)]))
  0xdeadbeef#32 0xcafef037#32
-- madd: negative × negative (same pair as the mult test whose product is
-- 0x3782dace_9d900000), accumulated onto seededHiLo with a 64-bit carry
-- into the hi word
#guard nextHiLoEq (hstep (prog1 (.madd 8#32 9#32)) (setRegs seededHiLo [(8, 0x88ca6c00#32), (9, 0x88ca6c00#32)]))
  0x163099be#32 0x688ef00d#32
-- maddu: unsigned operands > 2^31 (same pair as the multu test above)
#guard nextHiLoEq (hstep (prog1 (.maddu 8#32 9#32)) (setRegs seededHiLo [(8, 0xb2d05e00#32), (9, 0xb2d05e00#32)]))
  0x5b942b40#32 0xad82f00d#32
-- msub: subtracts the product from the prior accumulator (inverse of the
-- positive madd case above)
#guard nextHiLoEq (hstep (prog1 (.msub 8#32 9#32)) (setRegs seededHiLo [(8, 6#32), (9, 7#32)]))
  0xdeadbeef#32 0xcafeefe3#32
-- msubu: unsigned subtract
#guard nextHiLoEq (hstep (prog1 (.msubu 8#32 9#32)) (setRegs seededHiLo [(8, 0xb2d05e00#32), (9, 0xb2d05e00#32)]))
  0x61c7529e#32 0xe87af00d#32

-- mthi/mtlo: write-direction counterparts to mfhi/mflo. Each sets only its
-- own half, leaving the other half (0 on regs0) untouched
#guard nextHiLoEq (hstep (prog1 (.mthi 8#32)) (setRegs regs0 [(8, 0x12345678#32)])) 0x12345678#32 0#32
#guard nextHiLoEq (hstep (prog1 (.mtlo 8#32)) (setRegs regs0 [(8, 0x87654321#32)])) 0#32 0x87654321#32
-- round trip through the register file: mthi $8 then mfhi $9 reads back
-- $8's original value (symmetric for mtlo/mflo)
#guard (match stepState (prog1 (.mthi 8#32)) (setRegs regs0 [(8, 0x12345678#32)]) with
        | some s' =>
          let s'' := { s' with pc := textBase }
          nextRegEq (hstep (prog1 (.mfhi 9#32)) s'') 9 0x12345678#32
        | none => false)
#guard (match stepState (prog1 (.mtlo 8#32)) (setRegs regs0 [(8, 0x87654321#32)]) with
        | some s' =>
          let s'' := { s' with pc := textBase }
          nextRegEq (hstep (prog1 (.mflo 9#32)) s'') 9 0x87654321#32
        | none => false)

-- ### clo/clz/movn/movz/seb/seh (MIPS32/MIPS32r2 additions; see
-- docs/spec/INSTRUCTION-REF.md)

-- clo: all-ones -> 32; a mixed pattern; all-zero -> 0 leading ones
#guard nextRegEq (hstep (prog1 (.clo 8#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 10 32#32
#guard nextRegEq (hstep (prog1 (.clo 8#32 10#32)) (setRegs regs0 [(8, 0xfff0ffff#32)])) 10 12#32
#guard nextRegEq (hstep (prog1 (.clo 8#32 10#32)) (setRegs regs0 [(8, 0x00000000#32)])) 10 0#32
-- clz: all-zero -> 32; a mixed pattern; all-ones -> 0 leading zeros
#guard nextRegEq (hstep (prog1 (.clz 8#32 10#32)) (setRegs regs0 [(8, 0x00000000#32)])) 10 32#32
#guard nextRegEq (hstep (prog1 (.clz 8#32 10#32)) (setRegs regs0 [(8, 0x0000ffff#32)])) 10 16#32
#guard nextRegEq (hstep (prog1 (.clz 8#32 10#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 10 0#32

-- seb: sign-extends only the low byte of $rt, ignoring higher bits
#guard nextRegEq (hstep (prog1 (.seb 10#32 8#32)) (setRegs regs0 [(8, 0x12345680#32)])) 10 0xffffff80#32
#guard nextRegEq (hstep (prog1 (.seb 10#32 8#32)) (setRegs regs0 [(8, 0x1234567f#32)])) 10 0x0000007f#32
-- seh: sign-extends only the low halfword of $rt
#guard nextRegEq (hstep (prog1 (.seh 10#32 8#32)) (setRegs regs0 [(8, 0x1234ffff#32)])) 10 0xffffffff#32
#guard nextRegEq (hstep (prog1 (.seh 10#32 8#32)) (setRegs regs0 [(8, 0x12347fff#32)])) 10 0x00007fff#32

-- ### sllv/srlv/srav (MIPS32 variable shifts; docs/spec/MIPS-COVERAGE-GAPS.md
-- §3.4): the shift amount is `$rs`'s low 5 bits, not a `shamt` field --
-- these mirror the sll/srl/sra shamt-0/31 cases above but via a register,
-- and a shift-amount register holding 33 (0x21, i.e. 32 + 1) must behave
-- identically to one holding 1 (the masking test).
#guard nextRegEq (hstep (prog1 (.sllv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x12345678#32), (9, 0#32)]))
  10 0x12345678#32
#guard nextRegEq (hstep (prog1 (.sllv 10#32 8#32 9#32)) (setRegs regs0 [(8, 1#32), (9, 31#32)]))
  10 0x80000000#32
#guard nextRegEq (hstep (prog1 (.srlv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 31#32)]))
  10 1#32
#guard nextRegEq (hstep (prog1 (.srav 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 31#32)]))
  10 0xffffffff#32
-- masking: shift-amount register holding 33 behaves identically to holding 1
#guard nextRegEq (hstep (prog1 (.sllv 10#32 8#32 9#32)) (setRegs regs0 [(8, 1#32), (9, 33#32)]))
  10 2#32
#guard nextRegEq (hstep (prog1 (.sllv 10#32 8#32 9#32)) (setRegs regs0 [(8, 1#32), (9, 1#32)]))
  10 2#32
#guard nextRegEq (hstep (prog1 (.srlv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 33#32)]))
  10 0x40000000#32
#guard nextRegEq (hstep (prog1 (.srlv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 1#32)]))
  10 0x40000000#32
#guard nextRegEq (hstep (prog1 (.srav 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 33#32)]))
  10 0xc0000000#32
#guard nextRegEq (hstep (prog1 (.srav 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x80000000#32), (9, 1#32)]))
  10 0xc0000000#32

-- ### rotr/rotrv/ext/ins/wsbh (MIPS32r2 additions; docs/spec/MIPS-COVERAGE-GAPS.md
-- §3.4)

-- rotr: wrap-around is the whole point -- contrast directly with `srl` on
-- the exact same input (0x80000000 >> 31 would be 1 either way, so use a
-- shamt where zero-fill and wrap-around visibly differ).
#guard nextRegEq (hstep (prog1 (.rotr 10#32 8#32 4#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x81234567#32  -- rotate right 4: low nibble (0x8) wraps to the top
#guard nextRegEq (hstep (prog1 (.srl 10#32 8#32 4#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x01234567#32  -- srl on the same input: zero-fills instead of wrapping
#guard nextRegEq (hstep (prog1 (.rotr 10#32 8#32 0#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x12345678#32  -- rotate by 0 is a no-op
#guard nextRegEq (hstep (prog1 (.rotr 10#32 8#32 31#32)) (setRegs regs0 [(8, 0x80000000#32)]))
  10 1#32  -- rotate right 31 == rotate left 1

-- rotrv: same wrap-around behavior, but the amount comes from a register's
-- low 5 bits (masking case included, mirroring sllv/srlv/srav above).
#guard nextRegEq (hstep (prog1 (.rotrv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x12345678#32), (9, 4#32)]))
  10 0x81234567#32
#guard nextRegEq (hstep (prog1 (.rotrv 10#32 8#32 9#32)) (setRegs regs0 [(8, 0x12345678#32), (9, 36#32)]))
  10 0x81234567#32  -- 36 & 0x1f = 4, masks identically to rotrv by 4

-- ext: extract a 10-bit field starting at bit 6 out of a known pattern.
-- 0x12345678 = 0001 0010 0011 0100 0101 0110 0111 1000; bits [15:6]
-- (10 bits starting at pos 6, i.e. (0x12345678 >> 6) & 0x3ff) = 0x159.
#guard nextRegEq (hstep (prog1 (.ext 10#32 8#32 6#32 10#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x159#32
-- ext: pos=0, size=32 extracts the whole register unchanged
#guard nextRegEq (hstep (prog1 (.ext 10#32 8#32 0#32 32#32)) (setRegs regs0 [(8, 0x89abcdef#32)]))
  10 0x89abcdef#32
-- ext: a single bit
#guard nextRegEq (hstep (prog1 (.ext 10#32 8#32 31#32 1#32)) (setRegs regs0 [(8, 0x80000000#32)]))
  10 1#32

-- ins: insert the low 10 bits of $rs (0x159) at pos 6 into $rt, leaving the
-- bits outside [15:6] unchanged -- round-trips with the `ext` example above.
#guard nextRegEq (hstep (prog1 (.ins 10#32 8#32 6#32 10#32)) (setRegs regs0 [(8, 0x159#32), (10, 0x12345678#32)]))
  10 0x12345678#32  -- re-inserting the field ext'd out above reproduces the original word
-- ins leaves bits outside the target field unchanged, even when the source
-- register has garbage in its higher bits (only the low `size` bits of $rs
-- are used) and $rt's target field previously held something different.
-- low 10 bits of $rs = 0xfffffc01 & 0x3ff = 0x001, shifted to pos 6 = 0x40;
-- $rt starts at 0, so only that one bit (bit 6) ends up set.
#guard nextRegEq (hstep (prog1 (.ins 10#32 8#32 6#32 10#32)) (setRegs regs0 [(8, 0xfffffc01#32), (10, 0x00000000#32)]))
  10 0x40#32
-- ext/ins round-trip: ins-ing a field then ext-racting it back gives the
-- original (masked-to-size) value, for an arbitrary field/position.
-- (`prog1` always places its single instruction at `textBase`, so a true
-- two-instruction sequence needs `buildProg`, threading the same program
-- across two `stepState` calls -- the first executes `ins` at `textBase`
-- and advances `pc` to `textBase+4`, where the second call then finds
-- `ext`.)
private def extInsRoundTripProg : Program :=
  buildProg textBase [.ins 10#32 8#32 3#32 7#32, .ext 11#32 10#32 3#32 7#32]
#guard (stepState extInsRoundTripProg (setRegs regs0 [(8, 0x7f#32), (10, 0#32)])).bind
        (fun s' => (stepState extInsRoundTripProg s').map (fun s'' => readReg s'' 11))
  = some 0x7f#32

-- wsbh: swap bytes within each halfword independently, halfwords stay put.
-- 0x12345678 -> halfword0 (0x5678) swaps to 0x7856, halfword1 (0x1234)
-- swaps to 0x3412 -> result 0x34127856.
#guard nextRegEq (hstep (prog1 (.wsbh 10#32 8#32)) (setRegs regs0 [(8, 0x12345678#32)]))
  10 0x34127856#32

-- ### addi overflow trap vs addiu wrap; andi/ori/xori high-imm-bits; lui

#guard raises (hstep (prog1 (.addi 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x7fffffff#32)])) excCodeOv
#guard nextRegEq (hstep (prog1 (.addiu 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x7fffffff#32)])) 9 0x80000000#32
-- `andi`/`ori`/`xori` zero-extend the immediate (imm bit 15 set must NOT sign-extend)
#guard nextRegEq (hstep (prog1 (.andi 8#32 9#32 0x8001#32)) (setRegs regs0 [(8, 0xffffffff#32)])) 9 0x00008001#32
#guard nextRegEq (hstep (prog1 (.ori 8#32 9#32 0x8001#32)) (setRegs regs0 [(8, 0#32)])) 9 0x00008001#32
#guard nextRegEq (hstep (prog1 (.xori 8#32 9#32 0x8001#32)) (setRegs regs0 [(8, 0#32)])) 9 0x00008001#32
#guard nextRegEq (hstep (prog1 (.lui 9#32 0x8001#32)) regs0) 9 0x80010000#32
