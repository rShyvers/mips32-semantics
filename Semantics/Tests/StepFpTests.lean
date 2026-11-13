import Semantics.Tests.StepFixtures

/-!
# `step` tests: coprocessor 1 (FPU)

Moved verbatim out of `Semantics/Step.lean` (reviewability restructuring): the definition file now holds definitions only.
Every check that calls `step`/`run` is a `#guard` (see `StepFixtures.lean` for why).
-/

open StepTest

-- ### Coprocessor 1 (FPU)
--
-- Bit patterns: 1.0 = 0x3f800000, 2.0 = 0x40000000, 2.5 = 0x40200000,
-- 3.0 = 0x40400000, 3.5 = 0x40600000, −2.5 = 0xc0200000, +∞ = 0x7f800000,
-- legacy QNaN 0x7fbfffff (the default), legacy SNaN 0x7fc00000.
-- FCSR fields: Cause V/Z/O/U/I = bits 16/15/14/13/12, Enables = 11..7,
-- Flags = 6..2, RM = 1..0, FCC0 = bit 23, FCC1..7 = bits 25..31.

private def fp1 (instr : Instruction) (fprs : List (Fin 32 × W32)) (fcsr : W32 := 0#32)
    (gprs : List (Fin 32 × W32) := []) : Outcome :=
  hstep (prog1 instr) { (setFpRegs (setRegs regs0 gprs) fprs) with fcsr := fcsr }

/-- `r` completed normally with `FPR[i] = v` and `FCSR = fcsr`. -/
private def fpIs (r : Outcome) (i : Fin 32) (v fcsr : W32) : Bool :=
  match r with
  | .next s => readFpReg s i == v && s.fcsr == fcsr && s.pc == textBase + 4#32
  | .halt _ => false

/-- `r` is a Floating Point exception entry (ExcCode 15, `CE` = 0) with
`FCSR = fcsr` and `FPR[i]` still `v`. -/
private def fpTraps (r : Outcome) (i : Fin 32) (v fcsr : W32) : Bool :=
  raises r excCodeFPE &&
    (match r with
     | .next s => readFpReg s i == v && s.fcsr == fcsr && s.cp0Cause &&& causeCeMask == 0#32
     | .halt _ => false)

private def nextFcsrEq (r : Outcome) (v : W32) : Bool :=
  match r with
  | .next s => s.fcsr == v
  | .halt _ => false

-- mtc1 then mfc1 round-trips an arbitrary bit pattern through $f3
#guard nextFpRegEq (hstep (prog1 (.mtc1 8#32 3#32)) (setRegs regs0 [(8, 0x12345678#32)])) 3
  0x12345678#32
#guard nextRegEq (fp1 (.mfc1 9#32 3#32) [(3, 0x12345678#32)]) 9 0x12345678#32
-- mfhc1/mthc1 address the high word of the double in $f4, i.e. FPR[5]
#guard nextRegEq (fp1 (.mfhc1 9#32 4#32) [(4, 0x11111111#32), (5, 0x22222222#32)]) 9 0x22222222#32
#guard nextFpRegEq (fp1 (.mthc1 9#32 4#32) [(4, 0x11111111#32)] 0#32 [(9, 0xabcdef01#32)]) 5
  0xabcdef01#32
#guard nextFpRegEq (fp1 (.mthc1 9#32 4#32) [(4, 0x11111111#32)] 0#32 [(9, 0xabcdef01#32)]) 4
  0x11111111#32

-- #### Arithmetic, rounding modes, flags
-- 1.0 + 2.0 = 3.0, exact: FCSR unchanged (Cause cleared)
#guard fpIs (fp1 (.addS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40000000#32)]) 2 0x40400000#32 0#32
-- an exact operation clears a stale Cause but keeps Flags, RM, FCC
#guard fpIs (fp1 (.addS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40000000#32)] 0xfe81f07f#32) 2
  0x40400000#32 0xfe80007f#32
-- 1.0 / 3.0 in the four rounding modes: Inexact in Cause (bit 12) and Flags (bit 2)
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40400000#32)] 0#32) 2
  0x3eaaaaab#32 0x00001004#32
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40400000#32)] 1#32) 2
  0x3eaaaaaa#32 0x00001005#32
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40400000#32)] 2#32) 2
  0x3eaaaaab#32 0x00001006#32
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40400000#32)] 3#32) 2
  0x3eaaaaaa#32 0x00001007#32
-- 1.0 / 0.0 = +∞, Divide by Zero (Cause bit 15, Flags bit 5)
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0#32)]) 2 0x7f800000#32 0x00008020#32
-- invalid operations create the legacy default QNaN 0x7fbfffff (V: bits 16 and 6)
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 0#32), (6, 0#32)]) 2 0x7fbfffff#32 0x00010040#32
#guard fpIs (fp1 (.subS 2#32 4#32 6#32) [(4, 0x7f800000#32), (6, 0x7f800000#32)]) 2 0x7fbfffff#32
  0x00010040#32
#guard fpIs (fp1 (.sqrtS 2#32 4#32) [(4, 0xbf800000#32)]) 2 0x7fbfffff#32 0x00010040#32
#guard fpIs (fp1 (.mulS 2#32 4#32 6#32) [(4, 0#32), (6, 0x7f800000#32)]) 2 0x7fbfffff#32 0x00010040#32
-- overflow: largest × 2 → +∞ under RN, largest under RZ (O|I: Cause 14,12; Flags 4,2)
#guard fpIs (fp1 (.mulS 2#32 4#32 6#32) [(4, 0x7f7fffff#32), (6, 0x40000000#32)]) 2 0x7f800000#32
  0x00005014#32
#guard fpIs (fp1 (.mulS 2#32 4#32 6#32) [(4, 0x7f7fffff#32), (6, 0x40000000#32)] 1#32) 2
  0x7f7fffff#32 0x00005015#32
-- underflow: smallest subnormal / 2 → 0 (U|I: Cause 13,12; Flags 3,2)
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 1#32), (6, 0x40000000#32)]) 2 0#32 0x0000300c#32
-- sqrt(2), sqrt(4)
#guard fpIs (fp1 (.sqrtS 2#32 4#32) [(4, 0x40000000#32)]) 2 0x3fb504f3#32 0x00001004#32
#guard fpIs (fp1 (.sqrtS 2#32 4#32) [(4, 0x40800000#32)]) 2 0x40000000#32 0#32
-- NaN propagation: a quiet NaN operand is copied, no exception; an SNaN signals Invalid
#guard fpIs (fp1 (.addS 2#32 4#32 6#32) [(4, 0x7f800123#32), (6, 0x3f800000#32)]) 2 0x7f800123#32 0#32
#guard fpIs (fp1 (.addS 2#32 4#32 6#32) [(4, 0x7fc00000#32), (6, 0x3f800000#32)]) 2 0x7fbfffff#32
  0x00010040#32
-- abs/neg are arithmetic: sign-bit only on numbers; any NaN signals Invalid
#guard fpIs (fp1 (.absS 2#32 4#32) [(4, 0xc0200000#32)]) 2 0x40200000#32 0#32
#guard fpIs (fp1 (.negS 2#32 4#32) [(4, 0x40200000#32)]) 2 0xc0200000#32 0#32
#guard fpIs (fp1 (.absS 2#32 4#32) [(4, 0x7fc00000#32)]) 2 0x7fbfffff#32 0x00010040#32   -- SNaN
#guard fpIs (fp1 (.negS 2#32 4#32) [(4, 0xff800123#32)]) 2 0xff800123#32 0x00010040#32   -- QNaN
-- mov.s is non-arithmetic: an SNaN is copied, FCSR untouched
#guard fpIs (fp1 (.movS 2#32 4#32) [(4, 0x7fc00000#32)] 0x0000f07c#32) 2 0x7fc00000#32 0x0000f07c#32
-- recip / rsqrt / madd family
#guard fpIs (fp1 (.recipS 2#32 4#32) [(4, 0x40000000#32)]) 2 0x3f000000#32 0#32
#guard fpIs (fp1 (.rsqrtS 2#32 4#32) [(4, 0x40800000#32)]) 2 0x3f000000#32 0#32
#guard fpIs (fp1 (.rsqrtS 2#32 4#32) [(4, 0#32)]) 2 0x7f800000#32 0x00008020#32
-- madd.s $f2, $f8(fr), $f4, $f6: 2 × 3 + 1 = 7; msub 5; nmadd −7; nmsub −5
#guard fpIs (fp1 (.maddS 2#32 8#32 4#32 6#32)
  [(4, 0x40000000#32), (6, 0x40400000#32), (8, 0x3f800000#32)]) 2 0x40e00000#32 0#32
#guard fpIs (fp1 (.msubS 2#32 8#32 4#32 6#32)
  [(4, 0x40000000#32), (6, 0x40400000#32), (8, 0x3f800000#32)]) 2 0x40a00000#32 0#32
#guard fpIs (fp1 (.nmaddS 2#32 8#32 4#32 6#32)
  [(4, 0x40000000#32), (6, 0x40400000#32), (8, 0x3f800000#32)]) 2 0xc0e00000#32 0#32
#guard fpIs (fp1 (.nmsubS 2#32 8#32 4#32 6#32)
  [(4, 0x40000000#32), (6, 0x40400000#32), (8, 0x3f800000#32)]) 2 0xc0a00000#32 0#32
-- unfused: (1+2^−23)² rounds to 1+2^−22 before −(1+2^−22) is added → +0, Inexact
#guard fpIs (fp1 (.maddS 2#32 8#32 4#32 6#32)
  [(4, 0x3f800001#32), (6, 0x3f800001#32), (8, 0xbf800002#32)]) 2 0#32 0x00001004#32

-- #### Conversions
-- cvt.w.s follows FCSR.RM: 3.5 → 4 (RN, even), 2.5 → 2 (RN), 3 (RP); −2.5 → −3 (RM), −2 (RZ)
#guard fpIs (fp1 (.cvtWS 2#32 4#32) [(4, 0x40600000#32)]) 2 4#32 0x00001004#32
#guard fpIs (fp1 (.cvtWS 2#32 4#32) [(4, 0x40200000#32)]) 2 2#32 0x00001004#32
#guard fpIs (fp1 (.cvtWS 2#32 4#32) [(4, 0x40200000#32)] 2#32) 2 3#32 0x00001006#32
#guard fpIs (fp1 (.cvtWS 2#32 4#32) [(4, 0xc0200000#32)] 3#32) 2 0xfffffffd#32 0x00001007#32
#guard fpIs (fp1 (.cvtWS 2#32 4#32) [(4, 0xc0200000#32)] 1#32) 2 0xfffffffe#32 0x00001005#32
-- round/trunc/ceil/floor ignore FCSR.RM (here RM = 3)
#guard fpIs (fp1 (.roundWS 2#32 4#32) [(4, 0x40200000#32)] 3#32) 2 2#32 0x00001007#32
#guard fpIs (fp1 (.roundWS 2#32 4#32) [(4, 0xc0200000#32)] 3#32) 2 0xfffffffe#32 0x00001007#32
#guard fpIs (fp1 (.roundWS 2#32 4#32) [(4, 0x40600000#32)] 3#32) 2 4#32 0x00001007#32
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0xc0200000#32)] 3#32) 2 0xfffffffe#32 0x00001007#32
#guard fpIs (fp1 (.ceilWS 2#32 4#32) [(4, 0x40200000#32)] 3#32) 2 3#32 0x00001007#32
#guard fpIs (fp1 (.floorWS 2#32 4#32) [(4, 0xc0200000#32)] 0#32) 2 0xfffffffd#32 0x00001004#32
-- invalid conversions: NaN, ±∞, out of range (either sign) → 0x7fffffff, Invalid
#guard fpIs (fp1 (.cvtWS 2#32 4#32) [(4, 0x7fbfffff#32)]) 2 0x7fffffff#32 0x00010040#32
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0xff800000#32)]) 2 0x7fffffff#32 0x00010040#32
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0x4f000000#32)]) 2 0x7fffffff#32 0x00010040#32   -- 2^31
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0xdf000000#32)]) 2 0x7fffffff#32 0x00010040#32   -- −2^63
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0xcf000000#32)]) 2 0x80000000#32 0#32            -- −2^31
-- the double forms read the pair ($f4 = low, $f5 = high): 2.5 = 0x4004000000000000
#guard fpIs (fp1 (.roundWD 2#32 4#32) [(4, 0#32), (5, 0x40040000#32)]) 2 2#32 0x00001004#32
#guard fpIs (fp1 (.ceilWD 2#32 4#32) [(4, 0#32), (5, 0x40040000#32)]) 2 3#32 0x00001004#32
#guard fpIs (fp1 (.floorWD 2#32 4#32) [(4, 0#32), (5, 0xc0040000#32)]) 2 0xfffffffd#32 0x00001004#32
#guard fpIs (fp1 (.truncWD 2#32 4#32) [(4, 0#32), (5, 0xc0040000#32)]) 2 0xfffffffe#32 0x00001004#32
#guard fpIs (fp1 (.cvtWD 2#32 4#32) [(4, 0#32), (5, 0x40040000#32)] 2#32) 2 3#32 0x00001006#32
#guard fpIs (fp1 (.cvtWD 2#32 4#32) [(4, 0#32), (5, 0x7ff00000#32)]) 2 0x7fffffff#32 0x00010040#32
-- cvt.s.w: 5 → 5.0; 2^24+1 is inexact (RN down, RP up)
#guard fpIs (fp1 (.cvtSW 2#32 4#32) [(4, 5#32)]) 2 0x40a00000#32 0#32
#guard fpIs (fp1 (.cvtSW 2#32 4#32) [(4, 16777217#32)]) 2 0x4b800000#32 0x00001004#32
#guard fpIs (fp1 (.cvtSW 2#32 4#32) [(4, 16777217#32)] 2#32) 2 0x4b800001#32 0x00001006#32
-- cvt.d.w −1 → −1.0 = 0xbff0000000000000; cvt.d.s 1.0; cvt.s.d of 1+2^−24 (a tie)
#guard (match fp1 (.cvtDW 2#32 4#32) [(4, 0xffffffff#32)] with
        | .next s => readFpD s 2#32 == 0xbff0000000000000#64 && s.fcsr == 0#32
        | .halt _ => false)
#guard (match fp1 (.cvtDS 2#32 4#32) [(4, 0x3f800000#32)] with
        | .next s => readFpD s 2#32 == 0x3ff0000000000000#64 && s.fcsr == 0#32
        | .halt _ => false)
#guard fpIs (fp1 (.cvtSD 2#32 4#32) [(4, 0x10000000#32), (5, 0x3ff00000#32)]) 2 0x3f800000#32
  0x00001004#32
#guard fpIs (fp1 (.cvtSD 2#32 4#32) [(4, 0x10000000#32), (5, 0x3ff00000#32)] 2#32) 2 0x3f800001#32
  0x00001006#32

-- #### Double-precision arithmetic (pairs: low word in $fN, high word in $fN+1)
-- 1.0 + 2.0 = 3.0 (0x4008000000000000)
#guard (match fp1 (.addD 2#32 4#32 6#32) [(5, 0x3ff00000#32), (7, 0x40000000#32)] with
        | .next s => readFpD s 2#32 == 0x4008000000000000#64 && s.fcsr == 0#32
        | .halt _ => false)
-- 1.0 / 3.0 = 0x3fd5555555555555, Inexact
#guard (match fp1 (.divD 2#32 4#32 6#32) [(5, 0x3ff00000#32), (7, 0x40080000#32)] with
        | .next s => readFpD s 2#32 == 0x3fd5555555555555#64 && s.fcsr == 0x00001004#32
        | .halt _ => false)
-- sqrt.d(2) = 0x3ff6a09e667f3bcd; sqrt.d(−1) → default QNaN 0x7ff7ffffffffffff, Invalid
#guard (match fp1 (.sqrtD 2#32 4#32) [(5, 0x40000000#32)] with
        | .next s => readFpD s 2#32 == 0x3ff6a09e667f3bcd#64 && s.fcsr == 0x00001004#32
        | .halt _ => false)
#guard (match fp1 (.sqrtD 2#32 4#32) [(5, 0xbff00000#32)] with
        | .next s => readFpD s 2#32 == 0x7ff7ffffffffffff#64 && s.fcsr == 0x00010040#32
        | .halt _ => false)
-- mov.d / neg.d / abs.d
#guard (match fp1 (.movD 2#32 4#32) [(4, 0x89abcdef#32), (5, 0x7ff80000#32)] 0x7c#32 with
        | .next s => readFpD s 2#32 == 0x7ff8000089abcdef#64 && s.fcsr == 0x7c#32
        | .halt _ => false)
#guard (match fp1 (.negD 2#32 4#32) [(4, 1#32), (5, 0x3ff00000#32)] with
        | .next s => readFpD s 2#32 == 0xbff0000000000001#64 && s.fcsr == 0#32
        | .halt _ => false)
#guard (match fp1 (.absD 2#32 4#32) [(4, 1#32), (5, 0xbff00000#32)] with
        | .next s => readFpD s 2#32 == 0x3ff0000000000001#64
        | .halt _ => false)
-- madd.d: 2 × 3 + 1 = 7 (0x401c000000000000)
#guard (match fp1 (.maddD 2#32 8#32 4#32 6#32)
          [(5, 0x40000000#32), (7, 0x40080000#32), (9, 0x3ff00000#32)] with
        | .next s => readFpD s 2#32 == 0x401c000000000000#64 && s.fcsr == 0#32
        | .halt _ => false)

-- #### Compare, condition codes, FP branches, conditional moves
-- c.eq.s $fcc0: 1.0 = 1.0 sets FCC0 (bit 23); c.lt.s $fcc7: 1.0 < 2.0 sets FCC7 (bit 31)
#guard nextFcsrEq (fp1 (.cCondS 2#32 0#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x3f800000#32)])
  0x00800000#32
#guard nextFcsrEq (fp1 (.cCondS 12#32 7#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40000000#32)])
  0x80000000#32
-- a false compare clears exactly its own condition code (here FCC1 = bit 25)
#guard nextFcsrEq (fp1 (.cCondS 2#32 1#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40000000#32)]
  0xfe800000#32) 0xfc800000#32
-- −0 = +0
#guard nextFcsrEq (fp1 (.cCondS 2#32 0#32 4#32 6#32) [(4, 0x80000000#32), (6, 0#32)]) 0x00800000#32
-- quiet predicates on a QNaN: no exception; c.un true, c.eq false, c.ueq true
#guard nextFcsrEq (fp1 (.cCondS 1#32 0#32 4#32 6#32) [(4, 0x7fbfffff#32), (6, 0x3f800000#32)])
  0x00800000#32
#guard nextFcsrEq (fp1 (.cCondS 2#32 0#32 4#32 6#32) [(4, 0x7fbfffff#32), (6, 0x3f800000#32)]) 0#32
#guard nextFcsrEq (fp1 (.cCondS 3#32 0#32 4#32 6#32) [(4, 0x7fbfffff#32), (6, 0x3f800000#32)])
  0x00800000#32
-- signaling predicates on a QNaN: Invalid (c.seq false; c.ngle true; c.sf false)
#guard nextFcsrEq (fp1 (.cCondS 10#32 0#32 4#32 6#32) [(4, 0x7fbfffff#32), (6, 0x3f800000#32)])
  0x00010040#32
#guard nextFcsrEq (fp1 (.cCondS 9#32 0#32 4#32 6#32) [(4, 0x7fbfffff#32), (6, 0x3f800000#32)])
  0x00810040#32
#guard nextFcsrEq (fp1 (.cCondS 8#32 2#32 4#32 6#32) [(4, 0x7fbfffff#32), (6, 0x3f800000#32)])
  0x00010040#32
-- c.ngt.s (15): true on less, equal, unordered
#guard nextFcsrEq (fp1 (.cCondS 15#32 0#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x3f800000#32)])
  0x00800000#32
#guard nextFcsrEq (fp1 (.cCondS 15#32 0#32 4#32 6#32) [(4, 0x40000000#32), (6, 0x3f800000#32)]) 0#32
-- an SNaN signals Invalid even for a quiet predicate
#guard nextFcsrEq (fp1 (.cCondS 2#32 0#32 4#32 6#32) [(4, 0x7fc00000#32), (6, 0x3f800000#32)])
  0x00010040#32
-- with Invalid enabled (bit 11) the compare traps and FCC is not written
#guard fpTraps (fp1 (.cCondS 9#32 0#32 4#32 6#32) [(4, 0x7fbfffff#32), (6, 0x3f800000#32)]
  0x00000800#32) 4 0x7fbfffff#32 0x00010800#32
-- c.cond.d: 1.0 < 2.0 on pairs, into FCC3 (bit 27)
#guard nextFcsrEq (fp1 (.cCondD 12#32 3#32 4#32 6#32) [(5, 0x3ff00000#32), (7, 0x40000000#32)])
  0x08000000#32

-- bc1t/bc1f test the selected condition code; ordinary delay slot
#guard nextPendingEq (hstep (prog1 (.bc1t 0#32 4#32)) { regs0 with fcsr := 0x00800000#32 })
  (some (textBase + 4#32 + 16#32))
#guard nextPendingEq (hstep (prog1 (.bc1t 0#32 4#32)) regs0) (some (textBase + 8#32))
#guard nextPendingEq (hstep (prog1 (.bc1f 0#32 4#32)) regs0) (some (textBase + 4#32 + 16#32))
#guard nextPendingEq (hstep (prog1 (.bc1t 7#32 4#32)) { regs0 with fcsr := 0x80000000#32 })
  (some (textBase + 4#32 + 16#32))
#guard nextPendingEq (hstep (prog1 (.bc1t 7#32 4#32)) { regs0 with fcsr := 0x7e800000#32 })
  (some (textBase + 8#32))
-- bc1tl/bc1fl: taken → as bc1t; not taken → delay slot nullified (pc + 8, nothing pending)
#guard nextPendingEq (hstep (prog1 (.bc1tl 0#32 4#32)) { regs0 with fcsr := 0x00800000#32 })
  (some (textBase + 4#32 + 16#32))
#guard (match hstep (prog1 (.bc1tl 0#32 4#32)) regs0 with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch.isNone
        | .halt _ => false)
#guard (match hstep (prog1 (.bc1fl 1#32 4#32)) { regs0 with fcsr := 0x02000000#32 } with
        | .next s => s.pc == textBase + 8#32 && s.pendingBranch.isNone
        | .halt _ => false)
#guard nextPendingEq (hstep (prog1 (.bc1fl 1#32 4#32)) regs0) (some (textBase + 4#32 + 16#32))
-- an FP branch in a delay slot raises Reserved Instruction like any other branch
#guard isRiInDelaySlot
  (hstep (prog1 (.bc1tl 0#32 4#32)) { regs0 with pendingBranch := some textBase })

-- movf/movt (GPR) and movf.s/movt.s/movn.s/movz.s
#guard nextRegEq (hstep (prog1 (.movf 8#32 0#32 9#32)) (setRegs regs0 [(8, 0x55#32), (9, 0x11#32)])) 9
  0x55#32
#guard nextRegEq (hstep (prog1 (.movt 8#32 0#32 9#32)) (setRegs regs0 [(8, 0x55#32), (9, 0x11#32)])) 9
  0x11#32
#guard nextRegEq (hstep (prog1 (.movt 8#32 5#32 9#32))
  { (setRegs regs0 [(8, 0x55#32), (9, 0x11#32)]) with fcsr := 0x20000000#32 }) 9 0x55#32
#guard fpIs (fp1 (.movfS 2#32 4#32 0#32) [(2, 0x11#32), (4, 0x7fc00000#32)]) 2 0x7fc00000#32 0#32
#guard fpIs (fp1 (.movtS 2#32 4#32 0#32) [(2, 0x11#32), (4, 0x7fc00000#32)]) 2 0x11#32 0#32
#guard fpIs (fp1 (.movnS 2#32 4#32 8#32) [(2, 0x11#32), (4, 0x22#32)] 0#32 [(8, 1#32)]) 2 0x22#32 0#32
#guard fpIs (fp1 (.movzS 2#32 4#32 8#32) [(2, 0x11#32), (4, 0x22#32)] 0#32 [(8, 1#32)]) 2 0x11#32 0#32
#guard (match fp1 (.movtD 2#32 4#32 1#32) [(4, 0x22#32), (5, 0x33#32)] 0x02000000#32 with
        | .next s => readFpD s 2#32 == 0x0000003300000022#64 && s.fcsr == 0x02000000#32
        | .halt _ => false)
#guard (match fp1 (.movzD 2#32 4#32 0#32) [(4, 0x22#32), (5, 0x33#32)] with
        | .next s => readFpD s 2#32 == 0x0000003300000022#64
        | .halt _ => false)

-- #### Control registers: cfc1 / ctc1
-- FIR (0) is a constant; FCSR (31) round-trips its non-reserved bits
#guard nextRegEq (fp1 (.cfc1 9#32 0#32) []) 9 0x00130000#32
#guard fpTraps (fp1 (.ctc1 8#32 31#32) [] 0#32 [(8, 0xffffffff#32)]) 0 0#32 0xff83ffff#32
#guard nextFcsrEq (fp1 (.ctc1 8#32 31#32) [] 0#32 [(8, 0x00800003#32)]) 0x00800003#32
#guard nextRegEq (fp1 (.cfc1 9#32 31#32) [] 0x00800003#32) 9 0x00800003#32
-- views after `ctc1 0x00800003 → $31`: FCCR (25) = 1 (FCC0), FENR (28) = 3 (RM), FEXR (26) = 0
#guard nextRegEq (fp1 (.cfc1 9#32 25#32) [] 0x00800003#32) 9 1#32
#guard nextRegEq (fp1 (.cfc1 9#32 28#32) [] 0x00800003#32) 9 3#32
#guard nextRegEq (fp1 (.cfc1 9#32 26#32) [] 0x00800003#32) 9 0#32
-- FCCR write sets all eight condition codes and nothing else
#guard nextFcsrEq (fp1 (.ctc1 8#32 25#32) [] 0x00000f83#32 [(8, 0xff#32)]) 0xfe800f83#32
-- FENR write: Enables, FS (bit 2 → FCSR bit 24), RM
#guard nextFcsrEq (fp1 (.ctc1 8#32 28#32) [] 0#32 [(8, 0x00000f87#32)]) 0x01000f83#32
-- FEXR write: Cause and Flags
#guard nextFcsrEq (fp1 (.ctc1 8#32 26#32) [] 3#32 [(8, 0x0001f07c#32)]) 0x0001f07f#32
-- CheckFPException: writing a Cause bit whose Enable is set traps, register written first
#guard fpTraps (fp1 (.ctc1 8#32 26#32) [] 0x00000080#32 [(8, 0x00001000#32)]) 0 0#32 0x00001080#32
-- … and so does Cause.E (bit 17), which has no enable
#guard fpTraps (fp1 (.ctc1 8#32 31#32) [] 0#32 [(8, 0x00020000#32)]) 0 0#32 0x00020000#32
-- FIR is read-only; a nonexistent control register reads 0 / ignores writes (pin)
#guard nextFcsrEq (fp1 (.ctc1 8#32 0#32) [] 0x7c#32 [(8, 0xffffffff#32)]) 0x7c#32
#guard nextRegEq (fp1 (.cfc1 9#32 7#32) [] 0x7c#32 [(9, 0x55#32)]) 9 0#32
#guard nextFcsrEq (fp1 (.ctc1 8#32 7#32) [] 0x7c#32 [(8, 0xffffffff#32)]) 0x7c#32

-- #### Floating Point exception (enabled exception): destination not written
-- Inexact enabled (bit 7): 1/3 traps; $f2 keeps 0xdead; Cause.I set, Flags untouched
#guard fpTraps (fp1 (.divS 2#32 4#32 6#32)
  [(2, 0xdead#32), (4, 0x3f800000#32), (6, 0x40400000#32)] 0x00000080#32) 2 0xdead#32 0x00001080#32
-- Divide-by-zero enabled (bit 10)
#guard fpTraps (fp1 (.divS 2#32 4#32 6#32)
  [(2, 0xdead#32), (4, 0x3f800000#32), (6, 0#32)] 0x00000400#32) 2 0xdead#32 0x00008400#32
-- Invalid enabled (bit 11): cvt.w.s of a NaN, abs.s of a NaN
#guard fpTraps (fp1 (.cvtWS 2#32 4#32) [(2, 0xdead#32), (4, 0x7fbfffff#32)] 0x00000800#32) 2
  0xdead#32 0x00010800#32
#guard fpTraps (fp1 (.absS 2#32 4#32) [(2, 0xdead#32), (4, 0x7fbfffff#32)] 0x00000800#32) 2
  0xdead#32 0x00010800#32
-- Underflow enabled (bit 8): an exact tiny result (2^−126 × 0.5) traps
#guard fpTraps (fp1 (.mulS 2#32 4#32 6#32)
  [(2, 0xdead#32), (4, 0x00800000#32), (6, 0x3f000000#32)] 0x00000100#32) 2 0xdead#32 0x00002100#32
#guard fpIs (fp1 (.mulS 2#32 4#32 6#32) [(4, 0x00800000#32), (6, 0x3f000000#32)]) 2 0x00400000#32 0#32
-- a double result is not written either
#guard (match fp1 (.divD 2#32 4#32 6#32)
          [(2, 0xdead#32), (3, 0xbeef#32), (5, 0x3ff00000#32), (7, 0x40080000#32)] 0x00000080#32 with
        | .next s => readFpD s 2#32 == 0x0000beef0000dead#64 && causeExcCode s == excCodeFPE &&
            s.fcsr == 0x00001080#32 && s.cp0Epc == textBase
        | .halt _ => false)
-- FS = 1 (bit 24): a tiny result is flushed to zero with Underflow | Inexact
#guard fpIs (fp1 (.mulS 2#32 4#32 6#32) [(4, 0x00800000#32), (6, 0x3f000000#32)] 0x01000000#32) 2
  0#32 0x0100300c#32

-- #### Coprocessor Unusable: Status.CU1 = 0
private def noCu1 (s : State) : State := { s with cp0Status := 0#32 }

/-- `r` is a Coprocessor Unusable entry with `Cause.CE = ce`, and the FP
registers and FCSR are those of `s`. -/
private def cpuRaised (r : Outcome) (s : State) (ce : W32) : Bool :=
  raises r excCodeCpU &&
    (match r with
     | .next s' => (s'.cp0Cause &&& causeCeMask) == ce <<< 28 && s'.fpRegs == s.fpRegs &&
         s'.fcsr == s.fcsr && s'.regs == s.regs && s'.cp0Epc == s.pc
     | .halt _ => false)

private def cuState : State :=
  noCu1 { (setFpRegs (setRegs regs0 [(8, 0x10010000#32), (9, 0x77#32)])
      [(2, 0x11#32), (4, 0x3f800000#32), (6, 0x40000000#32)]) with fcsr := 0x00800003#32 }

#guard [Instruction.addS 2#32 4#32 6#32, .addD 2#32 4#32 6#32, .mfc1 9#32 4#32, .mtc1 9#32 4#32,
    .mfhc1 9#32 4#32, .mthc1 9#32 4#32, .cfc1 9#32 31#32, .ctc1 9#32 31#32,
    .lwc1 8#32 2#32 0#32, .swc1 8#32 2#32 0#32, .ldc1 8#32 2#32 0#32, .sdc1 8#32 2#32 0#32,
    .lwxc1 2#32 0#32 8#32, .sdxc1 2#32 0#32 8#32, .prefx 0#32 0#32 8#32,
    .movS 2#32 4#32, .absD 2#32 4#32, .cvtWS 2#32 4#32, .cvtDW 2#32 4#32, .sqrtS 2#32 4#32,
    .cCondS 2#32 0#32 4#32 6#32, .cCondD 2#32 0#32 4#32 6#32,
    .movfS 2#32 4#32 0#32, .movnD 2#32 4#32 9#32, .movf 9#32 0#32 10#32, .movt 9#32 0#32 10#32,
    .maddS 2#32 2#32 4#32 6#32, .nmsubD 2#32 2#32 4#32 6#32, .recipS 2#32 4#32, .rsqrtD 2#32 4#32,
    .roundWD 2#32 4#32, .bc1f 0#32 4#32, .bc1t 0#32 4#32, .bc1fl 0#32 4#32, .bc1tl 0#32 4#32].all
  fun i => cpuRaised (hstep (prog1 i) cuState) cuState 1#32
-- … and none of them raises it when CU1 = 1
#guard !(raises (hstep (prog1 (.addS 2#32 4#32 6#32)) { cuState with cp0Status := statusCu1Mask })
  excCodeCpU)
-- integer instructions and `pref` are unaffected by CU1
#guard isNext (hstep (prog1 (.addu 8#32 9#32 10#32)) cuState)
#guard isNext (hstep (prog1 (.pref 8#32 0#32 0#32)) cuState)
-- a reserved COP1 encoding: Coprocessor Unusable when CU1 = 0, Reserved Instruction when 1
#guard cpuRaised (hstep ((∅ : Program).insert textBase 0x47e00000#32) cuState) cuState 1#32
#guard raises (hstep ((∅ : Program).insert textBase 0x47e00000#32) regs0) excCodeRI
-- reserved COP1X (luxc1) and MOVCI (bit 17 set) words likewise
#guard cpuRaised (hstep ((∅ : Program).insert textBase 0x4c000005#32) cuState) cuState 1#32
#guard cpuRaised (hstep ((∅ : Program).insert textBase 0x00020001#32) cuState) cuState 1#32
#guard raises (hstep ((∅ : Program).insert textBase 0x00020001#32) regs0) excCodeRI
-- coprocessor 2 does not exist: COP2 / LWC2 words raise Coprocessor Unusable with CE = 2
#guard cpuRaised (hstep ((∅ : Program).insert textBase 0x48000000#32) regs0) regs0 2#32
#guard cpuRaised (hstep ((∅ : Program).insert textBase 0xc8000000#32) regs0) regs0 2#32
-- CpU in a delay slot: EPC = branch, BD set
#guard (match hstep (prog1 (.addS 2#32 4#32 6#32)) { cuState with pendingBranch := some 0x1000#32 } with
        | .next s => s.cp0Epc == textBase - 4#32 && s.cp0Cause == 0x9000002c#32
        | .halt _ => false)
-- a later exception reloads CE with 0
#guard (match hstep (prog1 (.break 0#32)) { regs0 with cp0Cause := 0x10000000#32 } with
        | .next s => s.cp0Cause == 0x00000024#32
        | .halt _ => false)

-- #### FP loads/stores
private def fpMemTestState : State :=
  { (setRegs regs0 [(8, 0x10010000#32), (9, 4#32)]) with
      mem := (((∅ : Std.HashMap W32 UInt8).insert 0x10010004#32 0x3f).insert 0x10010005#32 0x80)
               |>.insert 0x10010006#32 0x00 |>.insert 0x10010007#32 0x00 }  -- 1.0 at offset 4
#guard nextFpRegEq (hstep (prog1 (.lwc1 8#32 9#32 4#32)) fpMemTestState) 9 0x3f800000#32
#guard nextFpRegEq (hstep (prog1 (.lwxc1 3#32 9#32 8#32)) fpMemTestState) 3 0x3f800000#32
#guard (stepState (prog1 (.swc1 8#32 9#32 4#32))
          (setFpRegs (setRegs regs0 [(8, 0x10010000#32)]) [(9, 0x3f800000#32)])).bind
        (fun s' => readMemWord s' 0x10010004#32) = some 0x3f800000#32
#guard (stepState (prog1 (.swxc1 9#32 10#32 8#32))
          (setFpRegs (setRegs regs0 [(8, 0x10010000#32), (10, 8#32)]) [(9, 0x3f800000#32)])).bind
        (fun s' => readMemWord s' 0x10010008#32) = some 0x3f800000#32
#guard raisesAddr (hstep (prog1 (.lwc1 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)]))
  excCodeAdEL 0x10010001#32
#guard raisesAddr (hstep (prog1 (.swxc1 9#32 10#32 8#32))
  (setRegs regs0 [(8, 0x10010000#32), (10, 2#32)])) excCodeAdES 0x10010002#32

-- ldc1/sdc1: big-endian doubleword (high word at the lower address), doubleword-aligned
private def dpMemTestState : State :=
  { (setRegs regs0 [(8, 0x10010000#32), (9, 8#32)]) with
      mem := ((((∅ : Std.HashMap W32 UInt8).insert 0x10010008#32 0x3f).insert 0x10010009#32 0xf0)
               |>.insert 0x1001000f#32 0x01) }  -- 0x3ff0000000000001 at offset 8
#guard (match hstep (prog1 (.ldc1 8#32 2#32 8#32)) dpMemTestState with
        | .next s => readFpD s 2#32 == 0x3ff0000000000001#64 && readFpReg s 3 == 0x3ff00000#32
        | .halt _ => false)
#guard (match hstep (prog1 (.ldxc1 2#32 9#32 8#32)) dpMemTestState with
        | .next s => readFpD s 2#32 == 0x3ff0000000000001#64
        | .halt _ => false)
#guard (stepState (prog1 (.sdc1 8#32 2#32 16#32))
          (setFpRegs (setRegs regs0 [(8, 0x10010000#32)]) [(2, 0x89abcdef#32), (3, 0x01234567#32)])).bind
        (fun s' => (readMemWord s' 0x10010010#32).bind fun hi =>
          (readMemWord s' 0x10010014#32).map fun lo => (hi, lo))
      = some (0x01234567#32, 0x89abcdef#32)
#guard (stepState (prog1 (.sdxc1 2#32 9#32 8#32))
          (setFpRegs (setRegs regs0 [(8, 0x10010000#32), (9, 16#32)])
            [(2, 0x89abcdef#32), (3, 0x01234567#32)])).bind
        (fun s' => readMemWord s' 0x10010010#32) = some 0x01234567#32
-- word-aligned but not doubleword-aligned: Address Error
#guard raisesAddr (hstep (prog1 (.ldc1 8#32 2#32 4#32)) dpMemTestState) excCodeAdEL 0x10010004#32
#guard raisesAddr (hstep (prog1 (.sdc1 8#32 2#32 4#32)) dpMemTestState) excCodeAdES 0x10010004#32
#guard raisesAddr (hstep (prog1 (.ldxc1 2#32 9#32 8#32))
  (setRegs regs0 [(8, 0x10010000#32), (9, 12#32)])) excCodeAdEL 0x1001000c#32
#guard raisesAddr (hstep (prog1 (.sdxc1 2#32 9#32 8#32))
  (setRegs regs0 [(8, 0x10010000#32), (9, 12#32)])) excCodeAdES 0x1001000c#32
-- a store clears LLbit; a failed (misaligned) one does not get that far
#guard nextLlBitEq (hstep (prog1 (.sdc1 8#32 2#32 8#32)) { dpMemTestState with llBit := true }) false
