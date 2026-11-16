import Semantics.Tests.StepFixtures

/-!
# `step` tests: coprocessor 1 (FPU)

Originally moved out of `Semantics/Step.lean` (reviewability restructuring); updated for the Release 6 FPU (wave R6-5).
Every check that calls `step`/`run` is a `#guard` (see `StepFixtures.lean` for why).
-/

open StepTest

-- ### Coprocessor 1 (FPU), Release 6
--
-- 64-bit FPRs (`Status.FR = 1`): a single/word lives in the low 32 bits, a 32-bit write keeps the
-- upper half (model pin), a double/longword is the whole register.
-- Bit patterns: 1.0 = 0x3f800000, 2.0 = 0x40000000, 2.5 = 0x40200000,
-- 3.0 = 0x40400000, 3.5 = 0x40600000, −2.5 = 0xc0200000, +∞ = 0x7f800000;
-- IEEE 754-2008 NaNs (`FCSR.NAN2008 = 1`): quiet bit = fraction MSB set, default QNaN 0x7fc00000
-- (double 0x7ff8000000000000), SNaN e.g. 0x7f800123 (MD00082 Vol I-A Rev 6.01 Table 6.3, p.82).
-- FCSR fields (stored writable bits): FS = 24, Cause E/V/Z/O/U/I = bits 17/16/15/14/13/12,
-- Enables = 11..7, Flags = 6..2, RM = 1..0; a read of FCSR adds ABS2008/NAN2008 (bits 19, 18).

private def fp1 (instr : Instruction) (fprs : List (Fin 32 × W32)) (fcsr : W32 := 0#32)
    (gprs : List (Fin 32 × W32) := []) : Outcome :=
  hstep (prog1 instr) { (setFpRegs (setRegs regs0 gprs) fprs) with fcsr := fcsr }

/-- As `fp1`, with whole 64-bit FPR values. -/
private def fp64 (instr : Instruction) (fprs : List (Fin 32 × BitVec 64)) (fcsr : W32 := 0#32)
    (gprs : List (Fin 32 × W32) := []) : Outcome :=
  hstep (prog1 instr) { (setFpRegs64 (setRegs regs0 gprs) fprs) with fcsr := fcsr }

/-- `r` completed normally with (the low 32 bits of) `FPR[i] = v` and `FCSR = fcsr`. -/
private def fpIs (r : Outcome) (i : Fin 32) (v fcsr : W32) : Bool :=
  match r with
  | .next s => readFpReg s i == v && s.fcsr == fcsr && s.pc == textBase + 4#32
  | .halt _ => false

/-- `r` completed normally with the whole 64-bit `FPR[i] = v` and `FCSR = fcsr`. -/
private def fpIs64 (r : Outcome) (i : Fin 32) (v : BitVec 64) (fcsr : W32) : Bool :=
  match r with
  | .next s => readFpReg64 s i == v && s.fcsr == fcsr && s.pc == textBase + 4#32
  | .halt _ => false

/-- `r` is a Floating Point exception entry (ExcCode 15, `CE` = 0) with
`FCSR = fcsr` and the whole `FPR[i]` still `v`. -/
private def fpTraps64 (r : Outcome) (i : Fin 32) (v : BitVec 64) (fcsr : W32) : Bool :=
  raises r excCodeFPE &&
    (match r with
     | .next s => readFpReg64 s i == v && s.fcsr == fcsr && s.cp0Cause &&& causeCeMask == 0#32
     | .halt _ => false)

/-- `r` is a Floating Point exception entry with `FCSR = fcsr` and (the low half of) `FPR[i]` still
`v`. -/
private def fpTraps (r : Outcome) (i : Fin 32) (v fcsr : W32) : Bool :=
  raises r excCodeFPE &&
    (match r with
     | .next s => readFpReg s i == v && s.fcsr == fcsr && s.cp0Cause &&& causeCeMask == 0#32
     | .halt _ => false)

private def nextFcsrEq (r : Outcome) (v : W32) : Bool :=
  match r with
  | .next s => s.fcsr == v
  | .halt _ => false

-- #### Moves and the 64-bit register file
-- mtc1 then mfc1 round-trips an arbitrary bit pattern through $f3
#guard nextFpRegEq (hstep (prog1 (.mtc1 8#32 3#32)) (setRegs regs0 [(8, 0x12345678#32)])) 3
  0x12345678#32
#guard nextRegEq (fp1 (.mfc1 9#32 3#32) [(3, 0x12345678#32)]) 9 0x12345678#32
-- mtc1 writes the low word and keeps the upper half of the 64-bit FPR (model pin, MD00082 Vol I-A
-- Rev 6.01 §6.6.2, p.98); mfc1 reads the low word only
#guard nextFpReg64Eq (hstep (prog1 (.mtc1 8#32 3#32))
  (setFpRegs64 (setRegs regs0 [(8, 0x12345678#32)]) [(3, 0xcafebabe00000000#64)])) 3
  0xcafebabe12345678#64
#guard nextRegEq (fp64 (.mfc1 9#32 3#32) [(3, 0xcafebabe12345678#64)]) 9 0x12345678#32
-- mfhc1/mthc1 address bits 63..32 of the same FPR (not FPR[fs+1])
#guard nextRegEq (fp64 (.mfhc1 9#32 4#32) [(4, 0x2222222211111111#64), (5, 0x33333333#64)]) 9
  0x22222222#32
#guard nextRegEq (fp64 (.mfhc1 9#32 5#32) [(5, 0x4444444433333333#64)]) 9 0x44444444#32
#guard nextFpReg64Eq (fp64 (.mthc1 9#32 4#32) [(4, 0x11111111#64)] 0#32 [(9, 0xabcdef01#32)]) 4
  0xabcdef0111111111#64
#guard nextFpReg64Eq (fp64 (.mthc1 9#32 4#32) [(4, 0x11111111#64)] 0#32 [(9, 0xabcdef01#32)]) 5 0#64
-- odd registers hold doubles too: mthc1 + mtc1 on $f7
#guard nextFpReg64Eq (fp64 (.mthc1 9#32 7#32) [(7, 0x89abcdef#64)] 0#32 [(9, 0x01234567#32)]) 7
  0x0123456789abcdef#64

-- #### Arithmetic, rounding modes, flags
-- 1.0 + 2.0 = 3.0, exact: FCSR unchanged (Cause cleared)
#guard fpIs (fp1 (.addS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40000000#32)]) 2 0x40400000#32 0#32
-- a single result keeps the upper half of FPR[fd]
#guard fpIs64 (fp64 (.addS 2#32 4#32 6#32)
  [(2, 0xaaaaaaaa00000000#64), (4, 0x3f800000#64), (6, 0x40000000#64)]) 2 0xaaaaaaaa40400000#64 0#32
-- an exact operation clears a stale Cause but keeps Flags and RM
#guard fpIs (fp1 (.addS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40000000#32)] 0x0001f07f#32) 2
  0x40400000#32 0x0000007f#32
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
-- invalid operations create the default QNaN 0x7fc00000 (V: bits 16 and 6)
#guard fpIs (fp1 (.divS 2#32 4#32 6#32) [(4, 0#32), (6, 0#32)]) 2 0x7fc00000#32 0x00010040#32
#guard fpIs (fp1 (.subS 2#32 4#32 6#32) [(4, 0x7f800000#32), (6, 0x7f800000#32)]) 2 0x7fc00000#32
  0x00010040#32
#guard fpIs (fp1 (.sqrtS 2#32 4#32) [(4, 0xbf800000#32)]) 2 0x7fc00000#32 0x00010040#32
#guard fpIs (fp1 (.mulS 2#32 4#32 6#32) [(4, 0#32), (6, 0x7f800000#32)]) 2 0x7fc00000#32 0x00010040#32
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
-- NaN propagation: a quiet NaN operand is copied, no exception; an SNaN is made quiet (payload
-- kept) and signals Invalid; an SNaN takes precedence over a QNaN
#guard fpIs (fp1 (.addS 2#32 4#32 6#32) [(4, 0x7fc00123#32), (6, 0x3f800000#32)]) 2 0x7fc00123#32 0#32
#guard fpIs (fp1 (.addS 2#32 4#32 6#32) [(4, 0x7f800123#32), (6, 0x3f800000#32)]) 2 0x7fc00123#32
  0x00010040#32
#guard fpIs (fp1 (.addS 2#32 4#32 6#32) [(4, 0x7fc00011#32), (6, 0x7f800022#32)]) 2 0x7fc00022#32
  0x00010040#32
-- abs/neg are non-arithmetic (FCSR.ABS2008 = 1): only the sign bit changes, NaNs included, and
-- FCSR is not modified (not even Cause) (MD00086 Vol II-A Rev 6.06, ABS.fmt p.32, NEG.fmt p.307)
#guard fpIs (fp1 (.absS 2#32 4#32) [(4, 0xc0200000#32)]) 2 0x40200000#32 0#32
#guard fpIs (fp1 (.negS 2#32 4#32) [(4, 0x40200000#32)]) 2 0xc0200000#32 0#32
#guard fpIs (fp1 (.absS 2#32 4#32) [(4, 0xff800123#32)] 0x0001f07c#32) 2 0x7f800123#32 0x0001f07c#32
#guard fpIs (fp1 (.negS 2#32 4#32) [(4, 0x7fc00001#32)] 0x00001004#32) 2 0xffc00001#32 0x00001004#32
-- … and keep the upper half of FPR[fd] (single) / write the whole FPR (double)
#guard fpIs64 (fp64 (.negS 2#32 4#32) [(2, 0x5555555500000000#64), (4, 0x3f800000#64)]) 2
  0x55555555bf800000#64 0#32
-- mov.s is non-arithmetic: an SNaN is copied, FCSR untouched
#guard fpIs (fp1 (.movS 2#32 4#32) [(4, 0x7f800123#32)] 0x0000f07c#32) 2 0x7f800123#32 0x0000f07c#32
-- recip / rsqrt
#guard fpIs (fp1 (.recipS 2#32 4#32) [(4, 0x40000000#32)]) 2 0x3f000000#32 0#32
#guard fpIs (fp1 (.rsqrtS 2#32 4#32) [(4, 0x40800000#32)]) 2 0x3f000000#32 0#32
#guard fpIs (fp1 (.rsqrtS 2#32 4#32) [(4, 0#32)]) 2 0x7f800000#32 0x00008020#32


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
-- invalid conversions (FCSR.NAN2008 = 1 defaults, MD00082 Vol I-A Rev 6.01 Table 6.3, p.82):
-- any NaN → 0; +∞ or too big → 0x7fffffff; −∞ or too small → 0x80000000; Invalid
#guard fpIs (fp1 (.cvtWS 2#32 4#32) [(4, 0x7fc00000#32)]) 2 0#32 0x00010040#32
#guard fpIs (fp1 (.cvtWS 2#32 4#32) [(4, 0xff800123#32)]) 2 0#32 0x00010040#32
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0xff800000#32)]) 2 0x80000000#32 0x00010040#32
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0x7f800000#32)]) 2 0x7fffffff#32 0x00010040#32
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0x4f000000#32)]) 2 0x7fffffff#32 0x00010040#32   -- 2^31
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0xdf000000#32)]) 2 0x80000000#32 0x00010040#32   -- −2^63
#guard fpIs (fp1 (.truncWS 2#32 4#32) [(4, 0xcf000000#32)]) 2 0x80000000#32 0#32            -- −2^31
-- the double forms read the whole 64-bit FPR: 2.5 = 0x4004000000000000
#guard fpIs (fp64 (.roundWD 2#32 4#32) [(4, 0x4004000000000000#64)]) 2 2#32 0x00001004#32
#guard fpIs (fp64 (.ceilWD 2#32 4#32) [(4, 0x4004000000000000#64)]) 2 3#32 0x00001004#32
#guard fpIs (fp64 (.floorWD 2#32 4#32) [(4, 0xc004000000000000#64)]) 2 0xfffffffd#32 0x00001004#32
#guard fpIs (fp64 (.truncWD 2#32 4#32) [(4, 0xc004000000000000#64)]) 2 0xfffffffe#32 0x00001004#32
#guard fpIs (fp64 (.cvtWD 2#32 4#32) [(4, 0x4004000000000000#64)] 2#32) 2 3#32 0x00001006#32
#guard fpIs (fp64 (.cvtWD 2#32 4#32) [(4, 0x7ff0000000000000#64)]) 2 0x7fffffff#32 0x00010040#32
#guard fpIs (fp64 (.cvtWD 2#32 4#32) [(4, 0x7ff8000000000000#64)]) 2 0#32 0x00010040#32
-- an odd register holds a double: $f5
#guard fpIs (fp64 (.roundWD 2#32 5#32) [(5, 0x4004000000000000#64)]) 2 2#32 0x00001004#32
-- cvt.s.w: 5 → 5.0; 2^24+1 is inexact (RN down, RP up)
#guard fpIs (fp1 (.cvtSW 2#32 4#32) [(4, 5#32)]) 2 0x40a00000#32 0#32
#guard fpIs (fp1 (.cvtSW 2#32 4#32) [(4, 16777217#32)]) 2 0x4b800000#32 0x00001004#32
#guard fpIs (fp1 (.cvtSW 2#32 4#32) [(4, 16777217#32)] 2#32) 2 0x4b800001#32 0x00001006#32
-- cvt.d.w −1 → −1.0 = 0xbff0000000000000; cvt.d.s 1.0 (the whole FPR written); cvt.s.d of
-- 1+2^−24 (a tie)
#guard fpIs64 (fp1 (.cvtDW 2#32 4#32) [(4, 0xffffffff#32)]) 2 0xbff0000000000000#64 0#32
#guard fpIs64 (fp64 (.cvtDS 2#32 4#32) [(2, 0xffffffffffffffff#64), (4, 0x3f800000#64)]) 2
  0x3ff0000000000000#64 0#32
-- cvt.d.s of a QNaN keeps sign and payload; of an SNaN quiets it with Invalid
#guard fpIs64 (fp1 (.cvtDS 2#32 4#32) [(4, 0xffc00001#32)]) 2 0xfff8000020000000#64 0#32
#guard fpIs64 (fp1 (.cvtDS 2#32 4#32) [(4, 0x7f800001#32)]) 2 0x7ff8000020000000#64 0x00010040#32
#guard fpIs (fp64 (.cvtSD 2#32 4#32) [(4, 0x3ff0000010000000#64)]) 2 0x3f800000#32 0x00001004#32
#guard fpIs (fp64 (.cvtSD 2#32 4#32) [(4, 0x3ff0000010000000#64)] 2#32) 2 0x3f800001#32
  0x00001006#32

-- #### Longword (L) conversions (MD00086 Vol II-A Rev 6.06: CVT.L.fmt p.154, ROUND.L.fmt p.341,
-- TRUNC.L.fmt p.440, CEIL.L.fmt p.127, FLOOR.L.fmt p.185, CVT.S.fmt p.159, CVT.D.fmt p.153)
-- single → longword: cvt.l follows FCSR.RM, the others their fixed direction
#guard fpIs64 (fp1 (.cvtLS 2#32 4#32) [(4, 0x40200000#32)]) 2 2#64 0x00001004#32
#guard fpIs64 (fp1 (.cvtLS 2#32 4#32) [(4, 0x40200000#32)] 2#32) 2 3#64 0x00001006#32
#guard fpIs64 (fp1 (.truncLS 2#32 4#32) [(4, 0xc0200000#32)] 3#32) 2 0xfffffffffffffffe#64 0x00001007#32
#guard fpIs64 (fp1 (.roundLS 2#32 4#32) [(4, 0x40600000#32)] 3#32) 2 4#64 0x00001007#32
#guard fpIs64 (fp1 (.ceilLS 2#32 4#32) [(4, 0x40200000#32)]) 2 3#64 0x00001004#32
#guard fpIs64 (fp1 (.floorLS 2#32 4#32) [(4, 0xc0200000#32)]) 2 0xfffffffffffffffd#64 0x00001004#32
-- 2^40 and 2^31 fit a longword exactly (2^31 does not fit a word)
#guard fpIs64 (fp1 (.cvtLS 2#32 4#32) [(4, 0x53800000#32)]) 2 0x0000010000000000#64 0#32
#guard fpIs64 (fp1 (.truncLS 2#32 4#32) [(4, 0x4f000000#32)]) 2 0x0000000080000000#64 0#32
-- invalid: NaN → 0, 2^63 / +∞ → 0x7fff…, −∞ → 0x8000…; −2^63 itself is exact
#guard fpIs64 (fp1 (.cvtLS 2#32 4#32) [(4, 0x7fc00000#32)]) 2 0#64 0x00010040#32
#guard fpIs64 (fp1 (.roundLS 2#32 4#32) [(4, 0x5f000000#32)]) 2 0x7fffffffffffffff#64 0x00010040#32
#guard fpIs64 (fp1 (.floorLS 2#32 4#32) [(4, 0xff800000#32)]) 2 0x8000000000000000#64 0x00010040#32
#guard fpIs64 (fp1 (.truncLS 2#32 4#32) [(4, 0xdf000000#32)]) 2 0x8000000000000000#64 0#32
-- FCSR.FS = 1 flushes a subnormal operand to zero first: ceil of the smallest subnormal is 1
-- with FS = 0 (Inexact) and 0 with FS = 1, Inexact signaled by the flush (MD00082 Vol I-A Rev 6.01
-- §6.7.2.4, p.102)
#guard fpIs64 (fp1 (.ceilLS 2#32 4#32) [(4, 1#32)]) 2 1#64 0x00001004#32
#guard fpIs64 (fp1 (.ceilLS 2#32 4#32) [(4, 1#32)] 0x01000000#32) 2 0#64 0x01001004#32
-- double → longword
#guard fpIs64 (fp64 (.roundLD 2#32 4#32) [(4, 0x4004000000000000#64)]) 2 2#64 0x00001004#32
#guard fpIs64 (fp64 (.ceilLD 2#32 4#32) [(4, 0x4004000000000000#64)]) 2 3#64 0x00001004#32
#guard fpIs64 (fp64 (.floorLD 2#32 4#32) [(4, 0xc004000000000000#64)]) 2 0xfffffffffffffffd#64
  0x00001004#32
#guard fpIs64 (fp64 (.truncLD 2#32 4#32) [(4, 0xc004000000000000#64)]) 2 0xfffffffffffffffe#64
  0x00001004#32
#guard fpIs64 (fp64 (.cvtLD 2#32 4#32) [(4, 0x4004000000000000#64)] 2#32) 2 3#64 0x00001006#32
#guard fpIs64 (fp64 (.cvtLD 2#32 4#32) [(4, 0xc3e0000000000000#64)]) 2 0x8000000000000000#64 0#32
#guard fpIs64 (fp64 (.ceilLD 2#32 4#32) [(4, 0x43e0000000000000#64)]) 2 0x7fffffffffffffff#64
  0x00010040#32
#guard fpIs64 (fp64 (.cvtLD 2#32 4#32) [(4, 0x7ff0000000000000#64)]) 2 0x7fffffffffffffff#64
  0x00010040#32
#guard fpIs64 (fp64 (.cvtLD 2#32 4#32) [(4, 0x7ff0000000000001#64)]) 2 0#64 0x00010040#32
-- longword → double: rounded per FCSR.RM (2^53 + 1 is inexact)
#guard fpIs64 (fp64 (.cvtDL 2#32 4#32) [(4, 0x0020000000000001#64)]) 2 0x4340000000000000#64
  0x00001004#32
#guard fpIs64 (fp64 (.cvtDL 2#32 4#32) [(4, 0x0020000000000001#64)] 2#32) 2 0x4340000000000001#64
  0x00001006#32
#guard fpIs64 (fp64 (.cvtDL 2#32 4#32) [(4, 0x8000000000000000#64)]) 2 0xc3e0000000000000#64 0#32
#guard fpIs64 (fp64 (.cvtDL 2#32 4#32) [(4, 0xffffffffffffffff#64)]) 2 0xbff0000000000000#64 0#32
-- longword → single: rounded per FCSR.RM; the upper half of FPR[fd] kept
#guard fpIs (fp64 (.cvtSL 2#32 4#32) [(4, 0x7fffffffffffffff#64)]) 2 0x5f000000#32 0x00001004#32
#guard fpIs64 (fp64 (.cvtSL 2#32 4#32) [(2, 0xaaaaaaaa00000000#64), (4, 0xffffffffffffffff#64)]) 2
  0xaaaaaaaabf800000#64 0#32
-- Invalid enabled (bit 11): cvt.l.d of a NaN traps, FPR[fd] not written
#guard fpTraps64 (fp64 (.cvtLD 2#32 4#32) [(2, 0x0000beef0000dead#64), (4, 0x7ff8000000000000#64)]
  0x00000800#32) 2 0x0000beef0000dead#64 0x00010800#32

-- #### Double-precision arithmetic (one 64-bit FPR per double)
-- 1.0 + 2.0 = 3.0 (0x4008000000000000)
#guard fpIs64 (fp64 (.addD 2#32 4#32 6#32) [(4, 0x3ff0000000000000#64), (6, 0x4000000000000000#64)]) 2
  0x4008000000000000#64 0#32
-- odd registers: $f3 ← $f5 + $f7
#guard fpIs64 (fp64 (.addD 3#32 5#32 7#32) [(5, 0x3ff0000000000000#64), (7, 0x4000000000000000#64)]) 3
  0x4008000000000000#64 0#32
-- 1.0 / 3.0 = 0x3fd5555555555555, Inexact
#guard fpIs64 (fp64 (.divD 2#32 4#32 6#32) [(4, 0x3ff0000000000000#64), (6, 0x4008000000000000#64)]) 2
  0x3fd5555555555555#64 0x00001004#32
-- sqrt.d(2) = 0x3ff6a09e667f3bcd; sqrt.d(−1) → default QNaN 0x7ff8000000000000, Invalid
#guard fpIs64 (fp64 (.sqrtD 2#32 4#32) [(4, 0x4000000000000000#64)]) 2 0x3ff6a09e667f3bcd#64
  0x00001004#32
#guard fpIs64 (fp64 (.sqrtD 2#32 4#32) [(4, 0xbff0000000000000#64)]) 2 0x7ff8000000000000#64
  0x00010040#32
-- mov.d / neg.d / abs.d: non-arithmetic, FCSR untouched
#guard fpIs64 (fp64 (.movD 2#32 4#32) [(4, 0x7ff8000089abcdef#64)] 0x7c#32) 2 0x7ff8000089abcdef#64
  0x7c#32
#guard fpIs64 (fp64 (.negD 2#32 4#32) [(4, 0x3ff0000000000001#64)]) 2 0xbff0000000000001#64 0#32
#guard fpIs64 (fp64 (.absD 2#32 4#32) [(4, 0xbff0000000000001#64)]) 2 0x3ff0000000000001#64 0#32
#guard fpIs64 (fp64 (.negD 2#32 4#32) [(4, 0x7ff0000000000001#64)] 0x0001f07c#32) 2
  0xfff0000000000001#64 0x0001f07c#32

-- (Release 6 removed MADD/MSUB/NMADD/NMSUB.fmt, C.cond.fmt, BC1F/BC1T/BC1FL/BC1TL and the
-- conditional moves MOVF/MOVT/MOVN/MOVZ(.fmt); their tests are gone. Their Release 6 replacements
-- CMP.condn.fmt, BC1EQZ/BC1NEZ, SEL/SELEQZ/SELNEZ.fmt and MADDF/MSUBF.fmt are tested below, R6-6B.)

-- #### Control registers: cfc1 / ctc1 (MD00086 Vol II-A Rev 6.06, CFC1 p.129-130, CTC1 p.149-151)
-- FIR (0) is the constant 0x00f30000 (S, D, W, L, F64, Has2008)
#guard nextRegEq (fp1 (.cfc1 9#32 0#32) []) 9 0x00f30000#32
-- FCSR (31): only the writable bits are stored; writing all ones sets Cause.E, which traps
#guard fpTraps (fp1 (.ctc1 8#32 31#32) [] 0#32 [(8, 0xffffffff#32)]) 0 0#32 0x0103ffff#32
#guard nextFcsrEq (fp1 (.ctc1 8#32 31#32) [] 0#32 [(8, 0x01000003#32)]) 0x01000003#32
-- the Release 6 FCC bits (23, 31..25) are reserved: a write ignores them
#guard nextFcsrEq (fp1 (.ctc1 8#32 31#32) [] 0#32 [(8, 0xfe800003#32)]) 0x00000003#32
-- a read of FCSR shows ABS2008 = NAN2008 = 1 (bits 19, 18)
#guard nextRegEq (fp1 (.cfc1 9#32 31#32) [] 0x01000003#32) 9 0x010c0003#32
#guard nextRegEq (fp1 (.cfc1 9#32 31#32) []) 9 0x000c0000#32
-- views of FCSR = 0x01000003: FCCR (25) = 0, FENR (28) = 7 (FS in bit 2, RM), FEXR (26) = 0
#guard nextRegEq (fp1 (.cfc1 9#32 25#32) [] 0x01000003#32 [(9, 0x55#32)]) 9 0#32
#guard nextRegEq (fp1 (.cfc1 9#32 28#32) [] 0x01000003#32) 9 7#32
#guard nextRegEq (fp1 (.cfc1 9#32 26#32) [] 0x01000003#32) 9 0#32
-- an FCCR write changes nothing (its FCC bits are reserved)
#guard nextFcsrEq (fp1 (.ctc1 8#32 25#32) [] 0x00000f83#32 [(8, 0xff#32)]) 0x00000f83#32
-- FENR write: Enables, FS (bit 2 → FCSR bit 24), RM
#guard nextFcsrEq (fp1 (.ctc1 8#32 28#32) [] 0#32 [(8, 0x00000f87#32)]) 0x01000f83#32
-- FEXR write: Cause and Flags
#guard nextFcsrEq (fp1 (.ctc1 8#32 26#32) [] 3#32 [(8, 0x0001f07c#32)]) 0x0001f07f#32
-- CheckFPException: writing a Cause bit whose Enable is set traps, register written first
#guard fpTraps (fp1 (.ctc1 8#32 26#32) [] 0x00000080#32 [(8, 0x00001000#32)]) 0 0#32 0x00001080#32
-- … and so does Cause.E (bit 17), which has no enable
#guard fpTraps (fp1 (.ctc1 8#32 31#32) [] 0#32 [(8, 0x00020000#32)]) 0 0#32 0x00020000#32
-- Release 6 traps: FIR is not writable, UFR/UNFR (1, 4) and every control register that does not
-- exist raise Reserved Instruction; FRE (5) too, read or written (no FRE with FIR.FREP = 0; W7)
#guard raises (fp1 (.ctc1 8#32 0#32) [] 0x7c#32 [(8, 0xffffffff#32)]) excCodeRI
#guard nextFcsrEq (fp1 (.ctc1 8#32 0#32) [] 0x7c#32 [(8, 0xffffffff#32)]) 0x7c#32
#guard raises (fp1 (.cfc1 9#32 7#32) [] 0x7c#32 [(9, 0x55#32)]) excCodeRI
#guard nextRegEq (fp1 (.cfc1 9#32 7#32) [] 0x7c#32 [(9, 0x55#32)]) 9 0x55#32
#guard raises (fp1 (.ctc1 8#32 7#32) [] 0x7c#32 [(8, 0xffffffff#32)]) excCodeRI
#guard raises (fp1 (.cfc1 9#32 1#32) []) excCodeRI
#guard raises (fp1 (.ctc1 8#32 4#32) []) excCodeRI
#guard raises (fp1 (.cfc1 9#32 5#32) [] 0#32 [(9, 0x55#32)]) excCodeRI
#guard nextRegEq (fp1 (.cfc1 9#32 5#32) [] 0#32 [(9, 0x55#32)]) 9 0x55#32
#guard raises (fp1 (.ctc1 8#32 5#32) []) excCodeRI

-- #### Floating Point exception (enabled exception): destination not written
-- Inexact enabled (bit 7): 1/3 traps; $f2 keeps 0xdead; Cause.I set, Flags untouched
#guard fpTraps (fp1 (.divS 2#32 4#32 6#32)
  [(2, 0xdead#32), (4, 0x3f800000#32), (6, 0x40400000#32)] 0x00000080#32) 2 0xdead#32 0x00001080#32
-- Divide-by-zero enabled (bit 10)
#guard fpTraps (fp1 (.divS 2#32 4#32 6#32)
  [(2, 0xdead#32), (4, 0x3f800000#32), (6, 0#32)] 0x00000400#32) 2 0xdead#32 0x00008400#32
-- Invalid enabled (bit 11): cvt.w.s of a NaN traps
#guard fpTraps (fp1 (.cvtWS 2#32 4#32) [(2, 0xdead#32), (4, 0x7fc00000#32)] 0x00000800#32) 2
  0xdead#32 0x00010800#32
-- … but abs.s of a NaN does not (non-arithmetic): sign cleared, FCSR unchanged
#guard fpIs (fp1 (.absS 2#32 4#32) [(2, 0xdead#32), (4, 0xffc00001#32)] 0x00000800#32) 2
  0x7fc00001#32 0x00000800#32
-- Underflow enabled (bit 8): an exact tiny result (2^−126 × 0.5) traps
#guard fpTraps (fp1 (.mulS 2#32 4#32 6#32)
  [(2, 0xdead#32), (4, 0x00800000#32), (6, 0x3f000000#32)] 0x00000100#32) 2 0xdead#32 0x00002100#32
#guard fpIs (fp1 (.mulS 2#32 4#32 6#32) [(4, 0x00800000#32), (6, 0x3f000000#32)]) 2 0x00400000#32 0#32
-- a double result is not written either
#guard (match fp64 (.divD 2#32 4#32 6#32)
          [(2, 0x0000beef0000dead#64), (4, 0x3ff0000000000000#64), (6, 0x4008000000000000#64)]
          0x00000080#32 with
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
      [(2, 0x11#32), (4, 0x3f800000#32), (6, 0x40000000#32)]) with fcsr := 0x00000003#32 }

#guard [Instruction.addS 2#32 4#32 6#32, .addD 2#32 4#32 6#32, .mfc1 9#32 4#32, .mtc1 9#32 4#32,
    .mfhc1 9#32 4#32, .mthc1 9#32 4#32, .cfc1 9#32 31#32, .ctc1 9#32 31#32,
    .lwc1 8#32 2#32 0#32, .swc1 8#32 2#32 0#32, .ldc1 8#32 2#32 0#32, .sdc1 8#32 2#32 0#32,
    .movS 2#32 4#32, .absD 2#32 4#32, .cvtWS 2#32 4#32, .cvtDW 2#32 4#32, .sqrtS 2#32 4#32,
    .recipS 2#32 4#32, .rsqrtD 2#32 4#32, .roundWD 2#32 4#32, .cvtLS 2#32 4#32, .floorLD 2#32 4#32,
    .cvtSL 2#32 4#32, .cvtDL 2#32 4#32].all
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
-- Release 6 removed COP1X (opcode 0x13) and MOVCI (SPECIAL funct 0x01): they are not in
-- coprocessor 1's encoding space any more, so they raise Reserved Instruction even when CU1 = 0
#guard raises (hstep ((∅ : Program).insert textBase 0x4c000005#32) cuState) excCodeRI
#guard raises (hstep ((∅ : Program).insert textBase 0x00020001#32) cuState) excCodeRI
#guard raises (hstep ((∅ : Program).insert textBase 0x00020001#32) regs0) excCodeRI
-- coprocessor 2 does not exist: COP2 words raise Coprocessor Unusable with CE = 2
#guard cpuRaised (hstep ((∅ : Program).insert textBase 0x48000000#32) regs0) regs0 2#32
-- the pre-Release 6 LWC2 opcode (0x32) is not COP2 space in Release 6: it is BC (BC p.53), so
-- `0xc8000000` (BC with offset 0) goes to the next instruction and raises nothing
#guard (match hstep ((∅ : Program).insert textBase 0xc8000000#32) regs0 with
        | .next s => s.pc == textBase + 4#32 && s.pendingBranch.isNone && causeExcCode s == causeExcCode regs0
        | .halt _ => false)
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
      -- physical: data VA 0x1001_xxxx is PA 0x5001_xxxx (kuseg + 1 GB while ERL = 0)
      physMem := (((∅ : Std.HashMap W32 UInt8).insert 0x50010004#32 0x00).insert 0x50010005#32 0x00)
               |>.insert 0x50010006#32 0x80 |>.insert 0x50010007#32 0x3f }  -- 1.0 at offset 4 (LE)
#guard nextFpRegEq (hstep (prog1 (.lwc1 8#32 9#32 4#32)) fpMemTestState) 9 0x3f800000#32
-- lwc1 writes the low word, keeping the upper half of the 64-bit FPR (model pin); swc1 stores the low word
#guard nextFpReg64Eq (hstep (prog1 (.lwc1 8#32 9#32 4#32))
  (setFpRegs64 fpMemTestState [(9, 0xaaaaaaaabbbbbbbb#64)])) 9 0xaaaaaaaa3f800000#64
#guard (stepState (prog1 (.swc1 8#32 9#32 4#32))
          (setFpRegs64 (setRegs regs0 [(8, 0x10010000#32)]) [(9, 0x123456783f800000#64)])).bind
        (fun s' => readMemWord s' 0x10010004#32) = some 0x3f800000#32
#guard (stepState (prog1 (.swc1 8#32 9#32 4#32))
          (setFpRegs (setRegs regs0 [(8, 0x10010000#32)]) [(9, 0x3f800000#32)])).bind
        (fun s' => readMemWord s' 0x10010004#32) = some 0x3f800000#32
#guard raisesAddr (hstep (prog1 (.lwc1 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)]))
  excCodeAdEL 0x10010001#32

-- ldc1/sdc1: little-endian doubleword (low word at the lower address) in one 64-bit FPR,
-- doubleword-aligned
private def dpMemTestState : State :=
  { (setRegs regs0 [(8, 0x10010000#32), (9, 8#32)]) with
      -- physical: data VA 0x1001_xxxx is PA 0x5001_xxxx (kuseg + 1 GB while ERL = 0)
      physMem := ((((∅ : Std.HashMap W32 UInt8).insert 0x5001000f#32 0x3f).insert 0x5001000e#32 0xf0)
               |>.insert 0x50010008#32 0x01) }  -- 0x3ff0000000000001 at offset 8 (LE)
#guard (match hstep (prog1 (.ldc1 8#32 2#32 8#32)) dpMemTestState with
        | .next s => readFpD s 2#32 == 0x3ff0000000000001#64 && readFpReg64 s 3 == 0#64
        | .halt _ => false)
-- an odd register: ldc1 $f3 loads the whole doubleword into FPR[3], FPR[2] and FPR[4] untouched
#guard (match hstep (prog1 (.ldc1 8#32 3#32 8#32))
          (setFpRegs64 dpMemTestState [(2, 0x2222#64), (4, 0x4444#64)]) with
        | .next s => readFpReg64 s 3 == 0x3ff0000000000001#64 && readFpReg64 s 2 == 0x2222#64 &&
            readFpReg64 s 4 == 0x4444#64
        | .halt _ => false)
#guard (stepState (prog1 (.sdc1 8#32 2#32 16#32))
          (setFpRegs64 (setRegs regs0 [(8, 0x10010000#32)]) [(2, 0x0123456789abcdef#64)])).bind
        (fun s' => (readMemWord s' 0x10010010#32).bind fun lo =>
          (readMemWord s' 0x10010014#32).map fun hi => (lo, hi))
      = some (0x89abcdef#32, 0x01234567#32)
-- sdc1 from an odd register
#guard (stepState (prog1 (.sdc1 8#32 5#32 16#32))
          (setFpRegs64 (setRegs regs0 [(8, 0x10010000#32)]) [(4, 0x1111#64), (5, 0xfedcba9876543210#64)])).bind
        (fun s' => (readMemWord s' 0x10010010#32).bind fun lo =>
          (readMemWord s' 0x10010014#32).map fun hi => (lo, hi))
      = some (0x76543210#32, 0xfedcba98#32)
-- word-aligned but not doubleword-aligned: Address Error
#guard raisesAddr (hstep (prog1 (.ldc1 8#32 2#32 4#32)) dpMemTestState) excCodeAdEL 0x10010004#32
#guard raisesAddr (hstep (prog1 (.sdc1 8#32 2#32 4#32)) dpMemTestState) excCodeAdES 0x10010004#32
-- a store clears LLbit; a failed (misaligned) one does not get that far
#guard nextLlBitEq (hstep (prog1 (.sdc1 8#32 2#32 8#32)) { dpMemTestState with llBit := true }) false

-- #### The Release 6 FP instructions (MD00086 Vol II-A Rev 6.06)
-- CMP.condn.fmt (p.136-140): a mask of all ones / all zeros; the upper half of a .S result kept
#guard fpIs (fp1 (.cmpS 4#32 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40000000#32)]) 2 0xffffffff#32 0#32
#guard fpIs (fp1 (.cmpS 4#32 2#32 4#32 6#32) [(4, 0x40000000#32), (6, 0x3f800000#32)]) 2 0#32 0#32
#guard fpIs64 (fp64 (.cmpS 4#32 2#32 4#32 6#32) [(2, 0x1234567800000000#64), (4, 0x3f800000#64),
  (6, 0x40000000#64)]) 2 0x12345678ffffffff#64 0#32
-- EQ ignores the sign of zero; NE (condn 19) is its negation
#guard fpIs (fp1 (.cmpS 2#32 2#32 4#32 6#32) [(4, 0x80000000#32), (6, 0#32)]) 2 0xffffffff#32 0#32
#guard fpIs (fp1 (.cmpS 19#32 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x40000000#32)]) 2 0xffffffff#32 0#32
-- a quiet NaN: UN true, quiet EQ false, no exception; the signalling SEQ (condn 10) raises Invalid
#guard fpIs (fp1 (.cmpS 1#32 2#32 4#32 6#32) [(4, 0x7fc00000#32), (6, 0x3f800000#32)]) 2 0xffffffff#32 0#32
#guard fpIs (fp1 (.cmpS 2#32 2#32 4#32 6#32) [(4, 0x7fc00000#32), (6, 0x3f800000#32)]) 2 0#32 0#32
#guard fpIs (fp1 (.cmpS 10#32 2#32 4#32 6#32) [(4, 0x7fc00000#32), (6, 0x3f800000#32)]) 2 0#32 0x00010040#32
-- OR (condn 17) of a QNaN is false; an SNaN raises Invalid even for a quiet predicate
#guard fpIs (fp1 (.cmpS 17#32 2#32 4#32 6#32) [(4, 0x7fc00000#32), (6, 0x3f800000#32)]) 2 0#32 0#32
#guard fpIs (fp1 (.cmpS 3#32 2#32 4#32 6#32) [(4, 0x7f800001#32), (6, 0x3f800000#32)]) 2 0xffffffff#32
  0x00010040#32
-- Invalid enabled: trap, `fd` not written
#guard fpTraps (fp1 (.cmpS 10#32 2#32 4#32 6#32) [(2, 7#32), (4, 0x7fc00000#32), (6, 0x3f800000#32)]
  0x800#32) 2 7#32 0x00010800#32
#guard fpIs64 (fp64 (.cmpD 6#32 2#32 4#32 6#32) [(4, 0x3ff0000000000000#64), (6, 0x3ff0000000000000#64)]) 2
  0xffffffffffffffff#64 0#32
#guard fpIs64 (fp64 (.cmpD 4#32 2#32 4#32 6#32) [(4, 0x3ff0000000000000#64), (6, 0x3ff0000000000000#64)]) 2
  0#64 0#32
-- BC1EQZ/BC1NEZ (p.54-55): a delay-slot branch on bit 0 of FPR[ft]
#guard nextPendingEq (fp1 (.bc1eqz 3#32 2#32) [(3, 0xfffffffe#32)]) (some (textBase + 12#32))
#guard nextPendingEq (fp1 (.bc1eqz 3#32 2#32) [(3, 1#32)]) (some (textBase + 8#32))
#guard nextPendingEq (fp1 (.bc1nez 3#32 2#32) [(3, 1#32)]) (some (textBase + 12#32))
#guard nextPendingEq (fp1 (.bc1nez 3#32 0xffff#32) [(3, 0xffffffff#32)]) (some textBase)
#guard nextPcEq (fp1 (.bc1nez 3#32 2#32) [(3, 0#32)]) (textBase + 4#32)
-- a CTI in its delay slot: Reserved Instruction in the delay slot; it is one in a delay slot too
#guard (match stepState (buildProg textBase [.bc1eqz 3#32 1#32, .beq 0#32 0#32 0#32]) regs0 with
        | some s1 => isRiInDelaySlot (hstep (buildProg textBase [.bc1eqz 3#32 1#32, .beq 0#32 0#32 0#32]) s1)
        | none => false)
#guard (match stepState (buildProg textBase [.beq 0#32 0#32 1#32, .bc1nez 3#32 0#32]) regs0 with
        | some s1 => isRiInDelaySlot (hstep (buildProg textBase [.beq 0#32 0#32 1#32, .bc1nez 3#32 0#32]) s1)
        | none => false)
-- SEL/SELEQZ/SELNEZ (p.368, p.371): FCSR untouched
#guard fpIs (fp1 (.selS 2#32 4#32 6#32) [(2, 1#32), (4, 0x11#32), (6, 0x22#32)] 0x7c#32) 2 0x22#32 0x7c#32
#guard fpIs (fp1 (.selS 2#32 4#32 6#32) [(2, 2#32), (4, 0x11#32), (6, 0x22#32)]) 2 0x11#32 0#32
#guard fpIs64 (fp64 (.selD 2#32 4#32 6#32) [(2, 0xffffffff00000001#64), (4, 1#64), (6, 0x7ff0000000000001#64)])
  2 0x7ff0000000000001#64 0#32
#guard fpIs (fp1 (.seleqzS 2#32 4#32 6#32) [(4, 0x7f800001#32), (6, 0#32)]) 2 0x7f800001#32 0#32
#guard fpIs (fp1 (.seleqzS 2#32 4#32 6#32) [(4, 0x7f800001#32), (6, 3#32)]) 2 0#32 0#32
#guard fpIs64 (fp64 (.seleqzD 2#32 4#32 6#32) [(4, 5#64), (6, 0x100000001#64)]) 2 0#64 0#32
#guard fpIs (fp1 (.selnezS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 1#32)]) 2 0x3f800000#32 0#32
#guard fpIs64 (fp64 (.selnezD 2#32 4#32 6#32) [(4, 5#64), (6, 0x100000000#64)]) 2 0#64 0#32
-- MADDF/MSUBF (p.259): fd ± fs × ft with one rounding
#guard fpIs (fp1 (.maddfS 2#32 4#32 6#32) [(2, 0x3f800000#32), (4, 0x40000000#32), (6, 0x40400000#32)])
  2 0x40e00000#32 0#32
#guard fpIs64 (fp64 (.msubfD 2#32 4#32 6#32) [(2, 0x3ff0000000000000#64), (4, 0x4000000000000000#64),
  (6, 0x4008000000000000#64)]) 2 0xc014000000000000#64 0#32
-- fused: (1 + 2^-22) − (1 + 2^-23)² = −2^-46 exactly (an unfused product would round to 1 + 2^-22,
-- giving 0)
#guard fpIs (fp1 (.msubfS 2#32 4#32 6#32) [(2, 0x3f800002#32), (4, 0x3f800001#32), (6, 0x3f800001#32)])
  2 0xa8800000#32 0#32
-- MAX/MIN/MAXA/MINA (p.262-265): a number beats a NaN; ±0 ordered; magnitudes
#guard fpIs (fp1 (.maxS 2#32 4#32 6#32) [(4, 0x7fc00000#32), (6, 0x3f800000#32)]) 2 0x3f800000#32 0#32
#guard fpIs (fp1 (.minS 2#32 4#32 6#32) [(4, 0x3f800000#32), (6, 0x7fc00000#32)]) 2 0x3f800000#32 0#32
#guard fpIs (fp1 (.maxS 2#32 4#32 6#32) [(4, 0x80000000#32), (6, 0#32)]) 2 0#32 0#32
#guard fpIs (fp1 (.minS 2#32 4#32 6#32) [(4, 0#32), (6, 0x80000000#32)]) 2 0x80000000#32 0#32
#guard fpIs (fp1 (.maxaS 2#32 4#32 6#32) [(4, 0xc0400000#32), (6, 0x40000000#32)]) 2 0xc0400000#32 0#32
#guard fpIs (fp1 (.minaS 2#32 4#32 6#32) [(4, 0xc0400000#32), (6, 0x40000000#32)]) 2 0x40000000#32 0#32
#guard fpIs (fp1 (.minS 2#32 4#32 6#32) [(4, 0x7f800001#32), (6, 0x3f800000#32)]) 2 0x3f800000#32
  0x00010040#32
#guard fpIs64 (fp64 (.maxD 2#32 4#32 6#32) [(4, 0x7ff8000000000001#64), (6, 0x7ff8000000000002#64)]) 2
  0x7ff8000000000001#64 0#32
#guard fpIs64 (fp64 (.minaD 2#32 4#32 6#32) [(4, 0xbff0000000000000#64), (6, 0x3ff0000000000000#64)]) 2
  0xbff0000000000000#64 0#32
#guard fpIs64 (fp64 (.maxaD 2#32 4#32 6#32) [(4, 0xbff0000000000000#64), (6, 0x3ff0000000000000#64)]) 2
  0x3ff0000000000000#64 0#32
#guard fpIs64 (fp64 (.minD 2#32 4#32 6#32) [(4, 0xbff0000000000000#64), (6, 0x3ff0000000000000#64)]) 2
  0xbff0000000000000#64 0#32
-- CLASS (p.132): the 10-bit mask, FCSR untouched
#guard fpIs (fp1 (.classS 2#32 4#32) [(4, 0x7f800000#32)] 0x7c#32) 2 0x40#32 0x7c#32
#guard fpIs (fp1 (.classS 2#32 4#32) [(4, 0x7f800001#32)]) 2 1#32 0#32
#guard fpIs (fp1 (.classS 2#32 4#32) [(4, 0x80000001#32)]) 2 0x10#32 0#32
#guard fpIs64 (fp64 (.classD 2#32 4#32) [(4, 0x8000000000000000#64)]) 2 0x20#64 0#32
#guard fpIs64 (fp64 (.classD 2#32 4#32) [(4, 0x3ff0000000000000#64)]) 2 0x80#64 0#32
-- RINT (p.337): round to integral in FCSR.RM, Inexact when it changes the value
#guard fpIs (fp1 (.rintS 2#32 4#32) [(4, 0x40200000#32)]) 2 0x40000000#32 0x00001004#32
#guard fpIs (fp1 (.rintS 2#32 4#32) [(4, 0x40200000#32)] 2#32) 2 0x40400000#32 0x00001006#32
#guard fpIs (fp1 (.rintS 2#32 4#32) [(4, 0x40400000#32)]) 2 0x40400000#32 0#32
#guard fpIs64 (fp64 (.rintD 2#32 4#32) [(4, 0xc004000000000000#64)] 3#32) 2 0xc008000000000000#64
  0x00001007#32
