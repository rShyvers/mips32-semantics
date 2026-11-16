import Semantics.Refine.Abs
import Semantics.Env
import Semantics.Manual.Decode

/-!
# ManualTests — the independent manual spec, run on concrete states

`Manual.InstructionTime modelImpl modelOracle decode` on small programs, checked against the
expected architectural effect and against `abs (step s)` (the harness in `EquivHarness` does the
same over every corpus and oracle program). `decode` is the model's decoder, used here only as the
decoder argument of the spec (`Manual.DecoderSound`).

The fixtures are local (`ManualTest`), so these tests depend on the model and the spec only.
-/

namespace ManualTest

/-- The state the programs start in: `pc = textBase`, Kernel Mode, `Status.CU1 = 1`. -/
def regs0 : State := initialState textBase

def setRegs (s : State) (kvs : List (Fin 32 × W32)) : State :=
  kvs.foldl (fun acc kv => writeReg acc kv.1 kv.2) s

def setFpRegs (s : State) (kvs : List (Fin 32 × W32)) : State :=
  kvs.foldl (fun acc kv => writeFpReg acc kv.1 kv.2) s

/-- A program of one instruction at `textBase`. -/
def prog1 (instr : Instruction) : Program :=
  (∅ : Program).insert textBase (encode instr)

/-- `s` with the word `v` stored at the virtual address `va` (the model's store, `writeMemWord`). -/
def withWord (s : State) (va v : W32) : State := (writeMemWord s va v).getD s

end ManualTest

open Manual Refine ManualTest

/-- One instruction time of the spec from the model state `s`. -/
def specTime (s : State) : Option Arch := InstructionTime modelImpl modelOracle decode (abs s)

/-- The fields the tests compare. -/
def archKey (a : Arch) : List W32 :=
  [a.PC, a.GPR 8, a.GPR 9, a.GPR 10, a.GPR 31, a.Cause, a.EPC, a.Status, a.Count, a.FCSR,
   (a.FPR 0).extractLsb' 0 32, (a.FPR 0).extractLsb' 32 32, (a.FPR 4).extractLsb' 0 32,
   (a.FPR 4).extractLsb' 32 32]

/-- Spec and model agree on the compared fields. -/
def agree (s : State) : Bool :=
  match specTime s with
  | some a => archKey a == archKey (abs (step s)) && a.BranchDelay == (step s).pendingBranch &&
      a.LowPower == (step s).standby && a.LLbit == (step s).llBit
  | none => false

/-- The `ExcCode` of the spec's `Cause` after one instruction time. -/
def specExc (s : State) : Option W32 := (specTime s).map fun (a : Arch) => (a.Cause >>> 2) &&& 0x1F#32

-- ADD without overflow, and with overflow (Integer Overflow, ExcCode 12, EPC = the add).
#guard agree (loadImage (prog1 (.add 8#32 9#32 10#32)) (setRegs regs0 [(8, 3#32), (9, 4#32)]))
#guard agree (loadImage (prog1 (.add 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x7fffffff#32), (9, 1#32)]))
#guard (match specTime (loadImage (prog1 (.add 8#32 9#32 10#32))
          (setRegs regs0 [(8, 0x7fffffff#32), (9, 1#32)])) with
        | some a => (a.Cause >>> 2) &&& 0x1F#32 == 12#32 && a.EPC == textBase
        | none => false)
-- LW misaligned: Address Error (load), BadVAddr = the address.
#guard agree (loadImage (prog1 (.lw 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32)]))
-- ADD.S with Status.CU1 = 0: Coprocessor Unusable, CE = 1.
#guard agree (loadImage (prog1 (.addS 0#32 2#32 4#32)) { regs0 with cp0Status := 0#32 })
-- MTC0 to Compare clears the timer interrupt.
#guard agree (loadImage (prog1 (.mtc0 8#32 11#32 0#32)) { setRegs regs0 [(8, 77#32)] with cp0TimerInt := true })

/-! ## 7R review regressions (the reproducers of the independent review) -/

/-- An FP state for the spec: `FPR`s, `FCSR`; `Status.CU1` as in `regs0`. -/
def fpState (instr : Instruction) (fprs : List (Fin 32 × W32)) (fcsr : W32 := 0#32) : State :=
  loadImage (prog1 instr) { setFpRegs regs0 fprs with fcsr := fcsr }

/-- The spec's 64-bit `FPR[i]` and `FCSR` after one instruction time. -/
def specFp (s : State) (i : Fin 32) : Option (BitVec 64 × W32) :=
  (specTime s).map fun a => (a.FPR i, a.FCSR)

-- (3) NEG.S / ABS.S of a NaN with the sign set: Release 6 `ABS2008 = 1`, non-arithmetic (only the
-- sign bit changes, FCSR not modified; MD00086 Vol II-A Rev 6.06, ABS.fmt p.32, NEG.fmt p.307). The
-- upper half of `FPR[fd]` is kept (the `fprUpper` pin).
#guard specFp (fpState (.negS 4#32 2#32) [(2, 0xff800001#32)]) 4 = some (0x7f800001#64, 0#32)
#guard specFp (fpState (.absS 4#32 2#32) [(2, 0xff800001#32)] 0x00001004#32) 4 =
  some (0x7f800001#64, 0x00001004#32)
#guard agree (fpState (.negS 4#32 2#32) [(2, 0xff800001#32)])
#guard agree (fpState (.absS 4#32 2#32) [(2, 0xff800001#32)] 0x00001004#32)
-- (5) JALR.HB with `rd = 0` (the Release 6 JR.HB, JR p.207): the hint-16 word jumps; hint 1 is
-- UNPREDICTABLE: RI.
#guard agree (loadImage (prog1 (.jalrHb 8#32 0#32)) (setRegs regs0 [(8, 0x00400100#32)]))
#guard (match specTime (loadImage (prog1 (.jalrHb 8#32 0#32)) (setRegs regs0 [(8, 0x00400100#32)])) with
        | some a => a.BranchDelay == some 0x00400100#32
        | none => false)
#guard UnpredictableEncoding 0x01000049#32 && !UnpredictableEncoding 0x01000409#32 &&
  !UnpredictableEncoding 0x01000009#32
-- (6) EXT with lsb + msbd > 31, CLZ with rt != 0, ADD with a nonzero shamt: UNPREDICTABLE encodings
-- (review r3; CLZ in its Release 6 diagram, `rt = 00000`, `sa = 00001`, CLZ p.135).
#guard UnpredictableEncoding 0x7D099D00#32 && UnpredictableEncoding 0x00010050#32 &&
  UnpredictableEncoding 0x00000060#32 && !UnpredictableEncoding 0x00000020#32
#guard (decode 0x7D099D00#32).isNone

/-- `DecoderSound decode` on one word: whatever `decode` returns has the word as its diagram. -/
def soundAt (w : W32) : Bool :=
  match decode w with
  | some i => enc i == some w
  | none => true

-- `DecoderSound decode`, checked (not proved) on 2^18 words spread over the whole word space, and on
-- every opcode/function combination with all variable fields zero and all ones.
#guard (List.range 262144).all fun k => soundAt (BitVec.ofNat 32 (k * 2654435761 + 12345))
#guard (List.range 64).all fun op => (List.range 64).all fun fn =>
  soundAt (BitVec.ofNat 32 (op * 2^26 + fn)) && soundAt (BitVec.ofNat 32 (op * 2^26 + 0x03FFFFC0 + fn)) &&
    soundAt (BitVec.ofNat 32 (op * 2^26 + 0x00000400 + fn))

-- 7C S3: a `j`/`jal` built by hand with `target` bits above the 26-bit `instr_index` (MD00086 Vol II-A
-- Rev 6.06, J p.194, JAL p.195): spec and model use only its low 26 bits (model fix in 7C S3).
#guard (match Execute { impl := modelImpl, oracle := modelOracle } 0#32 (.j 0xFFFFFFFF#32) (abs regs0) with
        | some a => a.BranchDelay == (execInstr regs0 (.j 0xFFFFFFFF#32)).pendingBranch &&
            a.BranchDelay == some (((regs0.pc + 4#32) &&& 0xF0000000#32) ||| 0x0FFFFFFC#32)
        | none => false)
#guard (match Execute { impl := modelImpl, oracle := modelOracle } 0#32 (.jal 0x0C000001#32) (abs regs0) with
        | some a => a.BranchDelay == (execInstr regs0 (.jal 0x0C000001#32)).pendingBranch &&
            a.BranchDelay == some (((regs0.pc + 4#32) &&& 0xF0000000#32) ||| 0x4#32)
        | none => false)
-- end 7C S3
-- 7C S4b: begin
/-- The spec's `Execute` of the instruction `i` (fetched as its own diagram) against the model's
`execInstr`, on the compared fields. -/
def execAgree (i : Instruction) (s : State) : Bool :=
  match enc i with
  | some w =>
    match Execute { impl := modelImpl, oracle := modelOracle } w i (abs s) with
    | some a => archKey a == archKey (abs (execInstr s i)) && a.LowPower == (execInstr s i).standby
    | none => false
  | none => false

-- CTC1 to `UFR` (`fs = 1`): Release 6 traps with Reserved Instruction (ExcCode 10), FCSR unchanged
-- (MD00086 Vol II-A Rev 6.06, CTC1 p.149-150: "Release 6 traps"; 7C S4b had the pre-Release 6
-- `CheckFPException()` after the UNPREDICTABLE arm).
#guard agree (fpState (.ctc1 8#32 1#32) [] 0x00010800#32)
#guard (match specTime (fpState (.ctc1 8#32 1#32) [] 0x00010800#32) with
        | some a => (a.Cause >>> 2) &&& 0x1F#32 == 10#32 && a.EPC == textBase && a.FCSR == 0x00010800#32
        | none => false)
#guard ((step (fpState (.ctc1 8#32 1#32) [] 0x00010800#32)).cp0Cause >>> 2) &&& 0x1F#32 == 10#32
-- 7C S4b: end

/-! ## Wave R6-1: the Release 6 instructions and encodings, little-endian memory -/

-- AUI (p.47): `GPR[rt] ← GPR[rs] + sign_extend(immediate << 16)`; LUI is AUI with `rs = 0`.
#guard agree (loadImage (prog1 (.aui 8#32 9#32 0x1234#32)) (setRegs regs0 [(8, 0x00005678#32)]))
#guard (specTime (loadImage (prog1 (.aui 8#32 9#32 0x8001#32)) (setRegs regs0 [(8, 1#32)]))).map
  (·.GPR 9) == some 0x80010001#32
#guard (specTime (loadImage (prog1 (.aui 0#32 9#32 0x1234#32)) regs0)).map (·.GPR 9) == some 0x12340000#32
-- NAL (p.306): `GPR[31] ← PC + 8`, a not-taken branch with a delay slot.
#guard agree (loadImage (prog1 (.nal 0x7#32)) regs0)
#guard (match specTime (loadImage (prog1 (.nal 0x7#32)) regs0) with
        | some a => a.GPR 31 == textBase + 8#32 && a.PC == textBase + 4#32 &&
            a.BranchDelay == some (textBase + 8#32)
        | none => false)
-- BAL (p.50): link and jump to `PC + 4 + offset × 4`.
#guard agree (loadImage (prog1 (.bal 0x10#32)) regs0)
#guard (match specTime (loadImage (prog1 (.bal 0x10#32)) regs0) with
        | some a => a.GPR 31 == textBase + 8#32 && a.BranchDelay == some (textBase + 4#32 + 0x40#32)
        | none => false)
-- PAUSE (p.317) with LLbit = 1: EPC ← PC + 4 and the lower power mode (pin); with LLbit = 0 a no-op.
#guard agree (loadImage (prog1 .pause) { regs0 with llBit := true })
#guard (match specTime (loadImage (prog1 .pause) { regs0 with llBit := true }) with
        | some a => a.LowPower && a.EPC == textBase + 4#32 && a.PC == textBase + 4#32
        | none => false)
#guard agree (loadImage (prog1 .pause) regs0)
#guard (specTime (loadImage (prog1 .pause) regs0)).map (·.LowPower) == some false
-- PAUSE is a CTI: in a delay slot Reserved Instruction (ExcCode 10), EPC = the branch, BD = 1.
#guard execAgree .pause { regs0 with pendingBranch := some 0x00400100#32, llBit := true }
#guard (match Execute { impl := modelImpl, oracle := modelOracle } 0x140#32 .pause
          (abs { regs0 with pendingBranch := some 0x00400100#32 }) with
        | some a => (a.Cause >>> 2) &&& 0x1F#32 == 10#32 && a.EPC == textBase - 4#32 && a.Cause.getLsbD 31
        | none => false)
-- NAL in a delay slot: Reserved Instruction as well.
#guard execAgree (.nal 0#32) { regs0 with pendingBranch := some 0x00400100#32 }
-- RDHWR with `sel` (p.332-333): `sel = 0` reads `CC` = Count; `sel ≠ 0` is Reserved Instruction.
#guard agree (loadImage (prog1 (.rdhwr 9#32 2#32 0#32)) { regs0 with cp0Count := 1234#32 })
#guard (specTime (loadImage (prog1 (.rdhwr 9#32 2#32 0#32)) { regs0 with cp0Count := 1234#32 })).map
  (·.GPR 9) == some 1234#32
#guard agree (loadImage (prog1 (.rdhwr 9#32 2#32 1#32)) regs0)
#guard specExc (loadImage (prog1 (.rdhwr 9#32 2#32 1#32)) regs0) == some 10#32
-- LL / SC / PREF with the 9-bit offset (LL p.223, SC p.347, PREF p.321): offset 0x1FC is -4.
#guard agree (loadImage (prog1 (.ll 8#32 9#32 0x1FC#32))
  (withWord (setRegs regs0 [(8, 0x10010004#32)]) 0x10010000#32 0xCAFEF00D#32))
#guard (match specTime (loadImage (prog1 (.ll 8#32 9#32 0x1FC#32))
          (withWord (setRegs regs0 [(8, 0x10010004#32)]) 0x10010000#32 0xCAFEF00D#32)) with
        | some a => a.GPR 9 == 0xCAFEF00D#32 && a.LLbit && a.LLAddr == 0x10010000#32
        | none => false)
#guard agree (loadImage (prog1 (.sc 8#32 9#32 0x1FC#32))
  { setRegs regs0 [(8, 0x10010004#32), (9, 7#32)] with llBit := true, llAddr := 0x10010000#32 })
#guard agree (loadImage (prog1 (.pref 8#32 1#32 0x1FC#32)) (setRegs regs0 [(8, 0x10010004#32)]))
-- CLO / CLZ in their Release 6 SPECIAL encodings (p.134, p.135).
#guard agree (loadImage (prog1 (.clz 8#32 9#32)) (setRegs regs0 [(8, 0x00010000#32)]))
#guard agree (loadImage (prog1 (.clo 8#32 9#32)) (setRegs regs0 [(8, 0xFF000000#32)]))
-- Little-endian memory (`BigEndianMem = 0`): the byte at the word's address is its least significant.
#guard (specTime (loadImage (prog1 (.lb 8#32 9#32 0#32))
  (withWord (setRegs regs0 [(8, 0x10010000#32)]) 0x10010000#32 0x112233C4#32))).map (·.GPR 9) ==
  some 0xFFFFFFC4#32
#guard (specTime (loadImage (prog1 (.lbu 8#32 9#32 3#32))
  (withWord (setRegs regs0 [(8, 0x10010000#32)]) 0x10010000#32 0x112233C4#32))).map (·.GPR 9) ==
  some 0x11#32
#guard (specTime (loadImage (prog1 (.lhu 8#32 9#32 2#32))
  (withWord (setRegs regs0 [(8, 0x10010000#32)]) 0x10010000#32 0x112233C4#32))).map (·.GPR 9) ==
  some 0x1122#32
#guard agree (loadImage (prog1 (.lh 8#32 9#32 0#32))
  (withWord (setRegs regs0 [(8, 0x10010000#32)]) 0x10010000#32 0x1122B3C4#32))
-- SB/SH/SW: the stored bytes in little-endian order at the physical address (kuseg + 1 GB).
#guard (match specTime (loadImage (prog1 (.sw 8#32 9#32 0#32))
          (setRegs regs0 [(8, 0x10010000#32), (9, 0x11223344#32)])) with
        | some a => a.Mem 0x50010000#32 == 0x44 && a.Mem 0x50010003#32 == 0x11
        | none => false)
#guard (match specTime (loadImage (prog1 (.sh 8#32 9#32 2#32))
          (setRegs regs0 [(8, 0x10010000#32), (9, 0x11223344#32)])) with
        | some a => a.Mem 0x50010002#32 == 0x44 && a.Mem 0x50010003#32 == 0x33
        | none => false)
#guard agree (loadImage (prog1 (.sb 8#32 9#32 1#32)) (setRegs regs0 [(8, 0x10010000#32), (9, 0xAB#32)]))
-- LDC1 / SDC1: the word at the effective address is the low word of the 64-bit `FPR[ft]` (LDC1 p.215).
#guard (match specTime (loadImage (prog1 (.ldc1 8#32 2#32 0#32))
          (withWord (withWord (setRegs regs0 [(8, 0x10010000#32)]) 0x10010000#32 0x11111111#32)
            0x10010004#32 0x22222222#32)) with
        | some a => a.FPR 2 == 0x2222222211111111#64 && a.FPR 3 == 0#64
        | none => false)
#guard agree (loadImage (prog1 (.ldc1 8#32 2#32 0#32))
  (withWord (withWord (setRegs regs0 [(8, 0x10010000#32)]) 0x10010000#32 0x11111111#32)
    0x10010004#32 0x22222222#32))
#guard (match specTime (loadImage (prog1 (.sdc1 8#32 2#32 0#32))
          (writeFpReg64 (setRegs regs0 [(8, 0x10010000#32)]) 2 0x2222222211111111#64)) with
        | some a => a.Mem 0x50010000#32 == 0x11 && a.Mem 0x50010004#32 == 0x22
        | none => false)
-- The 64-bit FPU against the spec: L conversions, MTHC1/MFHC1, CVT.D.S
#guard agree (fpState (.cvtLS 4#32 2#32) [(2, 0x40200000#32)])
#guard agree (fpState (.cvtLS 4#32 2#32) [(2, 0x7fc00000#32)])
#guard agree (fpState (.truncLS 4#32 2#32) [(2, 0xc0200000#32)] 3#32)
#guard agree (fpState (.floorLD 4#32 2#32) [(2, 0#32)])
#guard agree (loadImage (prog1 (.cvtLD 4#32 2#32))
  { writeFpReg64 regs0 2 0x43e0000000000000#64 with fcsr := 0#32 })
#guard agree (loadImage (prog1 (.cvtDL 4#32 2#32))
  { writeFpReg64 regs0 2 0x0020000000000001#64 with fcsr := 2#32 })
#guard agree (loadImage (prog1 (.cvtSL 4#32 2#32))
  { writeFpReg64 (writeFpReg64 regs0 2 0x7fffffffffffffff#64) 4 0xaaaaaaaa00000000#64 with fcsr := 0#32 })
#guard specFp (loadImage (prog1 (.cvtLD 4#32 2#32)) (writeFpReg64 regs0 2 0x4004000000000000#64)) 4 =
  some (2#64, 0x00001004#32)
#guard agree (loadImage (prog1 (.mthc1 8#32 4#32)) (setRegs (writeFpReg64 regs0 4 0x11111111#64) [(8, 0xabcdef01#32)]))
#guard agree (loadImage (prog1 (.mfhc1 8#32 4#32)) (writeFpReg64 regs0 4 0x0123456789abcdef#64))
#guard agree (fpState (.cvtDS 4#32 2#32) [(2, 0x7f800001#32)])
#guard agree (fpState (.addS 4#32 2#32 0#32) [(2, 0x7f800001#32), (0, 0x3f800000#32)])
-- The Release 6 FP instructions against the spec (incl. the trap of CMP's Invalid and
-- the words Manual.Decode reads)
#guard agree (fpState (.cmpS 4#32 4#32 2#32 0#32) [(2, 0x3f800000#32), (0, 0x40000000#32)])
#guard agree (fpState (.cmpS 10#32 4#32 2#32 0#32) [(2, 0x7fc00000#32), (0, 0x40000000#32)])
#guard agree (fpState (.cmpS 10#32 4#32 2#32 0#32) [(2, 0x7fc00000#32), (0, 0x40000000#32)] 0x800#32)
#guard agree (fpState (.cmpS 19#32 4#32 2#32 0#32) [(2, 0x80000000#32), (0, 0#32)])
#guard agree (fpState (.cmpD 27#32 4#32 2#32 0#32) [(2, 0x7f800001#32), (0, 0#32)])
#guard agree (fpState (.bc1eqz 2#32 3#32) [(2, 0#32)])
#guard agree (fpState (.bc1nez 2#32 3#32) [(2, 0#32)])
#guard agree (fpState (.selS 4#32 2#32 0#32) [(4, 1#32), (2, 5#32), (0, 7#32)])
#guard agree (fpState (.seleqzD 4#32 2#32 0#32) [(2, 5#32), (0, 1#32)])
#guard agree (fpState (.selnezS 4#32 2#32 0#32) [(2, 5#32), (0, 1#32)] 0x7c#32)
#guard agree (fpState (.maddfS 4#32 2#32 0#32) [(4, 0x3f800000#32), (2, 0x40000000#32), (0, 0x40400000#32)])
#guard agree (fpState (.msubfD 4#32 2#32 0#32) [(4, 0#32), (2, 0x7f800000#32), (0, 0#32)])
#guard agree (fpState (.maxS 4#32 2#32 0#32) [(2, 0x7fc00000#32), (0, 0x3f800000#32)])
#guard agree (fpState (.minaS 4#32 2#32 0#32) [(2, 0x7f800001#32), (0, 0x3f800000#32)])
#guard agree (fpState (.maxaD 4#32 2#32 0#32) [(2, 0#32), (0, 0#32)])
#guard agree (fpState (.classS 4#32 2#32) [(2, 0xff800000#32)] 0x7c#32)
#guard agree (fpState (.classD 4#32 2#32) [(2, 1#32)])
#guard agree (fpState (.rintS 4#32 2#32) [(2, 0x40200000#32)] 2#32)
#guard agree (fpState (.rintD 4#32 2#32) [(2, 0x7f800001#32)])
-- a reserved `condn` (16) and CLASS with `ft ≠ 0`: no diagram, Reserved Instruction
#guard specExc (loadImage ((∅ : Program).insert textBase 0x46831050#32) regs0) == some 10#32
#guard Manual.Decode 0x46831050#32 == .reserved
#guard Manual.Decode 0x4603105b#32 == .unpredictable
#guard Manual.Decode 0x46831051#32 == .instr (.cmpS 17#32 1#32 2#32 3#32)
-- Instruction fetch is little-endian too: the program word is fetched and decoded.
#guard agree (loadImage (prog1 (.addiu 0#32 8#32 5#32)) regs0)
-- Removed encodings (Release 6, "6R"/"6Rm", MD00086 Vol II-A Rev 6.06 Table A.1-A.2, p.451):
-- MULT, the pre-Release 6 LL opcode, COP1X with CU1 = 0, BEQL: Reserved Instruction.
#guard specExc (loadImage ((∅ : Program).insert textBase 0x01090018#32) regs0) == some 10#32
#guard specExc (loadImage ((∅ : Program).insert textBase 0xC1090000#32) regs0) == some 10#32
#guard specExc (loadImage ((∅ : Program).insert textBase 0x4C000000#32) { regs0 with cp0Status := 0#32 }) ==
  some 10#32
#guard specExc (loadImage ((∅ : Program).insert textBase 0x51090001#32) regs0) == some 10#32
#guard agree (loadImage ((∅ : Program).insert textBase 0x4C000000#32) { regs0 with cp0Status := 0#32 })
-- COP2 (opcode 0x12): Coprocessor Unusable, CE = 2; the old LWC2 opcode (0x32) is BC in Release 6
-- (BC p.53): no exception, and the model agrees.
#guard specExc (loadImage ((∅ : Program).insert textBase 0x48000000#32) regs0) == some 11#32
#guard specExc (loadImage ((∅ : Program).insert textBase 0xC8000000#32) regs0) == some 0#32
#guard agree (loadImage ((∅ : Program).insert textBase 0xC8000000#32) regs0)
