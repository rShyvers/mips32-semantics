import Semantics.Refine.Abs
import Semantics.Tests.StepFixtures

/-!
# ManualTests — the independent manual spec, run on concrete states

`Manual.InstructionTime modelImpl modelOracle decode` on small programs, checked against the
expected architectural effect and against `abs (step s)` (the harness in `EquivHarness` does the
same over every corpus and oracle program). `decode` is the model's decoder, used here only as the
decoder argument of the spec (`Manual.DecoderSound`).
-/

open Manual Refine StepTest

/-- One instruction time of the spec from the model state `s`. -/
def specTime (s : State) : Option Arch := InstructionTime modelImpl modelOracle decode (abs s)

/-- The fields the tests compare. -/
def archKey (a : Arch) : List W32 :=
  [a.PC, a.GPR 8, a.GPR 9, a.GPR 10, a.Cause, a.EPC, a.Status, a.Count, a.FCSR, a.FPR 0]

/-- Spec and model agree on the compared fields. -/
def agree (s : State) : Bool :=
  match specTime s with
  | some a => archKey a == archKey (abs (step s)) && a.BranchDelay == (step s).pendingBranch &&
      a.Nullify == (step s).nullified
  | none => false

-- ADD without overflow, and with overflow (Integer Overflow, ExcCode 12, EPC = the add).
#guard agree (loadImage (prog1 (.add 8#32 9#32 10#32)) (setRegs regs0 [(8, 3#32), (9, 4#32)]))
#guard agree (loadImage (prog1 (.add 8#32 9#32 10#32)) (setRegs regs0 [(8, 0x7fffffff#32), (9, 1#32)]))
#guard (match specTime (loadImage (prog1 (.add 8#32 9#32 10#32))
          (setRegs regs0 [(8, 0x7fffffff#32), (9, 1#32)])) with
        | some a => (a.Cause >>> 2) &&& 0x1F#32 == 12#32 && a.EPC == textBase
        | none => false)
-- BEQL not taken: the delay slot is nullified in the next instruction time.
#guard agree (loadImage (prog1 (.beql 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)]))
#guard (match specTime (loadImage (prog1 (.beql 8#32 9#32 3#32)) (setRegs regs0 [(8, 5#32), (9, 6#32)])) with
        | some a => a.Nullify && a.PC == textBase + 4#32 &&
            (match InstructionTime modelImpl modelOracle decode a with
             | some b => b.PC == textBase + 8#32 && !b.Nullify && b.Count == a.Count + 1#32
             | none => false)
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

/-- The spec's `FPR[i]` and `FCSR` after one instruction time. -/
def specFp (s : State) (i : Fin 32) : Option (W32 × W32) := (specTime s).map fun a => (a.FPR i, a.FCSR)

-- (1) MADD.S, Enables.O: the multiply traps with its own Cause (O), the add never runs (review r1).
#guard (match specTime (fpState (.maddS 8#32 6#32 2#32 4#32)
          [(2, 0x7f7fffff#32), (4, 0x40000000#32), (6, 0xff800000#32), (8, 0x12345678#32)] 0x200#32) with
        | some a => (a.Cause >>> 2) &&& 0x1F#32 == 15#32 && a.FCSR == 0x4200#32 && a.FPR 8 == 0x12345678#32
        | none => false)
#guard agree (fpState (.maddS 8#32 6#32 2#32 4#32)
  [(2, 0x7f7fffff#32), (4, 0x40000000#32), (6, 0xff800000#32), (8, 0x12345678#32)] 0x200#32)
-- (1) without enables: Cause is the add's (V), Flags V|O|I (review r1c).
#guard specFp (fpState (.maddS 8#32 6#32 2#32 4#32)
  [(2, 0x7f7fffff#32), (4, 0x40000000#32), (6, 0xff800000#32)]) 8 = some (0x7fbfffff#32, 0x00010054#32)
-- (2) NMADD.S: -(vfr + (vfs x vft)): fr's QNaN is the add's first operand, the negate flips its sign and
-- signals Invalid; MADD.S keeps the product (vfs) first (review r2).
#guard specFp (fpState (.nmaddS 8#32 6#32 2#32 4#32)
  [(6, 0x7f800001#32), (2, 0x7f800002#32), (4, 0x3f800000#32)]) 8 = some (0xff800001#32, 0x00010040#32)
#guard specFp (fpState (.maddS 8#32 6#32 2#32 4#32)
  [(6, 0x7f800001#32), (2, 0x7f800002#32), (4, 0x3f800000#32)]) 8 = some (0x7f800002#32, 0#32)
#guard agree (fpState (.nmaddS 8#32 6#32 2#32 4#32) [(6, 0x7f800001#32), (2, 0x7f800002#32), (4, 0x3f800000#32)])
-- (3) NEG.S / ABS.S of a QNaN with the sign set: reading A' (review r5).
#guard specFp (fpState (.negS 4#32 2#32) [(2, 0xff800001#32)]) 4 = some (0x7f800001#32, 0x00010040#32)
#guard specFp (fpState (.absS 4#32 2#32) [(2, 0xff800001#32)]) 4 = some (0x7f800001#32, 0x00010040#32)
#guard agree (fpState (.negS 4#32 2#32) [(2, 0xff800001#32)])
-- (5) JR.HB: the hint-16 word decodes to `.jrHb` and jumps as `jr` (review r4); hint 1 is UNPREDICTABLE: RI.
#guard agree (loadImage (prog1 (.jrHb 8#32)) (setRegs regs0 [(8, 0x00400100#32)]))
#guard (match specTime (loadImage (prog1 (.jrHb 8#32)) (setRegs regs0 [(8, 0x00400100#32)])) with
        | some a => a.BranchDelay == some 0x00400100#32
        | none => false)
#guard UnpredictableEncoding 0x01000048#32 && !UnpredictableEncoding 0x01000408#32 &&
  !UnpredictableEncoding 0x01000008#32
-- (6) EXT with lsb + msbd > 31, CLZ with rt != rd, ADD with a nonzero shamt: UNPREDICTABLE encodings (review r3).
#guard UnpredictableEncoding 0x7D099D00#32 && UnpredictableEncoding (0x70000020#32 ||| (1#32 <<< 16)) &&
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
