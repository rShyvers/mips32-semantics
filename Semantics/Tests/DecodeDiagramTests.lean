import Semantics.Refine.Abs
import Semantics.Manual.Decode
import Semantics.Tests.ManualTests

/-!
# DecodeDiagramTests — the specification's own decoder `Manual.Decode`

Concrete words through `Manual.Decode`, and the regression of audit finding D1: `MFC0` of a register
coprocessor 0 does not contain (`rd = 0`, `sel = 0`, `Index`, absent under the Fixed Mapping MMU) is
a word of the MFC0 diagram (MD00086 Vol II-A Rev 6.06, MFC0, p.266). Before Release 6 its result was
UNDEFINED and the model's `decode` rejected it; in Release 6 "Reading a reserved register or a
register that is not implemented for the current core configuration returns 0" (p.266), so both
decoders accept it and both the model and the specification read 0.
-/

open Manual Refine ManualTest

-- ADD $8, $9, $10; NOP (= SLL $0, $0, 0); a word of no diagram; the JALR hint UNPREDICTABLE.
#guard Decode 0x012A4020#32 == .instr (.add 9#32 10#32 8#32)
#guard Decode 0x00000000#32 == .instr (.sll 0#32 0#32 0#32)
#guard Decode 0xFFFFFFFF#32 == .reserved
#guard Decode 0x01000049#32 == .unpredictable
-- EXT with lsb + msbd > 31 is a word of the EXT diagram (p.183): decoded; its Operation is UNPREDICTABLE.
#guard Decode 0x7D099D00#32 == .instr (.ext 9#32 8#32 20#32 20#32)
-- D1: MFC0 $9, $0, 0 (Index): a diagram word, decoded by both decoders (Release 6).
#guard Manual.enc (.mfc0 9#32 0#32 0#32) == some 0x40090000#32
#guard decode 0x40090000#32 == some (.mfc0 9#32 0#32 0#32)
#guard Decode 0x40090000#32 == .instr (.mfc0 9#32 0#32 0#32)
#guard decodeDiagram 0x40090000#32 == some (.mfc0 9#32 0#32 0#32)

/-- The `MFC0 $9, $0, 0` state (Kernel Mode), with `$9 = 0x55` before. -/
def sIndex : State := loadImage (prog1 (.mfc0 9#32 0#32 0#32)) (setRegs regs0 [(9, 0x55#32)])

-- The register is not implemented: the specification reads 0, as `step` does, through either decoder
-- (no oracle choice is involved any more).
#guard (match InstructionTime modelImpl modelOracle decodeDiagram (abs sIndex) with
        | some a => a.GPR 9 == 0#32 && a.PC == (abs (step sIndex)).PC &&
            a.GPR 9 == (abs (step sIndex)).GPR 9
        | none => false)
#guard (match InstructionTime modelImpl modelOracle decode (abs sIndex) with
        | some a => a.GPR 9 == 0#32
        | none => false)

/-! ## The Release 6 diagrams -/

-- PAUSE (`SLL r0, r0, 5`, p.317) is decoded as PAUSE, not as SLL; SLL r0, r0, 3 (EHB) stays SLL.
#guard Decode 0x00000140#32 == .instr .pause
#guard Decode 0x000000C0#32 == .instr (.sll 0#32 0#32 3#32)
-- AUI (p.47) with any `rs`; LUI is AUI with `rs = 0`.
#guard Decode (encode (.aui 8#32 9#32 0x1234#32)) == .instr (.aui 8#32 9#32 0x1234#32)
#guard Decode 0x3C091234#32 == .instr (.aui 0#32 9#32 0x1234#32)
-- NAL / BAL (REGIMM, `rs = 0`); BLTZAL / BGEZAL with `rs ≠ 0` are removed: no diagram.
#guard Decode 0x04100007#32 == .instr (.nal 7#32)
#guard Decode 0x04110007#32 == .instr (.bal 7#32)
#guard Decode 0x05100007#32 == .reserved
#guard Decode 0x05110007#32 == .reserved
-- RDHWR with `sel` (bits 8..6); bits 10..9 nonzero are UNPREDICTABLE.
#guard Decode (encode (.rdhwr 9#32 2#32 3#32)) == .instr (.rdhwr 9#32 2#32 3#32)
#guard Decode (encode (.rdhwr 9#32 2#32 0#32) ||| 0x200#32) == .unpredictable
-- LL / SC / PREF in SPECIAL3 with the 9-bit offset; bit 6 set is UNPREDICTABLE; the pre-Release 6
-- opcodes (0x30, 0x38, 0x33) are removed.
#guard Decode (encode (.ll 8#32 9#32 0x1FC#32)) == .instr (.ll 8#32 9#32 0x1FC#32)
#guard Decode (encode (.sc 8#32 9#32 0x1FC#32)) == .instr (.sc 8#32 9#32 0x1FC#32)
#guard Decode (encode (.pref 8#32 1#32 0x1FC#32)) == .instr (.pref 8#32 1#32 0x1FC#32)
#guard Decode (encode (.ll 8#32 9#32 0x1FC#32) ||| 0x40#32) == .unpredictable
#guard Decode 0xC1090000#32 == .reserved
#guard Decode 0xE1090000#32 == .reserved
#guard Decode 0xCD010000#32 == .reserved
-- CLO / CLZ in SPECIAL (`rt = 0`, `sa = 1`); the SPECIAL2 forms are removed.
#guard Decode (encode (.clz 8#32 9#32)) == .instr (.clz 8#32 9#32)
#guard Decode (encode (.clo 8#32 9#32)) == .instr (.clo 8#32 9#32)
#guard Decode 0x71094820#32 == .reserved
-- JR (SPECIAL function 001000) is removed; JR is JALR with `rd = 0` (JR p.207).
#guard Decode 0x01000008#32 == .reserved
#guard Decode 0x01000009#32 == .instr (.jalr 8#32 0#32)
-- Removed: MULT, MFHI, MOVN, BEQL, TEQI, LWL, COP1X (LWXC1), MOVCI, C.cond.S, BC1F.
#guard [0x01090018#32, 0x00004010#32, 0x012A400B#32, 0x51090001#32, 0x050C0001#32,
  0x89090000#32, 0x4D090000#32, 0x01014001#32, 0x46020030#32, 0x45000001#32].all
  (fun w => Decode w == .reserved)
-- The pre-Release 6 ADDI opcode is POP10 (Table A.26, p.464): `0x21090001` (rs = 8 < rt = 9) is
-- BEQC, `0x21280001` (rs = 9 ≥ rt = 8) is BOVC, `0x20090001` (rs = 0) is BEQZALC. BLEZL/BGTZL
-- (POP26/POP27 with `rt = 0`) stay removed.
#guard Decode 0x21090001#32 == .instr (.beqc 8#32 9#32 1#32)
#guard Decode 0x21280001#32 == .instr (.bovc 9#32 8#32 1#32)
#guard Decode 0x20090001#32 == .instr (.beqzalc 9#32 1#32)
#guard Decode 0x59000001#32 == .reserved
#guard Decode 0x5D000001#32 == .reserved
-- The encoding spaces: COP1X, MOVCI are outside COP1 (Reserved Instruction even with CU1 = 0);
-- COP2 is opcode 0x12 only; the Release 6 CACHE (SPECIAL3 function 100101) is in the COP0 space.
#guard !InCop1Space 0x4C000000#32 && !InCop1Space 0x00010001#32 && InCop1Space 0x44000000#32
#guard InCop2Space 0x48000000#32 && !InCop2Space 0xC8000000#32
#guard InCop0Space 0x7C000025#32 && InCop0Space 0x40000000#32 && !InCop0Space 0x7C000026#32
#guard Undecodable 0x4C000000#32 (abs { regs0 with cp0Status := 0#32 }) == .ReservedInstruction
#guard Undecodable 0x7C000025#32 (abs { regs0 with cp0Status := 0x10#32 }) == .CoprocessorUnusable 0
-- Every word `decode` accepts is decoded to the same instruction by the spec (checked on 2^16 words).
#guard (List.range 65536).all fun k =>
  let w := BitVec.ofNat 32 (k * 2654435761 + 977)
  match decode w with
  | some i => Decode w == .instr i
  | none => true

-- ERETNC (p.179: ERET with bit 6 set), SIGRIE (p.375: REGIMM rt = 0x17, rs = 0), CACHE (p.114:
-- SPECIAL3 funct 0x25, bit 6 zero) are diagram words; MFC0/MTC0 of any (rd, sel) too.
#guard Decode 0x42000058#32 == .instr .eretnc
#guard Decode 0x04170005#32 == .instr (.sigrie 5#32)
#guard Decode 0x7d34fc25#32 == .instr (.cache 9#32 20#32 0x1f8#32)
#guard decodeDiagram 0x42000058#32 == decode 0x42000058#32
#guard decodeDiagram 0x04170005#32 == decode 0x04170005#32
#guard decodeDiagram 0x7d34fc25#32 == decode 0x7d34fc25#32
#guard Decode (encode (.mfc0 8#32 4#32 2#32)) == .instr (.mfc0 8#32 4#32 2#32)
#guard Decode (encode (.mtc0 8#32 31#32 7#32)) == .instr (.mtc0 8#32 31#32 7#32)
-- DVP p.172 / EVP p.181: the diagram words decode; a nonzero unnamed field is UNPREDICTABLE (§2.1.1, p.12)
#guard Decode 0x41680024#32 == .instr (.dvp 8#32)
#guard Decode 0x41600004#32 == .instr (.evp 0#32)
#guard decodeDiagram 0x41680024#32 == decode 0x41680024#32
#guard Decode 0x41680824#32 == .unpredictable
#guard Decode 0x4168002c#32 == .unpredictable
