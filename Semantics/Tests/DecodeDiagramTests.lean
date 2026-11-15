import Semantics.Refine.Abs
import Semantics.Manual.Decode
import Semantics.Tests.StepFixtures

/-!
# DecodeDiagramTests — the specification's own decoder `Manual.Decode` (wave 12b)

Concrete words through `Manual.Decode`, and the regression of audit finding D1: `MFC0` of a register
coprocessor 0 does not contain (`rd = 0`, `sel = 0`, `Index`, absent under the Fixed Mapping MMU) is
a word of the MFC0 diagram (MD00086 Vol II-A Rev 6.06, MFC0, p.266); the model's `decode` rejects it,
the spec decodes it and its Operation reaches the UNDEFINED choice `Oracle.cp0Undefined` ("Pre-Release
6: The results are UNDEFINED if coprocessor 0 does not contain a register as specified by rd and sel",
p.266), so two oracles give two instruction times.
-/

open Manual Refine StepTest

-- ADD $8, $9, $10; NOP (= SLL $0, $0, 0); a word of no diagram; the JR hint UNPREDICTABLE.
#guard Decode 0x012A4020#32 == .instr (.add 9#32 10#32 8#32)
#guard Decode 0x00000000#32 == .instr (.sll 0#32 0#32 0#32)
#guard Decode 0xFFFFFFFF#32 == .reserved
#guard Decode 0x01000048#32 == .unpredictable
-- EXT with lsb + msbd > 31 is a word of the EXT diagram (p.183): decoded; its Operation is UNPREDICTABLE.
#guard Decode 0x7D099D00#32 == .instr (.ext 9#32 8#32 20#32 20#32)
-- D1: MFC0 $9, $0, 0 (Index): the diagram word, rejected by `decode`, decoded by the spec.
#guard Manual.enc (.mfc0 9#32 0#32 0#32) == some 0x40090000#32
#guard decode 0x40090000#32 == none
#guard Decode 0x40090000#32 == .instr (.mfc0 9#32 0#32 0#32)
#guard decodeDiagram 0x40090000#32 == some (.mfc0 9#32 0#32 0#32)

/-- An oracle that resolves the UNDEFINED CP0 access by writing `0xDEADBEEF` to `GPR[9]`. -/
def oracleCp0 : Oracle :=
  { modelOracle with cp0Undefined := fun a _ => .arbitrary { a with GPR := update a.GPR 9 0xDEADBEEF#32 } }

/-- The `MFC0 $9, $0, 0` state (Kernel Mode). -/
def sIndex : State := loadImage (prog1 (.mfc0 9#32 0#32 0#32)) regs0

-- The model's oracle: Reserved Instruction (ExcCode 10), as `step`.
#guard (match InstructionTime modelImpl modelOracle decodeDiagram (abs sIndex) with
        | some a => (a.Cause >>> 2) &&& 0x1F#32 == 10#32 && a.PC == (abs (step sIndex)).PC
        | none => false)
-- Another valid resolution of the UNDEFINED access: reached through the spec's decoder.
#guard (match InstructionTime modelImpl oracleCp0 decodeDiagram (abs sIndex) with
        | some a => a.GPR 9 == 0xDEADBEEF#32
        | none => false)
-- With the model's `decode` as the decoder the choice was unreachable (the D1 finding).
#guard (match InstructionTime modelImpl oracleCp0 decode (abs sIndex) with
        | some a => a.GPR 9 != 0xDEADBEEF#32
        | none => false)
