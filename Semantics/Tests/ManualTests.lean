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
