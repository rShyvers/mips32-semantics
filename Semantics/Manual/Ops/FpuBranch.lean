import Semantics.Manual.FPU

/-!
# Manual.Ops.FpuBranch — branches on the FP condition code (MD00086 Vol II-A Rev 6.06), 7B S4

`BC1F`, `BC1T`, `BC1FL`, `BC1TL`. As `BEQ`/`BEQL`: the `I+1:` statements are `I1`; in `I+1`, `PC` is
the address of the delay slot, the branch's `PC + 4`. The branch-likely forms call
`NullifyCurrentInstruction()` when not taken (`I1 .nullify`, §2.2.2.5.4, p.26).

`cc` is the 3-bit condition-code field of the instruction word (bits 20..18, e.g. BC1F p.56, MOVF.fmt
p.277), "The Condition code number in the range 0..7" (Figure 2.25, p.23): the raw `cc` operand of
the `Instruction` constructor is read as `(low cc 3).toNat` (7C S4b; before, `cc.toNat` read bits
of the FCSR above 31 for an operand >= 8 that no instruction word can carry).
-/

namespace Manual.Ops

open Manual

/-- **BC1F cc, offset** — MD00086 Vol II-A Rev 6.06, BC1F, p.56.
```
I:   condition <- FPConditionCode(cc) = 0
     target_offset <- (offset15)^(GPRLEN-(16+2)) || offset || 0^2
I+1: if condition then
        PC <- PC + target_offset
     endif
```
In `I+1`, `PC` is the address of the delay slot, the branch's `PC + 4`. When the condition is false `I+1` assigns nothing; the delay slot still follows the branch (`Delay.fallThrough`). -/
def BC1F (cc offset : W32) : Pseudo Unit := do
  -- I: condition <- FPConditionCode(cc) = 0
  let condition := (← FPConditionCode (low cc 3).toNat) == false
  -- target_offset <- (offset15)^(GPRLEN-(16+2)) || offset || 0^2
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  let pc ← PC
  -- I+1: if condition then PC <- PC + target_offset endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .fallThrough

/-- **BC1T cc, offset** — MD00086 Vol II-A Rev 6.06, BC1T, p.60.
```
I:   condition <- FPConditionCode(cc) = 1
     target_offset <- (offset15)^(GPRLEN-(16+2)) || offset || 0^2
I+1: if condition then
        PC <- PC + target_offset
     endif
```
In `I+1`, `PC` is the address of the delay slot, the branch's `PC + 4`. When the condition is false `I+1` assigns nothing; the delay slot still follows the branch (`Delay.fallThrough`). -/
def BC1T (cc offset : W32) : Pseudo Unit := do
  -- I: condition <- FPConditionCode(cc) = 1
  let condition := (← FPConditionCode (low cc 3).toNat) == true
  -- target_offset <- (offset15)^(GPRLEN-(16+2)) || offset || 0^2
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  let pc ← PC
  -- I+1: if condition then PC <- PC + target_offset endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .fallThrough

/-- **BC1FL cc, offset** — MD00086 Vol II-A Rev 6.06, BC1FL, p.58.
```
I:   condition <- FPConditionCode(cc) = 0
     target_offset <- (offset15)^(GPRLEN-(16+2)) || offset || 0^2
I+1: if condition then
        PC <- PC + target_offset
     else
        NullifyCurrentInstruction()
     endif
```
In `I+1`, `PC` is the address of the delay slot, the branch's `PC + 4`. -/
def BC1FL (cc offset : W32) : Pseudo Unit := do
  -- I: condition <- FPConditionCode(cc) = 0
  let condition := (← FPConditionCode (low cc 3).toNat) == false
  -- target_offset <- (offset15)^(GPRLEN-(16+2)) || offset || 0^2
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  let pc ← PC
  -- I+1: if condition then PC <- PC + target_offset else NullifyCurrentInstruction() endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .nullify

/-- **BC1TL cc, offset** — MD00086 Vol II-A Rev 6.06, BC1TL, p.62.
```
I:   condition <- FPConditionCode(cc) = 1
     target_offset <- (offset15)^(GPRLEN-(16+2)) || offset || 0^2
I+1: if condition then
        PC <- PC + target_offset
     else
        NullifyCurrentInstruction()
     endif
```
In `I+1`, `PC` is the address of the delay slot, the branch's `PC + 4`. -/
def BC1TL (cc offset : W32) : Pseudo Unit := do
  -- I: condition <- FPConditionCode(cc) = 1
  let condition := (← FPConditionCode (low cc 3).toNat) == true
  -- target_offset <- (offset15)^(GPRLEN-(16+2)) || offset || 0^2
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  let pc ← PC
  -- I+1: if condition then PC <- PC + target_offset else NullifyCurrentInstruction() endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .nullify

end Manual.Ops
