import Semantics.Manual.Pseudocode

/-!
# Manual.Ops.BranchLikely — branch-likely instructions (MD00086 Vol II-A Rev 6.06)

Sub-wave 7A transcribes the pilot `BEQL`. `NullifyCurrentInstruction()` in `I+1` nullifies the
delay-slot instruction in its own instruction time (§2.2.2.5.4, p.26; `Manual.Cycle`).
-/

namespace Manual.Ops

open Manual

/-- **BEQL rs, rt, offset** — MD00086 Vol II-A Rev 6.06, BEQL, p.73.
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← (GPR[rs] = GPR[rt])
I+1: if condition then
        PC ← PC + target_offset
     else
        NullifyCurrentInstruction()
     endif
```
In `I+1`, `PC` is the address of the delay slot, the branch's `PC + 4`. -/
def BEQL (rs rt offset : W32) : Pseudo Unit := do
  -- I: target_offset ← sign_extend(offset || 0^2)
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- condition ← (GPR[rs] = GPR[rt])
  let condition := (← GPR (reg rs)) == (← GPR (reg rt))
  let pc ← PC
  -- I+1: if condition then PC ← PC + target_offset else NullifyCurrentInstruction() endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .nullify

end Manual.Ops
