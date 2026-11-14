import Semantics.Manual.Pseudocode

/-!
# Manual.Ops.Branch — branches with a delay slot (MD00086 Vol II-A Rev 6.06)

Sub-wave 7A transcribes the pilot `BEQ`. `I+1:` statements are scheduled with `I1` and happen in
the next instruction time, whose `PC` is the delay slot's address, `PC + 4` (MD00086 Vol II-A Rev 6.06
§1.3, Table 1.1, p.6).
-/

namespace Manual.Ops

open Manual

/-- **BEQ rs, rt, offset** — MD00086 Vol II-A Rev 6.06, BEQ, p.72.
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← (GPR[rs] = GPR[rt])
I+1: if condition then
        PC ← PC + target_offset
     endif
```
In `I+1`, `PC` is the address of the delay slot, the branch's `PC + 4`. When the condition is false
`I+1` assigns nothing; the delay slot still follows the branch (`Delay.fallThrough`). -/
def BEQ (rs rt offset : W32) : Pseudo Unit := do
  -- I: target_offset ← sign_extend(offset || 0^2)
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- condition ← (GPR[rs] = GPR[rt])
  let condition := (← GPR (reg rs)) == (← GPR (reg rt))
  let pc ← PC
  -- I+1: if condition then PC ← PC + target_offset endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .fallThrough

end Manual.Ops
