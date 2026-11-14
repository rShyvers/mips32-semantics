import Semantics.Manual.Pseudocode

/-!
# Manual.Ops.IntArith — integer arithmetic (MD00086 Vol II-A Rev 6.06)

Sub-wave 7A transcribes the pilot `ADD`; 7B adds the rest of the family.
-/

namespace Manual.Ops

open Manual

/-- **ADD rd, rs, rt** — MD00086 Vol II-A Rev 6.06, ADD, p.33.
```
temp ← (GPR[rs]31||GPR[rs]31..0) + (GPR[rt]31||GPR[rt]31..0)
if temp32 ≠ temp31 then
   SignalException(IntegerOverflow)
else
   GPR[rd] ← temp
endif
```
`GPR[rd] ← temp` stores the 32-bit result `temp31..0` (GPRLEN = 32). -/
def ADD (rs rt rd : W32) : Pseudo Unit := do
  let x ← GPR (reg rs)
  let y ← GPR (reg rt)
  -- temp ← (GPR[rs]31||GPR[rs]31..0) + (GPR[rt]31||GPR[rt]31..0)
  let temp : BitVec 33 := (BitVec.ofBool (bit x 31) ++ x) + (BitVec.ofBool (bit y 31) ++ y)
  -- if temp32 ≠ temp31 then SignalException(IntegerOverflow)
  if bit temp 32 ≠ bit temp 31 then SignalException .IntegerOverflow
  -- else GPR[rd] ← temp
  else setGPR (reg rd) (low temp 32)

end Manual.Ops
