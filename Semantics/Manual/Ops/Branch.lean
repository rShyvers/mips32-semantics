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

-- 7B S3 control + system

/-- **BNE rs, rt, offset** — MD00086 Vol II-A Rev 6.06, BNE, p.103.
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← (GPR[rs] ≠ GPR[rt])
I+1: if condition then
        PC ← PC + target_offset
     endif
```
In `I+1`, `PC` is the address of the delay slot, the branch's `PC + 4`. -/
def BNE (rs rt offset : W32) : Pseudo Unit := do
  -- I: target_offset ← sign_extend(offset || 0^2)
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- condition ← (GPR[rs] ≠ GPR[rt])
  let condition := (← GPR (reg rs)) != (← GPR (reg rt))
  let pc ← PC
  -- I+1: if condition then PC ← PC + target_offset endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .fallThrough

/-- **BLEZ rs, offset** — MD00086 Vol II-A Rev 6.06, BLEZ, p.94.
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← GPR[rs] ≤ 0^GPRLEN
I+1: if condition then
        PC ← PC + target_offset
     endif
```
The comparison with zero is signed (two's complement). In `I+1`, `PC` is the delay slot's address, the
branch's `PC + 4`. -/
def BLEZ (rs offset : W32) : Pseudo Unit := do
  -- I: target_offset ← sign_extend(offset || 0^2)
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- condition ← GPR[rs] ≤ 0^GPRLEN
  let x ← GPR (reg rs)
  let condition := x.sle 0#32
  let pc ← PC
  -- I+1: if condition then PC ← PC + target_offset endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .fallThrough

/-- **BGTZ rs, offset** — MD00086 Vol II-A Rev 6.06, BGTZ, p.88.
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← GPR[rs] > 0^GPRLEN
I+1: if condition then
        PC ← PC + target_offset
     endif
```
The comparison with zero is signed (two's complement). In `I+1`, `PC` is the delay slot's address, the
branch's `PC + 4`. -/
def BGTZ (rs offset : W32) : Pseudo Unit := do
  -- I: target_offset ← sign_extend(offset || 0^2)
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- condition ← GPR[rs] > 0^GPRLEN
  let x ← GPR (reg rs)
  let condition := BitVec.slt 0#32 x
  let pc ← PC
  -- I+1: if condition then PC ← PC + target_offset endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .fallThrough

/-- **BLTZ rs, offset** — MD00086 Vol II-A Rev 6.06, BLTZ, p.97.
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← GPR[rs] < 0^GPRLEN
I+1: if condition then
        PC ← PC + target_offset
     endif
```
The comparison with zero is signed (two's complement). In `I+1`, `PC` is the delay slot's address, the
branch's `PC + 4`. -/
def BLTZ (rs offset : W32) : Pseudo Unit := do
  -- I: target_offset ← sign_extend(offset || 0^2)
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- condition ← GPR[rs] < 0^GPRLEN
  let x ← GPR (reg rs)
  let condition := x.slt 0#32
  let pc ← PC
  -- I+1: if condition then PC ← PC + target_offset endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .fallThrough

/-- **BGEZ rs, offset** — MD00086 Vol II-A Rev 6.06, BGEZ, p.75.
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← GPR[rs] ≥ 0^GPRLEN
I+1: if condition then
        PC ← PC + target_offset
     endif
```
The comparison with zero is signed (two's complement). In `I+1`, `PC` is the delay slot's address, the
branch's `PC + 4`. -/
def BGEZ (rs offset : W32) : Pseudo Unit := do
  -- I: target_offset ← sign_extend(offset || 0^2)
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- condition ← GPR[rs] ≥ 0^GPRLEN
  let x ← GPR (reg rs)
  let condition := BitVec.sle 0#32 x
  let pc ← PC
  -- I+1: if condition then PC ← PC + target_offset endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .fallThrough

/-- **BLTZAL rs, offset** — MD00086 Vol II-A Rev 6.06, BLTZAL, p.98 (pre-Release 6 only).
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← GPR[rs] < 0^GPRLEN
     GPR[31] ← PC + 8
I+1: if condition then
        PC ← PC + target_offset
     endif
```
The comparison with zero is signed (two's complement). In `I+1`, `PC` is the delay slot's address, the
branch's `PC + 4`.
Restrictions (p.98): "Branch-and-link Restartability: GPR 31 must not be used for the source register
rs ... The result of executing such an instruction is UNPREDICTABLE" (`Oracle.linkSourceIs31`).
The statements are executed in the order written: `condition` is evaluated before the link is
written. -/
def BLTZAL (rs offset : W32) : Pseudo Unit := do
  let o ← Pseudo.oracle
  let a ← Pseudo.get
  let body : Pseudo Unit := do
    -- I: target_offset ← sign_extend(offset || 0^2)
    let target_offset := sign_extend (imm16 offset ++ 0#2)
    -- condition ← GPR[rs] < 0^GPRLEN
    let x ← GPR (reg rs)
    let condition := x.slt 0#32
    let pc ← PC
    -- GPR[31] ← PC + 8
    setGPR 31 (pc + 8#32)
    -- I+1: if condition then PC ← PC + target_offset endif
    if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .fallThrough
  -- Restrictions: rs = 31 is UNPREDICTABLE
  if reg rs == 31 then unpredictableOr (o.linkSourceIs31 a (.bltzal rs offset)) body else body

/-- **BGEZAL rs, offset** — MD00086 Vol II-A Rev 6.06, BGEZAL, p.76 (pre-Release 6 only).
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← GPR[rs] ≥ 0^GPRLEN
     GPR[31] ← PC + 8
I+1: if condition then
        PC ← PC + target_offset
     endif
```
The comparison with zero is signed (two's complement). In `I+1`, `PC` is the delay slot's address, the
branch's `PC + 4`.
Restrictions (p.76): "Branch-and-link Restartability: GPR 31 must not be used for the source register
rs ... The result of executing such an instruction is UNPREDICTABLE" (`Oracle.linkSourceIs31`).
The statements are executed in the order written: `condition` is evaluated before the link is
written. -/
def BGEZAL (rs offset : W32) : Pseudo Unit := do
  let o ← Pseudo.oracle
  let a ← Pseudo.get
  let body : Pseudo Unit := do
    -- I: target_offset ← sign_extend(offset || 0^2)
    let target_offset := sign_extend (imm16 offset ++ 0#2)
    -- condition ← GPR[rs] ≥ 0^GPRLEN
    let x ← GPR (reg rs)
    let condition := BitVec.sle 0#32 x
    let pc ← PC
    -- GPR[31] ← PC + 8
    setGPR 31 (pc + 8#32)
    -- I+1: if condition then PC ← PC + target_offset endif
    if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .fallThrough
  -- Restrictions: rs = 31 is UNPREDICTABLE
  if reg rs == 31 then unpredictableOr (o.linkSourceIs31 a (.bgezal rs offset)) body else body

end Manual.Ops
