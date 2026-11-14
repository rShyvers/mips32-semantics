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

-- 7B S3 control + system

/-- **BNEL rs, rt, offset** — MD00086 Vol II-A Rev 6.06, BNEL, p.104 (pre-Release 6 only).
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← (GPR[rs] ≠ GPR[rt])
I+1: if condition then
        PC ← PC + target_offset
     else
        NullifyCurrentInstruction()
     endif
```
In `I+1`, `PC` is the address of the delay slot, the branch's `PC + 4`. -/
def BNEL (rs rt offset : W32) : Pseudo Unit := do
  -- I: target_offset ← sign_extend(offset || 0^2)
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- condition ← (GPR[rs] ≠ GPR[rt])
  let condition := (← GPR (reg rs)) != (← GPR (reg rt))
  let pc ← PC
  -- I+1: if condition then PC ← PC + target_offset else NullifyCurrentInstruction() endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .nullify

/-- **BLEZL rs, offset** — MD00086 Vol II-A Rev 6.06, BLEZL, p.95 (pre-Release 6 only).
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← GPR[rs] ≤ 0^GPRLEN
I+1: if condition then
        PC ← PC + target_offset
     else
        NullifyCurrentInstruction()
     endif
```
The comparison with zero is signed (two's complement). In `I+1`, `PC` is the delay slot's address, the
branch's `PC + 4`. -/
def BLEZL (rs offset : W32) : Pseudo Unit := do
  -- I: target_offset ← sign_extend(offset || 0^2)
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- condition ← GPR[rs] ≤ 0^GPRLEN
  let x ← GPR (reg rs)
  let condition := x.sle 0#32
  let pc ← PC
  -- I+1: if condition then PC ← PC + target_offset else NullifyCurrentInstruction() endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .nullify

/-- **BGTZL rs, offset** — MD00086 Vol II-A Rev 6.06, BGTZL, p.89 (pre-Release 6 only).
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← GPR[rs] > 0^GPRLEN
I+1: if condition then
        PC ← PC + target_offset
     else
        NullifyCurrentInstruction()
     endif
```
The comparison with zero is signed (two's complement). In `I+1`, `PC` is the delay slot's address, the
branch's `PC + 4`. -/
def BGTZL (rs offset : W32) : Pseudo Unit := do
  -- I: target_offset ← sign_extend(offset || 0^2)
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- condition ← GPR[rs] > 0^GPRLEN
  let x ← GPR (reg rs)
  let condition := BitVec.slt 0#32 x
  let pc ← PC
  -- I+1: if condition then PC ← PC + target_offset else NullifyCurrentInstruction() endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .nullify

/-- **BLTZL rs, offset** — MD00086 Vol II-A Rev 6.06, BLTZL, p.101 (pre-Release 6 only).
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← GPR[rs] < 0^GPRLEN
I+1: if condition then
        PC ← PC + target_offset
     else
        NullifyCurrentInstruction()
     endif
```
The comparison with zero is signed (two's complement). In `I+1`, `PC` is the delay slot's address, the
branch's `PC + 4`. -/
def BLTZL (rs offset : W32) : Pseudo Unit := do
  -- I: target_offset ← sign_extend(offset || 0^2)
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- condition ← GPR[rs] < 0^GPRLEN
  let x ← GPR (reg rs)
  let condition := x.slt 0#32
  let pc ← PC
  -- I+1: if condition then PC ← PC + target_offset else NullifyCurrentInstruction() endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .nullify

/-- **BGEZL rs, offset** — MD00086 Vol II-A Rev 6.06, BGEZL, p.86 (pre-Release 6 only).
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← GPR[rs] ≥ 0^GPRLEN
I+1: if condition then
        PC ← PC + target_offset
     else
        NullifyCurrentInstruction()
     endif
```
The comparison with zero is signed (two's complement). In `I+1`, `PC` is the delay slot's address, the
branch's `PC + 4`. -/
def BGEZL (rs offset : W32) : Pseudo Unit := do
  -- I: target_offset ← sign_extend(offset || 0^2)
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- condition ← GPR[rs] ≥ 0^GPRLEN
  let x ← GPR (reg rs)
  let condition := BitVec.sle 0#32 x
  let pc ← PC
  -- I+1: if condition then PC ← PC + target_offset else NullifyCurrentInstruction() endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .nullify

/-- **BLTZALL rs, offset** — MD00086 Vol II-A Rev 6.06, BLTZALL, p.99 (pre-Release 6 only).
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← GPR[rs] < 0^GPRLEN
     GPR[31] ← PC + 8
I+1: if condition then
        PC ← PC + target_offset
     else
        NullifyCurrentInstruction()
     endif
```
The comparison with zero is signed (two's complement). In `I+1`, `PC` is the delay slot's address, the
branch's `PC + 4`.
Restrictions (p.99): "Branch-and-link Restartability: GPR 31 must not be used for the source register
rs ... The result of executing such an instruction is UNPREDICTABLE" (`Oracle.linkSourceIs31`).
The statements are executed in the order written: `condition` is evaluated before the link is
written. -/
def BLTZALL (rs offset : W32) : Pseudo Unit := do
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
    -- I+1: if condition then PC ← PC + target_offset else NullifyCurrentInstruction() endif
    if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .nullify
  -- Restrictions: rs = 31 is UNPREDICTABLE
  if reg rs == 31 then unpredictableOr (o.linkSourceIs31 a (.bltzall rs offset)) body else body

/-- **BGEZALL rs, offset** — MD00086 Vol II-A Rev 6.06, BGEZALL, p.80 (pre-Release 6 only).
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← GPR[rs] ≥ 0^GPRLEN
     GPR[31] ← PC + 8
I+1: if condition then
        PC ← PC + target_offset
     else
        NullifyCurrentInstruction()
     endif
```
The comparison with zero is signed (two's complement). In `I+1`, `PC` is the delay slot's address, the
branch's `PC + 4`.
Restrictions (p.80): "Branch-and-link Restartability: GPR 31 must not be used for the source register
rs ... The result of executing such an instruction is UNPREDICTABLE" (`Oracle.linkSourceIs31`).
The statements are executed in the order written: `condition` is evaluated before the link is
written. -/
def BGEZALL (rs offset : W32) : Pseudo Unit := do
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
    -- I+1: if condition then PC ← PC + target_offset else NullifyCurrentInstruction() endif
    if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .nullify
  -- Restrictions: rs = 31 is UNPREDICTABLE
  if reg rs == 31 then unpredictableOr (o.linkSourceIs31 a (.bgezall rs offset)) body else body

end Manual.Ops
