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

/-- **NAL** — MD00086 Vol II-A Rev 6.06, NAL, p.306 (Release 6: `REGIMM 00000 10000 offset`).
```
GPR[31] ← PC + 8
```
Restrictions (p.306): "NAL is considered to be a not-taken branch, with a delay slot, and may not be
followed by instructions not allowed in delay slots"; the 16-bit offset "is ignored". **Pin
(transcription):** the Operation has no `I+1:` statement; the delay slot that "a not-taken branch,
with a delay slot" implies is transcribed as the `I+1:` of a not-taken branch, which assigns nothing
(`Delay.fallThrough`), so the next instruction is in a delay slot (`InstructionInBranchDelaySlot`,
and a CTI there signals Reserved Instruction) and `PC` then advances past it. -/
def NAL (_offset : W32) : Pseudo Unit := do
  let pc ← PC
  -- GPR[31] ← PC + 8
  setGPR 31 (pc + 8#32)
  -- (Restrictions) a not-taken branch, with a delay slot: I+1 assigns nothing
  I1 .fallThrough

/-- **BAL offset** — MD00086 Vol II-A Rev 6.06, BAL, p.50 (Release 6 diagram: `REGIMM 00000 10001
offset`; BGEZAL with `rs ≠ 0` "is required to signal a Reserved Instruction exception").
```
I:   target_offset ← sign_extend(offset || 0^2)
     GPR[31] ← PC + 8
I+1: PC ← PC + target_offset
```
In `I+1`, `PC` is the delay slot's address, the branch's `PC + 4`. -/
def BAL (offset : W32) : Pseudo Unit := do
  -- I: target_offset ← sign_extend(offset || 0^2)
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  let pc ← PC
  -- GPR[31] ← PC + 8
  setGPR 31 (pc + 8#32)
  -- I+1: PC ← PC + target_offset
  I1 (.jump ((pc + 4#32) + target_offset))

end Manual.Ops
