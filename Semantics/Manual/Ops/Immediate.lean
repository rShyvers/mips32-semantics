import Semantics.Manual.Pseudocode

/-!
# Manual.Ops.Immediate — arithmetic and logical with a 16-bit immediate (MD00086 Vol II-A Rev 6.06)
-/

namespace Manual.Ops

open Manual

/-- **ADDI rt, rs, immediate** — MD00086 Vol II-A Rev 6.06, ADDI, p.35.
```
temp ← (GPR[rs]31||GPR[rs]31..0) + sign_extend(immediate)
if temp32 ≠ temp31 then
   SignalException(IntegerOverflow)
else
   GPR[rt] ← temp
endif
```
`sign_extend(immediate)` is taken at the 33-bit width of `temp` (its sign bit repeated). -/
def ADDI (rs rt imm : W32) : Pseudo Unit := do
  let x ← GPR (reg rs)
  let se := sign_extend (imm16 imm)
  -- temp ← (GPR[rs]31||GPR[rs]31..0) + sign_extend(immediate)
  let temp : BitVec 33 := (BitVec.ofBool (bit x 31) ++ x) + (BitVec.ofBool (bit se 31) ++ se)
  -- if temp32 ≠ temp31 then SignalException(IntegerOverflow)
  if bit temp 32 != bit temp 31 then SignalException .IntegerOverflow
  -- else GPR[rt] ← temp
  else setGPR (reg rt) (low temp 32)

/-- **ADDIU rt, rs, immediate** — MD00086 Vol II-A Rev 6.06, ADDIU, p.36.
```
temp ← GPR[rs] + sign_extend(immediate)
GPR[rt] ← temp
``` -/
def ADDIU (rs rt imm : W32) : Pseudo Unit := do
  -- temp ← GPR[rs] + sign_extend(immediate)
  let temp := (← GPR (reg rs)) + sign_extend (imm16 imm)
  -- GPR[rt] ← temp
  setGPR (reg rt) temp

/-- **SLTI rt, rs, immediate** — MD00086 Vol II-A Rev 6.06, SLTI, p.379.
```
if GPR[rs] < sign_extend(immediate) then
   GPR[rt] ← 0GPRLEN-1 || 1
else
   GPR[rt] ← 0GPRLEN
endif
```
Signed comparison (Description, p.379). -/
def SLTI (rs rt imm : W32) : Pseudo Unit := do
  -- if GPR[rs] < sign_extend(immediate) then GPR[rt] ← 0^(GPRLEN-1) || 1
  if (← GPR (reg rs)).slt (sign_extend (imm16 imm)) then setGPR (reg rt) ((0#31 ++ 1#1).setWidth 32)
  -- else GPR[rt] ← 0^GPRLEN
  else setGPR (reg rt) 0#32

/-- **SLTIU rt, rs, immediate** — MD00086 Vol II-A Rev 6.06, SLTIU, p.380.
```
if (0 || GPR[rs]) < (0 || sign_extend(immediate)) then
   GPR[rt] ← 0GPRLEN-1 || 1
else
   GPR[rt] ← 0GPRLEN
endif
``` -/
def SLTIU (rs rt imm : W32) : Pseudo Unit := do
  -- if (0 || GPR[rs]) < (0 || sign_extend(immediate)) then GPR[rt] ← 0^(GPRLEN-1) || 1
  if (0#1 ++ (← GPR (reg rs))).ult (0#1 ++ sign_extend (imm16 imm)) then
    setGPR (reg rt) ((0#31 ++ 1#1).setWidth 32)
  -- else GPR[rt] ← 0^GPRLEN
  else setGPR (reg rt) 0#32

/-- **ANDI rt, rs, immediate** — MD00086 Vol II-A Rev 6.06, ANDI, p.45.
```
GPR[rt] ← GPR[rs] and zero_extend(immediate)
``` -/
def ANDI (rs rt imm : W32) : Pseudo Unit := do
  -- GPR[rt] ← GPR[rs] and zero_extend(immediate)
  setGPR (reg rt) ((← GPR (reg rs)) &&& zero_extend (imm16 imm))

/-- **ORI rt, rs, immediate** — MD00086 Vol II-A Rev 6.06, ORI, p.315.
```
GPR[rt] ← GPR[rs] or zero_extend(immediate)
``` -/
def ORI (rs rt imm : W32) : Pseudo Unit := do
  -- GPR[rt] ← GPR[rs] or zero_extend(immediate)
  setGPR (reg rt) ((← GPR (reg rs)) ||| zero_extend (imm16 imm))

/-- **XORI rt, rs, immediate** — MD00086 Vol II-A Rev 6.06, XORI, p.447.
```
GPR[rt] ← GPR[rs] xor zero_extend(immediate)
``` -/
def XORI (rs rt imm : W32) : Pseudo Unit := do
  -- GPR[rt] ← GPR[rs] xor zero_extend(immediate)
  setGPR (reg rt) ((← GPR (reg rs)) ^^^ zero_extend (imm16 imm))

/-- **LUI rt, immediate** — MD00086 Vol II-A Rev 6.06, LUI, p.233 (pre-Release 6: `rs` field `00000`).
```
GPR[rt] ← immediate || 016
``` -/
def LUI (rt imm : W32) : Pseudo Unit := do
  -- GPR[rt] ← immediate || 0^16
  setGPR (reg rt) ((imm16 imm ++ 0#16).setWidth 32)

end Manual.Ops
