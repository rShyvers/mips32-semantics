import Semantics.Manual.Pseudocode

/-!
# Manual.Ops.Immediate — arithmetic and logical with a 16-bit immediate (MD00086 Vol II-A Rev 6.06)
-/

namespace Manual.Ops

open Manual

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

/-- **AUI rt, rs, immediate** — MD00086 Vol II-A Rev 6.06, AUI, p.47 (Release 6; "In Release 6, LUI is
an assembly idiom for AUI with rs=0").
```
GPR[rt] ← GPR[rs] + sign_extend(immediate << 16)
```
`immediate << 16` is the 32-bit string `immediate || 0^16` ("The 16 bit immediate is shifted left 16
bits, sign-extended, and added to the register rs", p.47). -/
def AUI (rs rt imm : W32) : Pseudo Unit := do
  -- GPR[rt] ← GPR[rs] + sign_extend(immediate << 16)
  setGPR (reg rt) ((← GPR (reg rs)) + sign_extend (imm16 imm ++ 0#16))

end Manual.Ops
