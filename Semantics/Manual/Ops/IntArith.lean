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

/-- **ADDU rd, rs, rt** — MD00086 Vol II-A Rev 6.06, ADDU, p.38.
```
temp ← GPR[rs] + GPR[rt]
GPR[rd] ← temp
``` -/
def ADDU (rs rt rd : W32) : Pseudo Unit := do
  -- temp ← GPR[rs] + GPR[rt]
  let temp := (← GPR (reg rs)) + (← GPR (reg rt))
  -- GPR[rd] ← temp
  setGPR (reg rd) temp

/-- **SUB rd, rs, rt** — MD00086 Vol II-A Rev 6.06, SUB, p.388.
```
temp ← (GPR[rs]31||GPR[rs]31..0) - (GPR[rt]31||GPR[rt]31..0)
if temp32 ≠ temp31 then
   SignalException(IntegerOverflow)
else
   GPR[rd] ← temp31..0
endif
``` -/
def SUB (rs rt rd : W32) : Pseudo Unit := do
  let x ← GPR (reg rs)
  let y ← GPR (reg rt)
  -- temp ← (GPR[rs]31||GPR[rs]31..0) - (GPR[rt]31||GPR[rt]31..0)
  let temp : BitVec 33 := (BitVec.ofBool (bit x 31) ++ x) - (BitVec.ofBool (bit y 31) ++ y)
  -- if temp32 ≠ temp31 then SignalException(IntegerOverflow)
  if bit temp 32 != bit temp 31 then SignalException .IntegerOverflow
  -- else GPR[rd] ← temp31..0
  else setGPR (reg rd) (low temp 32)

/-- **SUBU rd, rs, rt** — MD00086 Vol II-A Rev 6.06, SUBU, p.390.
```
temp ← GPR[rs] - GPR[rt]
GPR[rd] ← temp
``` -/
def SUBU (rs rt rd : W32) : Pseudo Unit := do
  -- temp ← GPR[rs] - GPR[rt]
  let temp := (← GPR (reg rs)) - (← GPR (reg rt))
  -- GPR[rd] ← temp
  setGPR (reg rd) temp

/-- **AND rd, rs, rt** — MD00086 Vol II-A Rev 6.06, AND, p.44.
```
GPR[rd] ← GPR[rs] and GPR[rt]
``` -/
def AND (rs rt rd : W32) : Pseudo Unit := do
  -- GPR[rd] ← GPR[rs] and GPR[rt]
  setGPR (reg rd) ((← GPR (reg rs)) &&& (← GPR (reg rt)))

/-- **OR rd, rs, rt** — MD00086 Vol II-A Rev 6.06, OR, p.314.
```
GPR[rd] ← GPR[rs] or GPR[rt]
``` -/
def OR (rs rt rd : W32) : Pseudo Unit := do
  -- GPR[rd] ← GPR[rs] or GPR[rt]
  setGPR (reg rd) ((← GPR (reg rs)) ||| (← GPR (reg rt)))

/-- **XOR rd, rs, rt** — MD00086 Vol II-A Rev 6.06, XOR, p.446.
```
GPR[rd] ← GPR[rs] xor GPR[rt]
``` -/
def XOR (rs rt rd : W32) : Pseudo Unit := do
  -- GPR[rd] ← GPR[rs] xor GPR[rt]
  setGPR (reg rd) ((← GPR (reg rs)) ^^^ (← GPR (reg rt)))

/-- **NOR rd, rs, rt** — MD00086 Vol II-A Rev 6.06, NOR, p.313.
```
GPR[rd] ← GPR[rs] nor GPR[rt]
``` -/
def NOR (rs rt rd : W32) : Pseudo Unit := do
  -- GPR[rd] ← GPR[rs] nor GPR[rt]
  setGPR (reg rd) (~~~((← GPR (reg rs)) ||| (← GPR (reg rt))))

/-- **SLT rd, rs, rt** — MD00086 Vol II-A Rev 6.06, SLT, p.378.
```
if GPR[rs] < GPR[rt] then
   GPR[rd] ← 0GPRLEN-1 || 1
else
   GPR[rd] ← 0GPRLEN
endif
```
The comparison is of signed integers (Description, p.378). -/
def SLT (rs rt rd : W32) : Pseudo Unit := do
  let x ← GPR (reg rs)
  let y ← GPR (reg rt)
  -- if GPR[rs] < GPR[rt] then GPR[rd] ← 0^(GPRLEN-1) || 1
  if x.slt y then setGPR (reg rd) ((0#31 ++ 1#1).setWidth 32)
  -- else GPR[rd] ← 0^GPRLEN
  else setGPR (reg rd) 0#32

/-- **SLTU rd, rs, rt** — MD00086 Vol II-A Rev 6.06, SLTU, p.381.
```
if (0 || GPR[rs]) < (0 || GPR[rt]) then
   GPR[rd] ← 0GPRLEN-1 || 1
else
   GPR[rd] ← 0GPRLEN
endif
``` -/
def SLTU (rs rt rd : W32) : Pseudo Unit := do
  let x ← GPR (reg rs)
  let y ← GPR (reg rt)
  -- if (0 || GPR[rs]) < (0 || GPR[rt]) then GPR[rd] ← 0^(GPRLEN-1) || 1
  if (0#1 ++ x).ult (0#1 ++ y) then setGPR (reg rd) ((0#31 ++ 1#1).setWidth 32)
  -- else GPR[rd] ← 0^GPRLEN
  else setGPR (reg rd) 0#32

/-- **MOVN rd, rs, rt** — MD00086 Vol II-A Rev 6.06, MOVN, p.279.
```
if GPR[rt] ≠ 0 then
   GPR[rd] ← GPR[rs]
endif
``` -/
def MOVN (rs rt rd : W32) : Pseudo Unit := do
  -- if GPR[rt] ≠ 0 then GPR[rd] ← GPR[rs] endif
  if (← GPR (reg rt)) != 0#32 then setGPR (reg rd) (← GPR (reg rs))

/-- **MOVZ rd, rs, rt** — MD00086 Vol II-A Rev 6.06, MOVZ, p.284.
```
if GPR[rt] = 0 then
   GPR[rd] ← GPR[rs]
endif
``` -/
def MOVZ (rs rt rd : W32) : Pseudo Unit := do
  -- if GPR[rt] = 0 then GPR[rd] ← GPR[rs] endif
  if (← GPR (reg rt)) == 0#32 then setGPR (reg rd) (← GPR (reg rs))

end Manual.Ops
