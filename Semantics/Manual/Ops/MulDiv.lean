import Semantics.Manual.Pseudocode

/-!
# Manual.Ops.MulDiv — multiply, divide, multiply-accumulate, HI/LO moves (MD00086 Vol II-A Rev 6.06)

`x × y` is read at 64 bits: signed (`signExtend`) for `MULT`, `MADD`, `MSUB`, `MUL`, unsigned
(`0 ||`) for the `U` forms. `div` and `mod` are "2's complement integer division" and "2's
complement modulo" (Table 1.1, p.5): the quotient truncates toward zero and the remainder takes the
sign of the dividend (`BitVec.sdiv`, `BitVec.srem`); the manual does not say more (SPEC-NOTES §11).
-/

namespace Manual.Ops

open Manual

/-- **MULT rs, rt** — MD00086 Vol II-A Rev 6.06, MULT, p.303.
```
prod ← GPR[rs]31..0 × GPR[rt]31..0
LO ← prod31..0
HI ← prod63..32
``` -/
def MULT (rs rt : W32) : Pseudo Unit := do
  -- prod ← GPR[rs]31..0 × GPR[rt]31..0   (signed)
  let prod : BitVec 64 := (← GPR (reg rs)).signExtend 64 * (← GPR (reg rt)).signExtend 64
  -- LO ← prod31..0
  setLO (low prod 32)
  -- HI ← prod63..32
  setHI (bits prod 63 32)

/-- **MULTU rs, rt** — MD00086 Vol II-A Rev 6.06, MULTU, p.304.
```
prod ← (0 || GPR[rs]31..0) × (0 || GPR[rt]31..0)
LO ← prod31..0
HI ← prod63..32
``` -/
def MULTU (rs rt : W32) : Pseudo Unit := do
  -- prod ← (0 || GPR[rs]31..0) × (0 || GPR[rt]31..0)
  let prod : BitVec 64 := (← GPR (reg rs)).zeroExtend 64 * (← GPR (reg rt)).zeroExtend 64
  -- LO ← prod31..0
  setLO (low prod 32)
  -- HI ← prod63..32
  setHI (bits prod 63 32)

/-- **DIV rs, rt** — MD00086 Vol II-A Rev 6.06, DIV, p.165.
```
q ← GPR[rs]31..0 div GPR[rt]31..0
LO ← q
r ← GPR[rs]31..0 mod GPR[rt]31..0
HI ← r
```
Restrictions (p.165): "If the divisor in GPR rt is zero, the arithmetic result value is
UNPREDICTABLE" (`Oracle.divByZero`; no exception: "No arithmetic exception occurs under any
circumstances"). `q` has 33 bits (`-2^31 div -1 = 2^31`), `LO ← q` keeps the low 32. -/
def DIV (rs rt : W32) : Pseudo Unit := do
  let x ← GPR (reg rs)
  let y ← GPR (reg rt)
  if y == 0#32 then
    -- Restrictions: the divisor is zero, the arithmetic result value is UNPREDICTABLE
    let o ← Pseudo.oracle
    let a ← Pseudo.get
    setHI (o.divByZero a).1
    setLO (o.divByZero a).2
  else
    -- q ← GPR[rs]31..0 div GPR[rt]31..0
    let q : BitVec 33 := BitVec.sdiv (x.signExtend 33) (y.signExtend 33)
    -- LO ← q
    setLO (low q 32)
    -- r ← GPR[rs]31..0 mod GPR[rt]31..0
    let r : BitVec 33 := BitVec.srem (x.signExtend 33) (y.signExtend 33)
    -- HI ← r
    setHI (low r 32)

/-- **DIVU rs, rt** — MD00086 Vol II-A Rev 6.06, DIVU, p.171.
```
q ← (0 || GPR[rs]31..0) div (0 || GPR[rt]31..0)
r ← (0 || GPR[rs]31..0) mod (0 || GPR[rt]31..0)
LO ← sign_extend(q31..0)
HI ← sign_extend(r31..0)
```
Restrictions (p.171): "If the divisor in GPR rt is zero, the arithmetic result value is
UNPREDICTABLE" (`Oracle.divuByZero`). -/
def DIVU (rs rt : W32) : Pseudo Unit := do
  let x ← GPR (reg rs)
  let y ← GPR (reg rt)
  if y == 0#32 then
    -- Restrictions: the divisor is zero, the arithmetic result value is UNPREDICTABLE
    let o ← Pseudo.oracle
    let a ← Pseudo.get
    setHI (o.divuByZero a).1
    setLO (o.divuByZero a).2
  else
    -- q ← (0 || GPR[rs]31..0) div (0 || GPR[rt]31..0)
    let q : BitVec 33 := (0#1 ++ x) / (0#1 ++ y)
    -- r ← (0 || GPR[rs]31..0) mod (0 || GPR[rt]31..0)
    let r : BitVec 33 := (0#1 ++ x) % (0#1 ++ y)
    -- LO ← sign_extend(q31..0)
    setLO (sign_extend (low q 32))
    -- HI ← sign_extend(r31..0)
    setHI (sign_extend (low r 32))

/-- **MFHI rd** — MD00086 Vol II-A Rev 6.06, MFHI, p.273.
```
GPR[rd] ← HI
``` -/
def MFHI (rd : W32) : Pseudo Unit := do
  -- GPR[rd] ← HI
  setGPR (reg rd) (← HI)

/-- **MFLO rd** — MD00086 Vol II-A Rev 6.06, MFLO, p.274.
```
GPR[rd] ← LO
``` -/
def MFLO (rd : W32) : Pseudo Unit := do
  -- GPR[rd] ← LO
  setGPR (reg rd) (← LO)

/-- **MTHI rs** — MD00086 Vol II-A Rev 6.06, MTHI, p.297.
```
HI ← GPR[rs]
```
The Restrictions (p.297: after DIV/DIVU/MULT/MULTU and before MFLO/MFHI the contents of LO are
UNPREDICTABLE) depend on the history of the program, which the architectural state does not carry; they
are not modelled (SPEC-NOTES §11). -/
def MTHI (rs : W32) : Pseudo Unit := do
  -- HI ← GPR[rs]
  setHI (← GPR (reg rs))

/-- **MTLO rs** — MD00086 Vol II-A Rev 6.06, MTLO, p.298.
```
LO ← GPR[rs]
```
The Restrictions (p.298) are not modelled, as for `MTHI`. -/
def MTLO (rs : W32) : Pseudo Unit := do
  -- LO ← GPR[rs]
  setLO (← GPR (reg rs))

/-- **MUL rd, rs, rt** — MD00086 Vol II-A Rev 6.06, MUL, p.299.
```
temp ← GPR[rs] × GPR[rt]
GPR[rd] ← temp31..0
HI ← UNPREDICTABLE
LO ← UNPREDICTABLE
```
`HI`/`LO` are `Oracle.mulHILO`. -/
def MUL (rs rt rd : W32) : Pseudo Unit := do
  -- temp ← GPR[rs] × GPR[rt]   (signed, 64 bits)
  let temp : BitVec 64 := (← GPR (reg rs)).signExtend 64 * (← GPR (reg rt)).signExtend 64
  -- GPR[rd] ← temp31..0
  setGPR (reg rd) (low temp 32)
  let o ← Pseudo.oracle
  let a ← Pseudo.get
  -- HI ← UNPREDICTABLE
  setHI (o.mulHILO a).1
  -- LO ← UNPREDICTABLE
  setLO (o.mulHILO a).2

/-- **MADD rs, rt** — MD00086 Vol II-A Rev 6.06, MADD, p.255.
```
temp ← (HI || LO) + (GPR[rs] × GPR[rt])
HI ← temp63..32
LO ← temp31..0
``` -/
def MADD (rs rt : W32) : Pseudo Unit := do
  -- temp ← (HI || LO) + (GPR[rs] × GPR[rt])   (signed product)
  let temp : BitVec 64 :=
    ((← HI) ++ (← LO)) + ((← GPR (reg rs)).signExtend 64 * (← GPR (reg rt)).signExtend 64)
  -- HI ← temp63..32
  setHI (bits temp 63 32)
  -- LO ← temp31..0
  setLO (low temp 32)

/-- **MADDU rs, rt** — MD00086 Vol II-A Rev 6.06, MADDU, p.261.
```
temp ← (HI || LO) + (GPR[rs] × GPR[rt])
HI ← temp63..32
LO ← temp31..0
```
Both operands are unsigned (Description, p.261). -/
def MADDU (rs rt : W32) : Pseudo Unit := do
  -- temp ← (HI || LO) + (GPR[rs] × GPR[rt])   (unsigned product)
  let temp : BitVec 64 :=
    ((← HI) ++ (← LO)) + ((← GPR (reg rs)).zeroExtend 64 * (← GPR (reg rt)).zeroExtend 64)
  -- HI ← temp63..32
  setHI (bits temp 63 32)
  -- LO ← temp31..0
  setLO (low temp 32)

/-- **MSUB rs, rt** — MD00086 Vol II-A Rev 6.06, MSUB, p.286.
```
temp ← (HI || LO) - (GPR[rs] × GPR[rt])
HI ← temp63..32
LO ← temp31..0
``` -/
def MSUB (rs rt : W32) : Pseudo Unit := do
  -- temp ← (HI || LO) - (GPR[rs] × GPR[rt])   (signed product)
  let temp : BitVec 64 :=
    ((← HI) ++ (← LO)) - ((← GPR (reg rs)).signExtend 64 * (← GPR (reg rt)).signExtend 64)
  -- HI ← temp63..32
  setHI (bits temp 63 32)
  -- LO ← temp31..0
  setLO (low temp 32)

/-- **MSUBU rs, rt** — MD00086 Vol II-A Rev 6.06, MSUBU, p.289.
```
temp ← (HI || LO) - (GPR[rs] × GPR[rt])
HI ← temp63..32
LO ← temp31..0
```
Both operands are unsigned (Description, p.289). -/
def MSUBU (rs rt : W32) : Pseudo Unit := do
  -- temp ← (HI || LO) - (GPR[rs] × GPR[rt])   (unsigned product)
  let temp : BitVec 64 :=
    ((← HI) ++ (← LO)) - ((← GPR (reg rs)).zeroExtend 64 * (← GPR (reg rt)).zeroExtend 64)
  -- HI ← temp63..32
  setHI (bits temp 63 32)
  -- LO ← temp31..0
  setLO (low temp 32)

end Manual.Ops
