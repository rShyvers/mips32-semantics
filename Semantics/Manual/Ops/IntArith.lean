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

/-! ## Release 6: same-width multiply and divide, select, scaled address

`signed_word(x)` / `unsigned_word(x)` (p.301, p.169; not defined further by the manual) read the 32-bit
`x` as a signed / unsigned integer (`BitVec.toInt` / `BitVec.toNat`). "product is twice the width of
sources" (p.301): the integer product is taken as a 64-bit string (it fits: `|s1·s2| ≤ 2^62` signed,
`< 2^64` unsigned), `lo_word`/`hi_word` its bits 31..0 / 63..32. `div` / `mod` are "2's complement
integer division" / "2's complement modulo" (Table 1.1, p.5), defined on p.168: "(A div B)*B + (A mod
B) = A, where (A mod B) has same sign as the dividend A, and abs(A mod B) < abs(B)": truncated
division (`Int.tdiv`, `Int.tmod`; `Nat` `/`, `%` unsigned). `GPR[rd] ← quotient` keeps the low 32 bits
(GPRLEN = 32; `-2^31 div -1 = 2^31` keeps `0x8000_0000`). -/

/-- The 64-bit product string of two integers (`product ← s1 × s2`, MUL MUH MULU MUHU p.301). -/
def product64 (z : Int) : BitVec 64 := BitVec.ofInt 64 z

/-- `lo_word(product)` (p.301): bits 31..0. -/
def lo_word (p : BitVec 64) : W32 := p.extractLsb' 0 32

/-- `hi_word(product)` (p.301): bits 63..32. -/
def hi_word (p : BitVec 64) : W32 := p.extractLsb' 32 32

/-- **MUL rd, rs, rt** — MD00086 Vol II-A Rev 6.06, MUL MUH MULU MUHU, p.300 (diagram), p.301
(Operation).
```
s1 ← signed_word(GPR[rs])
s2 ← signed_word(GPR[rt])
product ← s1 × s2      /* product is twice the width of sources */
GPR[rd] ← lo_word( product )
``` -/
def MUL (rs rt rd : W32) : Pseudo Unit := do
  -- s1 ← signed_word(GPR[rs]); s2 ← signed_word(GPR[rt])
  let s1 := (← GPR (reg rs)).toInt
  let s2 := (← GPR (reg rt)).toInt
  -- product ← s1 × s2
  let product := product64 (s1 * s2)
  -- GPR[rd] ← lo_word( product )
  setGPR (reg rd) (lo_word product)

/-- **MUH rd, rs, rt** — MUL MUH MULU MUHU, p.301: as `MUL`, `GPR[rd] ← hi_word( product )`. -/
def MUH (rs rt rd : W32) : Pseudo Unit := do
  -- s1 ← signed_word(GPR[rs]); s2 ← signed_word(GPR[rt])
  let s1 := (← GPR (reg rs)).toInt
  let s2 := (← GPR (reg rt)).toInt
  -- product ← s1 × s2
  let product := product64 (s1 * s2)
  -- GPR[rd] ← hi_word( product )
  setGPR (reg rd) (hi_word product)

/-- **MULU rd, rs, rt** — MUL MUH MULU MUHU, p.301.
```
s1 ← unsigned_word(GPR[rs])
s2 ← unsigned_word(GPR[rt])
product ← s1 × s2
GPR[rd] ← lo_word( product )
``` -/
def MULU (rs rt rd : W32) : Pseudo Unit := do
  -- s1 ← unsigned_word(GPR[rs]); s2 ← unsigned_word(GPR[rt])
  let s1 := (← GPR (reg rs)).toNat
  let s2 := (← GPR (reg rt)).toNat
  -- product ← s1 × s2
  let product := product64 ((s1 * s2 : Nat) : Int)
  -- GPR[rd] ← lo_word( product )
  setGPR (reg rd) (lo_word product)

/-- **MUHU rd, rs, rt** — MUL MUH MULU MUHU, p.301: as `MULU`, `GPR[rd] ← hi_word( product )`. -/
def MUHU (rs rt rd : W32) : Pseudo Unit := do
  -- s1 ← unsigned_word(GPR[rs]); s2 ← unsigned_word(GPR[rt])
  let s1 := (← GPR (reg rs)).toNat
  let s2 := (← GPR (reg rt)).toNat
  -- product ← s1 × s2
  let product := product64 ((s1 * s2 : Nat) : Int)
  -- GPR[rd] ← hi_word( product )
  setGPR (reg rd) (hi_word product)

/-- The Restriction of DIV MOD DIVU MODU (p.168): "If the divisor in GPR rt is zero, the result value
is UNPREDICTABLE" (`Oracle.divByZero`, given the instruction `i` and the dividend `GPR[rs]`); otherwise
the value `v` the Operation computes is written: `GPR[rd] ← v`. -/
def divResult (i : Instruction) (rs rd : W32) (zero : Bool) (v : W32) : Pseudo Unit := do
  if zero then
    -- Restrictions (p.168): the divisor is zero, the result value is UNPREDICTABLE
    let o ← Pseudo.oracle
    let a ← Pseudo.get
    setGPR (reg rd) (o.divByZero a i (← GPR (reg rs)))
  else setGPR (reg rd) v

/-- **DIV rd, rs, rt** — MD00086 Vol II-A Rev 6.06, DIV MOD DIVU MODU, p.168 (diagram, Restrictions),
p.169 (Operation).
```
s1 ← signed_word(GPR[rs])
s2 ← signed_word(GPR[rt])
quotient ← s1 div s2
GPR[rd] ← quotient
``` -/
def DIV (rs rt rd : W32) : Pseudo Unit := do
  -- s1 ← signed_word(GPR[rs]); s2 ← signed_word(GPR[rt])
  let s1 := (← GPR (reg rs)).toInt
  let s2 := (← GPR (reg rt)).toInt
  -- quotient ← s1 div s2; GPR[rd] ← quotient
  divResult (.div rs rt rd) rs rd (s2 == 0) (BitVec.ofInt 32 (s1.tdiv s2))

/-- **MOD rd, rs, rt** — DIV MOD DIVU MODU, p.169: `remainder ← s1 mod s2`, `GPR[rd] ← remainder`
(signed). -/
def MOD (rs rt rd : W32) : Pseudo Unit := do
  -- s1 ← signed_word(GPR[rs]); s2 ← signed_word(GPR[rt])
  let s1 := (← GPR (reg rs)).toInt
  let s2 := (← GPR (reg rt)).toInt
  -- remainder ← s1 mod s2; GPR[rd] ← remainder
  divResult (.mod rs rt rd) rs rd (s2 == 0) (BitVec.ofInt 32 (s1.tmod s2))

/-- **DIVU rd, rs, rt** — DIV MOD DIVU MODU, p.169: `s1 ← unsigned_word(GPR[rs])`, `s2 ←
unsigned_word(GPR[rt])`, `quotient ← s1 div s2`, `GPR[rd] ← quotient`. -/
def DIVU (rs rt rd : W32) : Pseudo Unit := do
  -- s1 ← unsigned_word(GPR[rs]); s2 ← unsigned_word(GPR[rt])
  let s1 := (← GPR (reg rs)).toNat
  let s2 := (← GPR (reg rt)).toNat
  -- quotient ← s1 div s2; GPR[rd] ← quotient
  divResult (.divu rs rt rd) rs rd (s2 == 0) (BitVec.ofNat 32 (s1 / s2))

/-- **MODU rd, rs, rt** — DIV MOD DIVU MODU, p.169: `remainder ← s1 mod s2` (unsigned), `GPR[rd] ←
remainder`. -/
def MODU (rs rt rd : W32) : Pseudo Unit := do
  -- s1 ← unsigned_word(GPR[rs]); s2 ← unsigned_word(GPR[rt])
  let s1 := (← GPR (reg rs)).toNat
  let s2 := (← GPR (reg rt)).toNat
  -- remainder ← s1 mod s2; GPR[rd] ← remainder
  divResult (.modu rs rt rd) rs rd (s2 == 0) (BitVec.ofNat 32 (s1 % s2))

/-- **SELEQZ rd, rs, rt** — MD00086 Vol II-A Rev 6.06, SELEQZ SELNEZ, p.369.
```
SELEQZ: cond ← GPR[rt] = 0
if cond then
   tmp ← GPR[rs]
else
   tmp ← 0
endif
GPR[rd] ← tmp
``` -/
def SELEQZ (rs rt rd : W32) : Pseudo Unit := do
  -- cond ← GPR[rt] = 0
  let cond := (← GPR (reg rt)) == 0#32
  -- if cond then tmp ← GPR[rs] else tmp ← 0
  let tmp ← if cond then GPR (reg rs) else pure 0#32
  -- GPR[rd] ← tmp
  setGPR (reg rd) tmp

/-- **SELNEZ rd, rs, rt** — SELEQZ SELNEZ, p.369: `SELNEZ: cond ← GPR[rt] ≠ 0`, then as `SELEQZ`. -/
def SELNEZ (rs rt rd : W32) : Pseudo Unit := do
  -- cond ← GPR[rt] ≠ 0
  let cond := (← GPR (reg rt)) != 0#32
  -- if cond then tmp ← GPR[rs] else tmp ← 0
  let tmp ← if cond then GPR (reg rs) else pure 0#32
  -- GPR[rd] ← tmp
  setGPR (reg rd) tmp

/-- **LSA rd, rs, rt, sa** — MD00086 Vol II-A Rev 6.06, LSA, p.232.
```
GPR[rd] ← sign_extend.32( GPR[rs] << (sa+1) + GPR[rt] )
```
"The scaling shift is formed by adding 1 to the 2-bit sa field, which is interpreted as unsigned"
(Description, p.232); the shift binds tighter than the sum (Description: `(GPR[rs] << (sa+1)) +
GPR[rt]`). On a 32-bit CPU `sign_extend.32` of the 32-bit sum is the sum. -/
def LSA (rs rt rd sa : W32) : Pseudo Unit := do
  -- GPR[rd] ← sign_extend.32( GPR[rs] << (sa+1) + GPR[rt] )
  setGPR (reg rd) (sign_extend (((← GPR (reg rs)) <<< ((low sa 2).toNat + 1)) + (← GPR (reg rt))))

end Manual.Ops
