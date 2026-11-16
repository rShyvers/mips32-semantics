import Semantics.Manual.Pseudocode

/-!
# Manual.Ops.CompactBranch — the Release 6 compact branches (MD00086 Vol II-A Rev 6.06)

Wave R6-3. The compact branches have no delay slot: a taken branch assigns `PC` at time `I`
(`setPC`). The conditional ones have a **forbidden slot** instead: "Release 6 introduces conditional
compact branches and compact jumps that do not have a delay slot; they have instead a forbidden slot.
Release 6 unconditional compact branches have neither a delay slot nor a forbidden slot" (MD00082 Vol
I-A Rev 6.01 §5.3.2, p.62). The slot is the instruction after a branch that is not taken ("If a
control transfer instruction (CTI) is placed in the forbidden slot of a compact branch, Release 6
implementations are required to signal a Reserved Instruction exception, but only when the branch is
not taken", B<cond>C, Restrictions, p.84; §5.3.2.4.4, p.63). The Operations below end in `CompactIf`:
`PC ← target` when the condition holds, else `ForbiddenSlot` (`Delay.forbiddenSlot`,
`Manual/Arch.lean`), which is the Restrictions section of the page, not a statement of its Operation.

The pages (printed pages): BC p.53, BALC p.52, B<cond>C p.82-85 (BEQC, BNEC, BLTC, BGEC, BLTUC,
BGEUC, BLTZC, BLEZC, BGEZC, BGTZC, BEQZC, BNEZC), B{LE,GE,GT,LT,EQ,NE}ZALC p.77-79, BOVC/BNVC
p.107-108. JIC and JIALC are in `Manual/Ops/Jump.lean`.

**Erratum (DECISIONS D11).** The B<cond>C Operation (p.84) computes `target_offset ←
sign_extend( offset || 0^2 )` and then writes `PC ← ( PC+4+ sign_extend( offset ) )`, which leaves
`target_offset` unused and would not shift the offset. The Description of the same page says "An
18/23-bit signed offset (the 16/21-bit offset field shifted left 2 bits) is added to the address of
the instruction following the branch (not the branch itself)" (p.83), and the B*ZALC page writes
`PC ← ( PC+4+ sign_extend( target_offset ) )` (p.78). The transcription uses `target_offset`.
Likewise BOVC/BNVC write `sign_extend( offset << 2 )` (p.108) for "A 18-bit signed offset (the 16-bit
offset field shifted left 2 bits)" (p.107): read as the 18-bit string `offset || 0^2`.
-/

namespace Manual.Ops

open Manual

/-- **The forbidden slot** of a conditional compact branch that is not taken (module doc): the
next instruction is in it (`Delay.forbiddenSlot`). From the Restrictions of the pages, not from an
Operation statement. -/
def ForbiddenSlot : Pseudo Unit := I1 .forbiddenSlot

/-- `if cond then PC ← ( PC+4+ target_offset ) endif` of a conditional compact branch, the forbidden
slot when not taken. `target_offset` is already sign-extended to `GPRLEN` (its
`sign_extend(target_offset)` is the identity). -/
def CompactIf (cond : Bool) (target_offset : W32) : Pseudo Unit := do
  let pc ← PC
  if cond then setPC (pc + 4#32 + target_offset) else ForbiddenSlot

/-! ## BC, BALC (p.53, p.52): no delay slot, no forbidden slot -/

/-- **BC offset** — MD00086 Vol II-A Rev 6.06, BC, p.53.
```
target_offset ← sign_extend( offset || 0^2 )
PC ← ( PC+4 + sign_extend(target_offset) )
```
-/
def BC (offset : W32) : Pseudo Unit := do
  -- target_offset ← sign_extend( offset || 0^2 )
  let target_offset := sign_extend (bits offset 25 0 ++ 0#2)
  -- PC ← ( PC+4 + sign_extend(target_offset) )
  let pc ← PC
  setPC (pc + 4#32 + sign_extend target_offset)

/-- **BALC offset** — MD00086 Vol II-A Rev 6.06, BALC, p.52.
```
target_offset ← sign_extend( offset || 0^2 )
GPR[31] ← PC+4
PC ← PC+4 + sign_extend(target_offset)
```
-/
def BALC (offset : W32) : Pseudo Unit := do
  -- target_offset ← sign_extend( offset || 0^2 )
  let target_offset := sign_extend (bits offset 25 0 ++ 0#2)
  let pc ← PC
  -- GPR[31] ← PC+4
  setGPR 31 (pc + 4#32)
  -- PC ← PC+4 + sign_extend(target_offset)
  setPC (pc + 4#32 + sign_extend target_offset)

/-! ## B<cond>C (p.82-85)

```
target_offset ← sign_extend( offset || 0^2 )
/* Register-register compare and branch, 16 bit offset: */
BEQC: cond ← GPR[rs] = GPR[rt]          BNEC: cond ← GPR[rs] ≠ GPR[rt]
BLTC: cond ← GPR[rs] < GPR[rt]          BGEC: cond ← GPR[rs] ≥ GPR[rt]
BLTUC: cond ← unsigned(GPR[rs]) < unsigned(GPR[rt])
BGEUC: cond ← unsigned(GPR[rs]) ≥ unsigned(GPR[rt])
/* Compare register to zero, small offset: */
BLTZC: cond ← GPR[rt] < 0     BLEZC: cond ← GPR[rt] ≤ 0
BGEZC: cond ← GPR[rt] ≥ 0     BGTZC: cond ← GPR[rt] > 0
/* Compare register to zero, large offset: */
BEQZC: cond ← GPR[rs] = 0     BNEZC: cond ← GPR[rs] ≠ 0
if cond then
  PC ← ( PC+4+ sign_extend( offset ) )      -- erratum: target_offset (module doc, D11)
end if
```
The signed comparisons are two's complement (`BitVec.slt`/`sle`); BLTUC/BGEUC compare unsigned
(`BitVec.ult`/`ule`). The offset is 16 bits except for BEQZC/BNEZC (21 bits, p.83). -/

/-- **BEQC rs, rt, offset** — B<cond>C, p.82-85. -/
def BEQC (rs rt offset : W32) : Pseudo Unit := do
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- BEQC: cond ← GPR[rs] = GPR[rt]
  let cond := (← GPR (reg rs)) == (← GPR (reg rt))
  CompactIf cond target_offset

/-- **BNEC rs, rt, offset** — B<cond>C, p.82-85. -/
def BNEC (rs rt offset : W32) : Pseudo Unit := do
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- BNEC: cond ← GPR[rs] ≠ GPR[rt]
  let cond := (← GPR (reg rs)) != (← GPR (reg rt))
  CompactIf cond target_offset

/-- **BLTC rs, rt, offset** — B<cond>C, p.82-85. -/
def BLTC (rs rt offset : W32) : Pseudo Unit := do
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- BLTC: cond ← GPR[rs] < GPR[rt]
  let cond := BitVec.slt (← GPR (reg rs)) (← GPR (reg rt))
  CompactIf cond target_offset

/-- **BGEC rs, rt, offset** — B<cond>C, p.82-85. -/
def BGEC (rs rt offset : W32) : Pseudo Unit := do
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- BGEC: cond ← GPR[rs] ≥ GPR[rt]
  let x ← GPR (reg rs)
  let y ← GPR (reg rt)
  let cond := BitVec.sle y x
  CompactIf cond target_offset

/-- **BLTUC rs, rt, offset** — B<cond>C, p.82-85. -/
def BLTUC (rs rt offset : W32) : Pseudo Unit := do
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- BLTUC: cond ← unsigned(GPR[rs]) < unsigned(GPR[rt])
  let cond := BitVec.ult (← GPR (reg rs)) (← GPR (reg rt))
  CompactIf cond target_offset

/-- **BGEUC rs, rt, offset** — B<cond>C, p.82-85. -/
def BGEUC (rs rt offset : W32) : Pseudo Unit := do
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- BGEUC: cond ← unsigned(GPR[rs]) ≥ unsigned(GPR[rt])
  let x ← GPR (reg rs)
  let y ← GPR (reg rt)
  let cond := BitVec.ule y x
  CompactIf cond target_offset

/-- **BLTZC rt, offset** — B<cond>C, p.82-85. -/
def BLTZC (rt offset : W32) : Pseudo Unit := do
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- BLTZC: cond ← GPR[rt] < 0
  let cond := BitVec.slt (← GPR (reg rt)) 0#32
  CompactIf cond target_offset

/-- **BLEZC rt, offset** — B<cond>C, p.82-85. -/
def BLEZC (rt offset : W32) : Pseudo Unit := do
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- BLEZC: cond ← GPR[rt] ≤ 0
  let cond := BitVec.sle (← GPR (reg rt)) 0#32
  CompactIf cond target_offset

/-- **BGEZC rt, offset** — B<cond>C, p.82-85. -/
def BGEZC (rt offset : W32) : Pseudo Unit := do
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- BGEZC: cond ← GPR[rt] ≥ 0
  let cond := BitVec.sle 0#32 (← GPR (reg rt))
  CompactIf cond target_offset

/-- **BGTZC rt, offset** — B<cond>C, p.82-85. -/
def BGTZC (rt offset : W32) : Pseudo Unit := do
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- BGTZC: cond ← GPR[rt] > 0
  let cond := BitVec.slt 0#32 (← GPR (reg rt))
  CompactIf cond target_offset

/-- **BEQZC rs, offset** — B<cond>C, p.82-85 (21-bit offset). -/
def BEQZC (rs offset : W32) : Pseudo Unit := do
  let target_offset := sign_extend (bits offset 20 0 ++ 0#2)
  -- BEQZC: cond ← GPR[rs] = 0
  let cond := (← GPR (reg rs)) == 0#32
  CompactIf cond target_offset

/-- **BNEZC rs, offset** — B<cond>C, p.82-85 (21-bit offset). -/
def BNEZC (rs offset : W32) : Pseudo Unit := do
  let target_offset := sign_extend (bits offset 20 0 ++ 0#2)
  -- BNEZC: cond ← GPR[rs] ≠ 0
  let cond := (← GPR (reg rs)) != 0#32
  CompactIf cond target_offset

/-! ## B{LE,GE,GT,LT,EQ,NE}ZALC (p.77-79)

```
GPR[31] ← PC+4
target_offset ← sign_extend( offset || 0^2 )
BLTZALC: cond ← GPR[rt] < 0     BLEZALC: cond ← GPR[rt] ≤ 0
BGEZALC: cond ← GPR[rt] ≥ 0     BGTZALC: cond ← GPR[rt] > 0
BEQZALC: cond ← GPR[rt] = 0     BNEZALC: cond ← GPR[rt] ≠ 0
if cond then
  PC ← ( PC+4+ sign_extend( target_offset ) )
endif
```
"The return address link is unconditionally updated" (p.77). Restrictions (p.78): "Branch-and-link
Restartability: GPR 31 must not be used for the source registers ... The result of executing such an
instruction is UNPREDICTABLE" (`Oracle.linkSourceIs31`). The statements run in the order written: the
link is written before `GPR[rt]` is read. -/

/-- The common body of the B*ZALC pages: link, then the condition `c` of `GPR[rt]`, then
`CompactIf`; `rt = 31` is UNPREDICTABLE (`Oracle.linkSourceIs31`), resolved for instruction `i`. -/
def BZALC (i : Instruction) (c : W32 → Bool) (rt offset : W32) : Pseudo Unit := do
  let o ← Pseudo.oracle
  let a ← Pseudo.get
  let body : Pseudo Unit := do
    let pc ← PC
    -- GPR[31] ← PC+4
    setGPR 31 (pc + 4#32)
    -- target_offset ← sign_extend( offset || 0^2 )
    let target_offset := sign_extend (imm16 offset ++ 0#2)
    -- cond ← <condition on GPR[rt]>
    let cond := c (← GPR (reg rt))
    -- if cond then PC ← ( PC+4+ sign_extend( target_offset ) ) endif
    CompactIf cond (sign_extend target_offset)
  -- Restrictions: rt = 31 is UNPREDICTABLE
  if reg rt == 31 then unpredictableOr (o.linkSourceIs31 a i) body else body

/-- **BLEZALC rt, offset** — p.77-79: `cond ← GPR[rt] ≤ 0`. -/
def BLEZALC (rt offset : W32) : Pseudo Unit :=
  BZALC (.blezalc rt offset) (fun x => BitVec.sle x 0#32) rt offset

/-- **BGEZALC rt, offset** — p.77-79: `cond ← GPR[rt] ≥ 0`. -/
def BGEZALC (rt offset : W32) : Pseudo Unit :=
  BZALC (.bgezalc rt offset) (fun x => BitVec.sle 0#32 x) rt offset

/-- **BGTZALC rt, offset** — p.77-79: `cond ← GPR[rt] > 0`. -/
def BGTZALC (rt offset : W32) : Pseudo Unit :=
  BZALC (.bgtzalc rt offset) (fun x => BitVec.slt 0#32 x) rt offset

/-- **BLTZALC rt, offset** — p.77-79: `cond ← GPR[rt] < 0`. -/
def BLTZALC (rt offset : W32) : Pseudo Unit :=
  BZALC (.bltzalc rt offset) (fun x => BitVec.slt x 0#32) rt offset

/-- **BEQZALC rt, offset** — p.77-79: `cond ← GPR[rt] = 0`. -/
def BEQZALC (rt offset : W32) : Pseudo Unit :=
  BZALC (.beqzalc rt offset) (fun x => x == 0#32) rt offset

/-- **BNEZALC rt, offset** — p.77-79: `cond ← GPR[rt] ≠ 0`. -/
def BNEZALC (rt offset : W32) : Pseudo Unit :=
  BZALC (.bnezalc rt offset) (fun x => x != 0#32) rt offset

/-! ## BOVC, BNVC (p.107-108)

```
temp1 ← GPR[rs]
temp2 ← GPR[rt]
tempd ← temp1 + temp2 // wider than 32-bit precision
sum_overflow ← (tempd32 ≠ tempd31)
BOVC: cond ← sum_overflow
BNVC: cond ← not( sum_overflow )
if cond then
  PC ← ( PC+4 + sign_extend( offset << 2 ) )
endif
```
"BOVC performs a signed 32-bit addition of rs and rt" (p.107): the 33-bit sum of the sign-extended
operands, as ADD (p.33). `offset << 2` is the 18-bit `offset || 0^2` (module doc). -/

/-- `sum_overflow` of BOVC/BNVC (p.108): the signed 32-bit addition overflows. -/
def SumOverflow (temp1 temp2 : W32) : Bool :=
  -- tempd ← temp1 + temp2 // wider than 32-bit precision
  let tempd : BitVec 33 := (BitVec.ofBool (bit temp1 31) ++ temp1) + (BitVec.ofBool (bit temp2 31) ++ temp2)
  -- sum_overflow ← (tempd32 ≠ tempd31)
  bit tempd 32 != bit tempd 31

/-- **BOVC rs, rt, offset** — BOVC, p.107-108. -/
def BOVC (rs rt offset : W32) : Pseudo Unit := do
  let temp1 ← GPR (reg rs)
  let temp2 ← GPR (reg rt)
  -- BOVC: cond ← sum_overflow
  let cond := SumOverflow temp1 temp2
  -- if cond then PC ← ( PC+4 + sign_extend( offset << 2 ) ) endif
  CompactIf cond (sign_extend (imm16 offset ++ 0#2))

/-- **BNVC rs, rt, offset** — BNVC, p.107-108. -/
def BNVC (rs rt offset : W32) : Pseudo Unit := do
  let temp1 ← GPR (reg rs)
  let temp2 ← GPR (reg rt)
  -- BNVC: cond ← not( sum_overflow )
  let cond := !SumOverflow temp1 temp2
  -- if cond then PC ← ( PC+4 + sign_extend( offset << 2 ) ) endif
  CompactIf cond (sign_extend (imm16 offset ++ 0#2))

end Manual.Ops
