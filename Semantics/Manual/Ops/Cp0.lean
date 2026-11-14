import Semantics.Manual.CP0

/-!
# Manual.Ops.Cp0 — coprocessor 0 instructions (MD00086 Vol II-A Rev 6.06)

Sub-wave 7A transcribes the pilot `MTC0`. The Coprocessor Unusable check (outside Kernel Mode with
`Status.CU0 = 0`) is made for the whole COP0 encoding space before the Operation runs (MD00090 Vol III
Rev 6.02 §6.2.22, p.100; `Manual.Cycle`).
-/

namespace Manual.Ops

open Manual

/-- **MTC0 rt, rd, sel** — MD00086 Vol II-A Rev 6.06, MTC0, p.290-291, pre-Release 6 reading.
```
data ← GPR[rt]
reg ← rd
if IsCoprocessorRegisterImplemented (0, reg, sel) then
   CPR[0,reg,sel] ← data
   (Config5XPA = 1: no Config5 on this profile)
else
   if ArchitectureRevision() ≥ 6 then ... else UNDEFINED endif
endif
```
Restrictions (p.290): "Pre-Release 6: The results are UNDEFINED if coprocessor 0 does not contain a
register as specified by rd and sel" (`Oracle.cp0Undefined`). The effect of a write on each register
is its field table (`CPRWrite`); a write of a different Exception Base to `EBase` with `Status.BEV = 0`
is UNDEFINED (MD00090 Vol III Rev 6.02 §9.41, p.223; `Oracle.ebaseWriteBEV0`). -/
def MTC0 (rt rd sel : W32) : Pseudo Unit := do
  -- data ← GPR[rt]
  let data ← GPR (reg rt)
  -- reg ← rd
  let r := rd.toNat
  -- if IsCoprocessorRegisterImplemented (0, reg, sel) then CPR[0,reg,sel] ← data
  if IsCoprocessorRegisterImplemented r sel.toNat then
    let a ← Pseudo.get
    let o ← Pseudo.oracle
    let write := Pseudo.modify (CPRWrite r sel.toNat data)
    -- EBase (15, 1): "The operation of the processor is UNDEFINED if the Exception Base field is
    -- written with a different value when StatusBEV is 0" (Vol III §9.41, p.223)
    if r == 15 && sel.toNat == 1 && !StatusBEV a && bits data 29 12 != bits a.EBase 29 12 then
      unpredictableOr (o.ebaseWriteBEV0 a data) write
    else write
  -- else UNDEFINED
  else
    let o ← Pseudo.oracle
    let a ← Pseudo.get
    resolve (o.cp0Undefined a (.mtc0 rt rd sel))

-- 7B S3 control + system

/-- `SRSCtl_{PSS}` (bits 9..6; MD00090 Vol III Rev 6.02, SRSCtl, Table 9.49, p.204): the previous
shadow set number, as `SRSCtl` reads under `impl`. -/
def SRSCtlPSS (i : Impl) : BitVec 4 := bits i.SRSCtl 9 6

/-- **MFC0 rt, rd, sel** — MD00086 Vol II-A Rev 6.06, MFC0, p.266, pre-Release 6 reading.
```
reg = rd
if IsCoprocessorRegisterImplemented(0, reg, sel) then
   data ← CPR[0, reg, sel]
   GPR[rt] ← data
else
   if ArchitectureRevision() ≥ 6 then GPR[rt] ← 0 else UNDEFINED endif
endif
```
Restrictions (p.266): "Pre-Release 6: The results are UNDEFINED if coprocessor 0 does not contain a
register as specified by rd and sel" (`Oracle.cp0Undefined`). -/
def MFC0 (rt rd sel : W32) : Pseudo Unit := do
  let impl ← Pseudo.impl
  let a ← Pseudo.get
  -- reg = rd
  let r := rd.toNat
  -- if IsCoprocessorRegisterImplemented(0, reg, sel) then
  if IsCoprocessorRegisterImplemented r sel.toNat then
    -- data ← CPR[0, reg, sel]
    let data := CPRRead impl r sel.toNat a
    -- GPR[rt] ← data
    setGPR (reg rt) data
  -- else UNDEFINED
  else
    let o ← Pseudo.oracle
    resolve (o.cp0Undefined a (.mfc0 rt rd sel))

/-- **DI rt** — MD00086 Vol II-A Rev 6.06, DI, p.164 (MIPS32 Release 2). `DI` without an argument is
`DI r0` ("GPR r0 is implied, which discards the previous value of the Status register").
```
data ← Status
GPR[rt] ← data
StatusIE ← 0
```
(The page gives this Operation for the general interrupt enable/disable with `sc` a variable; DI is
`sc = 0`.) The Coprocessor Unusable check is made for the whole COP0 encoding space (module doc of
`Manual.Ops.Cp0`). -/
def DI (rt : W32) : Pseudo Unit := do
  let a ← Pseudo.get
  -- data ← Status
  let data := a.Status
  -- GPR[rt] ← data
  setGPR (reg rt) data
  -- StatusIE ← 0
  Pseudo.modify fun a => { a with Status := a.Status &&& ~~~(1#32 <<< 0) }

/-- **EI rt** — MD00086 Vol II-A Rev 6.06, EI, p.176 (MIPS32 Release 2). `EI` without an argument is
`EI r0`.
```
data ← Status
GPR[rt] ← data
StatusIE ← 1
```
(`sc = 1` of the page's general Operation.) -/
def EI (rt : W32) : Pseudo Unit := do
  let a ← Pseudo.get
  -- data ← Status
  let data := a.Status
  -- GPR[rt] ← data
  setGPR (reg rt) data
  -- StatusIE ← 1
  Pseudo.modify fun a => { a with Status := a.Status ||| (1#32 <<< 0) }

/-- `SGPR[s, r]`, register `r` of shadow set `s`. "The normal GPRs are logically considered shadow set
0" (MD00090 Vol III Rev 6.02, Chapter 7, p.103); with `SRSCtl.HSS = 0` "only the normal GPRs are
implemented" (Table 9.49, p.203), which `Impl.WF` requires, so set 0 is the only set and every
`SRSCtl` set field reads 0 (`PSS`, `Impl.WF`). The spec's state has no other set: an `s ≠ 0` (an
implementation outside `Impl.WF`) also reads the normal GPRs. -/
def SGPR (_s : BitVec 4) (r : Fin 32) : Pseudo W32 := GPR r

/-- `SGPR[s, r] ← v` (set 0 only, as `SGPR`). -/
def setSGPR (_s : BitVec 4) (r : Fin 32) (v : W32) : Pseudo Unit := setGPR r v

/-- **RDPGPR rd, rt** — MD00086 Vol II-A Rev 6.06, RDPGPR, p.335 (MIPS32 Release 2).
```
GPR[rd] ← SGPR[SRSCtlPSS, rt]
```
`SRSCtl.PSS = 0` under `Impl.WF`: set 0 is the normal GPRs (`SGPR`). -/
def RDPGPR (rd rt : W32) : Pseudo Unit := do
  let impl ← Pseudo.impl
  -- GPR[rd] ← SGPR[SRSCtlPSS, rt]
  setGPR (reg rd) (← SGPR (SRSCtlPSS impl) (reg rt))

/-- **WRPGPR rd, rt** — MD00086 Vol II-A Rev 6.06, WRPGPR, p.444 (MIPS32 Release 2).
```
SGPR[SRSCtlPSS, rd] ← GPR[rt]
```
As `RDPGPR`: set 0 is the normal GPRs. -/
def WRPGPR (rd rt : W32) : Pseudo Unit := do
  let impl ← Pseudo.impl
  -- SGPR[SRSCtlPSS, rd] ← GPR[rt]
  setSGPR (SRSCtlPSS impl) (reg rd) (← GPR (reg rt))

end Manual.Ops
