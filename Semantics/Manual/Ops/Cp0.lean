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
is its field table (`CPRWrite`). -/
def MTC0 (rt rd sel : W32) : Pseudo Unit := do
  -- data ← GPR[rt]
  let data ← GPR (reg rt)
  -- reg ← rd
  let r := rd.toNat
  -- if IsCoprocessorRegisterImplemented (0, reg, sel) then CPR[0,reg,sel] ← data
  if IsCoprocessorRegisterImplemented r sel.toNat then
    Pseudo.modify (CPRWrite r sel.toNat data)
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

/-- **RDPGPR rd, rt** — MD00086 Vol II-A Rev 6.06, RDPGPR, p.335 (MIPS32 Release 2).
```
GPR[rd] ← SGPR[SRSCtlPSS, rt]
```
"The normal GPRs are logically considered shadow set 0" (MD00090 Vol III Rev 6.02, Chapter 7, p.103),
so set `PSS = 0` is the current GPRs. `SRSCtl.HSS = 0` here (`Impl.SRSCtl`): no other set exists
(`Oracle.shadowSetUndefined`). -/
def RDPGPR (rd rt : W32) : Pseudo Unit := do
  let impl ← Pseudo.impl
  let o ← Pseudo.oracle
  let a ← Pseudo.get
  -- GPR[rd] ← SGPR[SRSCtlPSS, rt]
  if SRSCtlPSS impl == 0#4 then setGPR (reg rd) (← GPR (reg rt))
  else resolve (o.shadowSetUndefined a (.rdpgpr rd rt))

/-- **WRPGPR rd, rt** — MD00086 Vol II-A Rev 6.06, WRPGPR, p.444 (MIPS32 Release 2).
```
SGPR[SRSCtlPSS, rd] ← GPR[rt]
```
Set `PSS = 0` is the normal GPRs, as for `RDPGPR`. -/
def WRPGPR (rd rt : W32) : Pseudo Unit := do
  let impl ← Pseudo.impl
  let o ← Pseudo.oracle
  let a ← Pseudo.get
  -- SGPR[SRSCtlPSS, rd] ← GPR[rt]
  if SRSCtlPSS impl == 0#4 then setGPR (reg rd) (← GPR (reg rt))
  else resolve (o.shadowSetUndefined a (.wrpgpr rd rt))

end Manual.Ops
