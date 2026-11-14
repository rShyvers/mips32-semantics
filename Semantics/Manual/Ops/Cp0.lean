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

end Manual.Ops
