import Semantics.Manual.Pseudocode

/-!
# Manual.Ops.Shift — shifts and rotates (MD00086 Vol II-A Rev 6.06)

The shift amount `s` is the 5-bit `sa` field or `GPR[rs]4..0`. `x^s` with `s = 0` is the empty
string, so a result is built as `low x n ++ …` at the dependent width and cut to 32 bits.
-/

namespace Manual.Ops

open Manual

/-- `ArchitectureRevision()` (MD00086 Vol II-A Rev 6.06 §2.2.2.1, p.20): the target is Release 2. -/
private def ArchitectureRevision : Nat := 2

/-- **SLL rd, rt, sa** — MD00086 Vol II-A Rev 6.06, SLL, p.376.
```
s ← sa
temp ← GPR[rt](31-s)..0 || 0s
GPR[rd] ← temp
``` -/
def SLL (rd rt sa : W32) : Pseudo Unit := do
  -- s ← sa
  let s := (low sa 5).toNat
  -- temp ← GPR[rt](31-s)..0 || 0^s
  let temp : W32 := (low (← GPR (reg rt)) (32 - s) ++ 0#s).setWidth 32
  -- GPR[rd] ← temp
  setGPR (reg rd) temp

/-- **SRL rd, rt, sa** — MD00086 Vol II-A Rev 6.06, SRL, p.385.
```
s ← sa
temp ← 0s || GPR[rt]31..s
GPR[rd] ← temp
``` -/
def SRL (rd rt sa : W32) : Pseudo Unit := do
  -- s ← sa
  let s := (low sa 5).toNat
  -- temp ← 0^s || GPR[rt]31..s
  let temp : W32 := (0#s ++ bits (← GPR (reg rt)) 31 s).setWidth 32
  -- GPR[rd] ← temp
  setGPR (reg rd) temp

/-- **SRA rd, rt, sa** — MD00086 Vol II-A Rev 6.06, SRA, p.383.
```
s ← sa
temp ← (GPR[rt]31)s || GPR[rt]31..s
GPR[rd] ← temp
``` -/
def SRA (rd rt sa : W32) : Pseudo Unit := do
  let x ← GPR (reg rt)
  -- s ← sa
  let s := (low sa 5).toNat
  -- temp ← (GPR[rt]31)^s || GPR[rt]31..s
  let temp : W32 := (BitVec.fill s (bit x 31) ++ bits x 31 s).setWidth 32
  -- GPR[rd] ← temp
  setGPR (reg rd) temp

/-- **SLLV rd, rt, rs** — MD00086 Vol II-A Rev 6.06, SLLV, p.377.
```
s ← GPR[rs]4..0
temp ← GPR[rt](31-s)..0 || 0s
GPR[rd] ← temp
``` -/
def SLLV (rd rt rs : W32) : Pseudo Unit := do
  -- s ← GPR[rs]4..0
  let s := (low (← GPR (reg rs)) 5).toNat
  -- temp ← GPR[rt](31-s)..0 || 0^s
  let temp : W32 := (low (← GPR (reg rt)) (32 - s) ++ 0#s).setWidth 32
  -- GPR[rd] ← temp
  setGPR (reg rd) temp

/-- **SRLV rd, rt, rs** — MD00086 Vol II-A Rev 6.06, SRLV, p.386.
```
s ← GPR[rs]4..0
temp ← 0s || GPR[rt]31..s
GPR[rd] ← temp
``` -/
def SRLV (rd rt rs : W32) : Pseudo Unit := do
  -- s ← GPR[rs]4..0
  let s := (low (← GPR (reg rs)) 5).toNat
  -- temp ← 0^s || GPR[rt]31..s
  let temp : W32 := (0#s ++ bits (← GPR (reg rt)) 31 s).setWidth 32
  -- GPR[rd] ← temp
  setGPR (reg rd) temp

/-- **SRAV rd, rt, rs** — MD00086 Vol II-A Rev 6.06, SRAV, p.384.
```
s ← GPR[rs]4..0
temp ← (GPR[rt]31)s || GPR[rt]31..s
GPR[rd] ← temp
``` -/
def SRAV (rd rt rs : W32) : Pseudo Unit := do
  let x ← GPR (reg rt)
  -- s ← GPR[rs]4..0
  let s := (low (← GPR (reg rs)) 5).toNat
  -- temp ← (GPR[rt]31)^s || GPR[rt]31..s
  let temp : W32 := (BitVec.fill s (bit x 31) ++ bits x 31 s).setWidth 32
  -- GPR[rd] ← temp
  setGPR (reg rd) temp

/-- **ROTR rd, rt, sa** — MD00086 Vol II-A Rev 6.06, ROTR, p.339.
```
if ((ArchitectureRevision() < 2) and (Config3SM = 0)) then
   UNPREDICTABLE
endif
s ← sa
temp ← GPR[rt]s-1..0 || GPR[rt]31..s
GPR[rd] ← temp
```
The printed 6.06 text lost the relational operator of the first line (`ArchitectureRevision()  2`);
Rev 2.50 prints it as `<` (MD00086 Vol II Rev 2.50, ROTR, Operation). With `ArchitectureRevision() = 2`
(the target is Release 2) the test is false, so the UNPREDICTABLE branch is unreachable and `Config3.SM`
(SmartMIPS) is not needed; the branch is written as `resolve .proceed`. -/
def ROTR (rd rt sa : W32) : Pseudo Unit := do
  -- if ((ArchitectureRevision() < 2) and (Config3SM = 0)) then UNPREDICTABLE endif
  if ArchitectureRevision < 2 then resolve .proceed
  let x ← GPR (reg rt)
  -- s ← sa
  let s := (low sa 5).toNat
  -- temp ← GPR[rt]s-1..0 || GPR[rt]31..s
  let temp : W32 := (low x s ++ bits x 31 s).setWidth 32
  -- GPR[rd] ← temp
  setGPR (reg rd) temp

/-- **ROTRV rd, rt, rs** — MD00086 Vol II-A Rev 6.06, ROTRV, p.340.
```
if ((ArchitectureRevision() < 2) and (Config3SM = 0)) then
   UNPREDICTABLE
endif
s ← GPR[rs]4..0
temp ← GPR[rt]s-1..0 || GPR[rt]31..s
GPR[rd] ← temp
```
The condition is as for `ROTR`. -/
def ROTRV (rd rt rs : W32) : Pseudo Unit := do
  -- if ((ArchitectureRevision() < 2) and (Config3SM = 0)) then UNPREDICTABLE endif
  if ArchitectureRevision < 2 then resolve .proceed
  let x ← GPR (reg rt)
  -- s ← GPR[rs]4..0
  let s := (low (← GPR (reg rs)) 5).toNat
  -- temp ← GPR[rt]s-1..0 || GPR[rt]31..s
  let temp : W32 := (low x s ++ bits x 31 s).setWidth 32
  -- GPR[rd] ← temp
  setGPR (reg rd) temp

end Manual.Ops
