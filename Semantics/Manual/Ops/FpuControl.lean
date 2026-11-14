import Semantics.Manual.FPU

/-!
# Manual.Ops.FpuControl — FP control register moves (MD00086 Vol II-A Rev 6.06), 7B S4

`CFC1` and `CTC1`, read for pre-Release 6, Release 2 (the profile). The Release 5 `UFR`/`UNFR`
aliases (`fs` = 1, 4) and the Release 6 `FRE`/`NFRE` aliases (`fs` = 5, 6) need `Config5` and
`FIR.UFRP`, which this profile does not have (no `Config5`, `FIR.UFRP = 0`): they name no register
that exists, so they take the `else` arm of the Operation ("Prior to Release 6, the result is
UNPREDICTABLE if fs specifies a register that does not exist", CFC1 p.129, CTC1 p.149). The pre-
Release 6 Operation without those aliases is MD00086 Rev 2.50 p.106 (CTC1), the Rev 6.06 text is
used for the conditions. `ConfigAR >= 2` tests are Release 6 only (false here).
-/

namespace Manual.Ops

open Manual

/-- **CFC1 rt, fs** — MD00086 Vol II-A Rev 6.06, CFC1, p.129-130.
```
if fs = 0 then temp <- FIR
elseif fs = 25 then /* FCCR */  temp <- 0^24 || FCSR31..25 || FCSR23
elseif fs = 26 then /* FEXR */  temp <- 0^14 || FCSR17..12 || 0^5 || FCSR6..2 || 0^2
elseif fs = 28 then /* FENR */  temp <- 0^20 || FCSR11..7 || 0^4 || FCSR24 || FCSR1..0
elseif fs = 31 then /* FCSR */  temp <- FCSR
else temp <- UNPREDICTABLE
endif
GPR[rt] <- temp
```
(The Release 5/6 alias arms, see the module doc, are omitted.) -/
def CFC1 (rt fs : W32) : Pseudo Unit := do
  let a ← Pseudo.get
  let o ← Pseudo.oracle
  let i ← Pseudo.impl
  -- if fs = 0 then temp <- FIR
  let temp : W32 :=
    if fs == 0#32 then i.FIR
    -- elseif fs = 25 then temp <- 0^24 || FCSR31..25 || FCSR23
    else if fs == 25#32 then
      (0#24 ++ a.FCSR.extractLsb' 25 7 ++ BitVec.ofBool (bit a.FCSR 23) : BitVec 32)
    -- elseif fs = 26 then temp <- 0^14 || FCSR17..12 || 0^5 || FCSR6..2 || 0^2
    else if fs == 26#32 then
      (0#14 ++ a.FCSR.extractLsb' 12 6 ++ 0#5 ++ a.FCSR.extractLsb' 2 5 ++ 0#2 : BitVec 32)
    -- elseif fs = 28 then temp <- 0^20 || FCSR11..7 || 0^4 || FCSR24 || FCSR1..0
    else if fs == 28#32 then
      (0#20 ++ a.FCSR.extractLsb' 7 5 ++ 0#4 ++ BitVec.ofBool (bit a.FCSR 24) ++
        a.FCSR.extractLsb' 0 2 : BitVec 32)
    -- elseif fs = 31 then temp <- FCSR
    else if fs == 31#32 then a.FCSR
    -- else temp <- UNPREDICTABLE
    else o.cfc1Unpredictable a fs
  -- GPR[rt] <- temp
  setGPR (reg rt) temp

/-- **CTC1 rt, fs** — MD00086 Vol II-A Rev 6.06, CTC1, p.149-151.
```
temp <- GPR[rt]31..0
if fs = 25 then /* FCCR */
   if temp31..8 != 0^24 then UNPREDICTABLE
   else FCSR <- temp7..1 || FCSR24 || temp0 || FCSR22..0 endif
elseif fs = 26 then /* FEXR */
   if temp31..18 != 0 or temp11..7 != 0 or temp2..0 != 0 then UNPREDICTABLE
   else FCSR <- FCSR31..18 || temp17..12 || FCSR11..7 || temp6..2 || FCSR1..0 endif
elseif fs = 28 then /* FENR */
   if temp31..12 != 0 or temp6..3 != 0 then UNPREDICTABLE
   else FCSR <- FCSR31..25 || temp2 || FCSR23..12 || temp11..7 || FCSR6..2 || temp1..0 endif
elseif fs = 31 then /* FCSR */
   if (FCSRImpl field is not implemented) and (temp22..18 != 0) then UNPREDICTABLE
   else FCSR <- temp endif
else UNPREDICTABLE
endif
CheckFPException()
```
`FCSR.Impl` is not implemented (bits 22..18 read 0). "The register is written before the exception
occurs" (Description, p.149): `CheckFPException` follows the write. The `UNPREDICTABLE` arms are
`Oracle.ctc1Unpredictable`. -/
def CTC1 (rt fs : W32) : Pseudo Unit := do
  let o ← Pseudo.oracle
  -- temp <- GPR[rt]31..0
  let temp := low (← GPR (reg rt)) 32
  -- if fs = 25 then
  if fs == 25#32 then
    if bits temp 31 8 != 0#24 then
      -- UNPREDICTABLE
      Pseudo.modify fun a => { a with FCSR := o.ctc1Unpredictable a fs temp }
    else
      -- FCSR <- temp7..1 || FCSR24 || temp0 || FCSR22..0
      Pseudo.modify fun a => { a with FCSR :=
        (bits temp 7 1 ++ BitVec.ofBool (bit a.FCSR 24) ++ BitVec.ofBool (bit temp 0) ++
          bits a.FCSR 22 0 : BitVec 32) }
  -- elseif fs = 26 then
  else if fs == 26#32 then
    if bits temp 31 18 != 0#14 || bits temp 11 7 != 0#5 || bits temp 2 0 != 0#3 then
      -- UNPREDICTABLE
      Pseudo.modify fun a => { a with FCSR := o.ctc1Unpredictable a fs temp }
    else
      -- FCSR <- FCSR31..18 || temp17..12 || FCSR11..7 || temp6..2 || FCSR1..0
      Pseudo.modify fun a => { a with FCSR :=
        (bits a.FCSR 31 18 ++ bits temp 17 12 ++ bits a.FCSR 11 7 ++ bits temp 6 2 ++
          bits a.FCSR 1 0 : BitVec 32) }
  -- elseif fs = 28 then
  else if fs == 28#32 then
    if bits temp 31 12 != 0#20 || bits temp 6 3 != 0#4 then
      -- UNPREDICTABLE
      Pseudo.modify fun a => { a with FCSR := o.ctc1Unpredictable a fs temp }
    else
      -- FCSR <- FCSR31..25 || temp2 || FCSR23..12 || temp11..7 || FCSR6..2 || temp1..0
      Pseudo.modify fun a => { a with FCSR :=
        (bits a.FCSR 31 25 ++ BitVec.ofBool (bit temp 2) ++ bits a.FCSR 23 12 ++ bits temp 11 7 ++
          bits a.FCSR 6 2 ++ bits temp 1 0 : BitVec 32) }
  -- elseif fs = 31 then
  else if fs == 31#32 then
    if bits temp 22 18 != 0#5 then
      -- UNPREDICTABLE
      Pseudo.modify fun a => { a with FCSR := o.ctc1Unpredictable a fs temp }
    else
      -- FCSR <- temp
      Pseudo.modify fun a => { a with FCSR := temp }
  -- else UNPREDICTABLE
  else Pseudo.modify fun a => { a with FCSR := o.ctc1Unpredictable a fs temp }
  -- CheckFPException()
  CheckFPException

end Manual.Ops
