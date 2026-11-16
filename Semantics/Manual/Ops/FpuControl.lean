import Semantics.Manual.FPU

/-!
# Manual.Ops.FpuControl — FP control register moves (MD00086 Vol II-A Rev 6.06), Release 6

`CFC1` and `CTC1` as the Rev 6.06 pages give them; only the Release 6 arms are transcribed (as for
MTC0, `Manual.Ops.MTC0`): this spec is the Release 6 profile, whose `ConfigAR` is 2 ("2 Release 6",
MD00090 Vol III Rev 6.02 Table 9.64, p.234) and whose `FIR.UFRP` is 0 ("R0 (Release 6)", MD00082
Vol I-A Rev 6.01 Table 6.5, p.88). So every `if ConfigAR ≥ 2 SignalException(ReservedInstruction)
/* Release 6 traps */` is the exception, every `if ConfigAR ≤ 2 then ... UNPREDICTABLE` arm is the
UNPREDICTABLE, and the `FIRUFRP = 1` / `ConfigAR > 2` arms (the `StatusFR` switch, the `Config5.FRE`
access) are not transcribed. The FCC bits (31..25, 23) of FCSR are reserved in
Release 6 (Table 6.8, p.92), so a write that names them goes through `FCSRWrite` (the R/W fields
only), and FCCR reads 0.

**Misprint.** CFC1's Operation ends "if Config2AR < 2 then GPR[rt] ← temp endif" (p.130): `Config2`
has no `AR` field and, read as `ConfigAR`, Release 6 would never write `GPR[rt]` — an instruction that
reads a control register into nothing. Read as the unconditional `GPR[rt] ← temp` of the earlier
releases (SPEC-NOTES). Its `else` arm "if Config2AR ≥ 2 SignalException(ReservedInstruction)" and the
same arm of CTC1 are read with `ConfigAR`, as their comment "/*Release 6 traps*/" says.

**Misprint (fs = 5).** The `FRE` arm reads "if ConfigAR ≤ 2 then temp ← UNPREDICTABLE else if not
Config5UFR then SignalException(ReservedInstruction) endif; temp ← 0^31 || Config5FRE" (p.130; the `≤`
read in the PDF image). Release 6 has `ConfigAR = 2`, so read literally the Release 6 `FRE` read would
be dead code, against the Description: "The definition of this instruction has been extended in
Release 6 to allow user code to read and modify the Config5FRE bit" (p.129). Read as `ConfigAR < 2`
(the comparison of the `Config2AR < 2` line below), the Release 6 arm is the `else`: this profile has
no `FRE` (`FIR.FREP = 0`, MD00082 Vol I-A Rev 6.01 Table 6.5, p.88: "If FREP=1, then Config5UFE and
Config5FRE are available"; `Config5.UFR` R0, MD00090 Vol III Rev 6.02 Table 9.69, p.264), so `not
Config5UFR` signals Reserved Instruction. That is also what the Restrictions require: "In Release 6
and later, a Reserved Instruction exception occurs if fs specifies a register that does not exist"
(p.129). QEMU `mips32r6-generic` signals it too (`tests/oracle/fp_cfc1_ri_fs5.asm`).
-/

namespace Manual.Ops

open Manual

/-- **CFC1 rt, fs** — MD00086 Vol II-A Rev 6.06, CFC1, p.129-130 (Release 6 arms).
```
if fs = 0 then temp <- FIR
elseif fs = 1 then /* read UFR */
   if FIR_UFRP then ... else
      if ConfigAR >= 2 SignalException(ReservedInstruction) /* Release 6 traps */ endif
      temp <- UNPREDICTABLE endif
elseif fs = 4 then /* UNFR */
   if ConfigAR >= 2 SignalException(ReservedInstruction) /* Release 6 traps */ endif
   temp <- UNPREDICTABLE
elseif fs = 5 then /* user read of FRE, if permitted */
   if ConfigAR <= 2 then temp <- UNPREDICTABLE      (misprint: read as ConfigAR < 2, module doc)
   else if not Config5UFR then SignalException(ReservedInstruction) endif
        temp <- 0^31 || Config5FRE endif
elseif fs = 25 then /* FCCR */  temp <- 0^24 || FCSR31..25 || FCSR23
elseif fs = 26 then /* FEXR */  temp <- 0^14 || FCSR17..12 || 0^5 || FCSR6..2 || 0^2
elseif fs = 28 then /* FENR */  temp <- 0^20 || FCSR11..7 || 0^4 || FCSR24 || FCSR1..0
elseif fs = 31 then /* FCSR */  temp <- FCSR
else
   if Config2AR >= 2 SignalException(ReservedInstruction) /* Release 6 traps; includes NFRE */ endif
   temp <- UNPREDICTABLE
endif
if Config2AR < 2 then GPR[rt] <- temp endif     (misprint: read as GPR[rt] <- temp)
```
`FCSR` is read with its read-only bits (`FCSRRead`). -/
def CFC1 (rt fs : W32) : Pseudo Unit := do
  let a ← Pseudo.get
  let i ← Pseudo.impl
  -- if fs = 0 then temp <- FIR
  let temp ← (if fs == 0#32 then pure i.FIR
    -- elseif fs = 1 then (FIR_UFRP = 0): if ConfigAR >= 2 SignalException(ReservedInstruction)
    else if fs == 1#32 then SignalException .ReservedInstruction
    -- elseif fs = 4 then if ConfigAR >= 2 SignalException(ReservedInstruction)
    else if fs == 4#32 then SignalException .ReservedInstruction
    -- elseif fs = 5 then (ConfigAR < 2 is false, module doc) if not Config5UFR then
    --   SignalException(ReservedInstruction)   (Config5UFR = 0: no FRE on this profile)
    else if fs == 5#32 then SignalException .ReservedInstruction
    -- elseif fs = 25 then temp <- 0^24 || FCSR31..25 || FCSR23
    else if fs == 25#32 then
      pure (0#24 ++ (FCSRRead a).extractLsb' 25 7 ++ BitVec.ofBool (bit (FCSRRead a) 23) : BitVec 32)
    -- elseif fs = 26 then temp <- 0^14 || FCSR17..12 || 0^5 || FCSR6..2 || 0^2
    else if fs == 26#32 then
      pure (0#14 ++ (FCSRRead a).extractLsb' 12 6 ++ 0#5 ++ (FCSRRead a).extractLsb' 2 5 ++ 0#2 : BitVec 32)
    -- elseif fs = 28 then temp <- 0^20 || FCSR11..7 || 0^4 || FCSR24 || FCSR1..0
    else if fs == 28#32 then
      pure (0#20 ++ (FCSRRead a).extractLsb' 7 5 ++ 0#4 ++ BitVec.ofBool (bit (FCSRRead a) 24) ++
        (FCSRRead a).extractLsb' 0 2 : BitVec 32)
    -- elseif fs = 31 then temp <- FCSR
    else if fs == 31#32 then pure (FCSRRead a)
    -- else if ConfigAR >= 2 SignalException(ReservedInstruction)
    else SignalException .ReservedInstruction : Pseudo W32)
  -- GPR[rt] <- temp
  setGPR (reg rt) temp

/-- **CTC1 rt, fs** — MD00086 Vol II-A Rev 6.06, CTC1, p.149-151 (Release 6 arms).
```
temp <- GPR[rt]31..0
if (fs = 1 or fs = 4) then
   if ConfigAR >= 2 SignalException(ReservedInstruction) /* Release 6 traps */ endif
   ... (StatusFR switch, not reached in Release 6)
elseif fs = 5 then /* user write of 1 to FRE */  if ConfigAR <= 2 then UNPREDICTABLE else ... endif
elseif fs = 6 then /* user write of 0 to FRE */  if ConfigAR <= 2 then UNPREDICTABLE else ... endif
elseif fs = 25 then /* FCCR */
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
else
   if Config2AR >= 2 SignalException(ReservedInstruction) /* Release 6 traps */ endif
   UNPREDICTABLE
endif
CheckFPException()
```
`FCSR.Impl` is not implemented. "The register is written before the exception occurs" (Description,
p.149): `CheckFPException` follows the write. Every write to FCSR keeps only its R/W fields
(`FCSRWrite`). The `UNPREDICTABLE` arms are `Oracle.ctc1Unpredictable`. -/
def CTC1 (rt fs : W32) : Pseudo Unit := do
  let o ← Pseudo.oracle
  -- temp <- GPR[rt]31..0
  let temp := low (← GPR (reg rt)) 32
  -- if (fs = 1 or fs = 4) then if ConfigAR >= 2 SignalException(ReservedInstruction)
  if fs == 1#32 || fs == 4#32 then SignalException .ReservedInstruction
  -- elseif fs = 5 / fs = 6 then if ConfigAR <= 2 then UNPREDICTABLE
  else if fs == 5#32 || fs == 6#32 then
    resolve (o.ctc1Unpredictable (← Pseudo.get) fs temp)
  -- elseif fs = 25 then
  else if fs == 25#32 then
    if bits temp 31 8 != 0#24 then
      -- UNPREDICTABLE
      resolve (o.ctc1Unpredictable (← Pseudo.get) fs temp)
    else
      -- FCSR <- temp7..1 || FCSR24 || temp0 || FCSR22..0
      Pseudo.modify fun a => { a with FCSR := FCSRWrite (
        bits temp 7 1 ++ BitVec.ofBool (bit a.FCSR 24) ++ BitVec.ofBool (bit temp 0) ++
          bits a.FCSR 22 0 : BitVec 32) }
  -- elseif fs = 26 then
  else if fs == 26#32 then
    if bits temp 31 18 != 0#14 || bits temp 11 7 != 0#5 || bits temp 2 0 != 0#3 then
      -- UNPREDICTABLE
      resolve (o.ctc1Unpredictable (← Pseudo.get) fs temp)
    else
      -- FCSR <- FCSR31..18 || temp17..12 || FCSR11..7 || temp6..2 || FCSR1..0
      Pseudo.modify fun a => { a with FCSR := FCSRWrite (
        bits a.FCSR 31 18 ++ bits temp 17 12 ++ bits a.FCSR 11 7 ++ bits temp 6 2 ++
          bits a.FCSR 1 0 : BitVec 32) }
  -- elseif fs = 28 then
  else if fs == 28#32 then
    if bits temp 31 12 != 0#20 || bits temp 6 3 != 0#4 then
      -- UNPREDICTABLE
      resolve (o.ctc1Unpredictable (← Pseudo.get) fs temp)
    else
      -- FCSR <- FCSR31..25 || temp2 || FCSR23..12 || temp11..7 || FCSR6..2 || temp1..0
      Pseudo.modify fun a => { a with FCSR := FCSRWrite (
        bits a.FCSR 31 25 ++ BitVec.ofBool (bit temp 2) ++ bits a.FCSR 23 12 ++ bits temp 11 7 ++
          bits a.FCSR 6 2 ++ bits temp 1 0 : BitVec 32) }
  -- elseif fs = 31 then
  else if fs == 31#32 then
    if bits temp 22 18 != 0#5 then
      -- UNPREDICTABLE
      resolve (o.ctc1Unpredictable (← Pseudo.get) fs temp)
    else
      -- FCSR <- temp
      Pseudo.modify fun a => { a with FCSR := FCSRWrite temp }
  -- else if ConfigAR >= 2 SignalException(ReservedInstruction)
  else SignalException .ReservedInstruction
  -- CheckFPException()
  CheckFPException

end Manual.Ops
