import Semantics.Manual.FPU

/-!
# Manual.Ops.FpuMove — FP moves (MD00086 Vol II-A Rev 6.06), 7B S4

`MFC1`, `MTC1`, `MFHC1`, `MTHC1`, `MOV.fmt`, `MOVF.fmt`, `MOVT.fmt`, `MOVN.fmt`, `MOVZ.fmt`, `MOVF`,
`MOVT`. "The move is non-arithmetic; it causes no IEEE 754 exceptions, and the FCSR Cause and FCSR
Flags fields are not modified" (MOV.fmt, p.275), so no `FPResult`. The `PS` format is not in the
profile (SPEC-NOTES §9 item 13).
-/

namespace Manual.Ops

open Manual

/-- **MFC1 rt, fs** — MD00086 Vol II-A Rev 6.06, MFC1, p.267.
```
data <- ValueFPR(fs, UNINTERPRETED_WORD)
GPR[rt] <- data
``` -/
def MFC1 (rt fs : W32) : Pseudo Unit := do
  -- data <- ValueFPR(fs, UNINTERPRETED_WORD)
  let data ← ValueFPR32 (reg fs)
  -- GPR[rt] <- data
  setGPR (reg rt) data

/-- **MTC1 rt, fs** — MD00086 Vol II-A Rev 6.06, MTC1, p.292.
```
data <- GPR[rt]31..0
StoreFPR(fs, UNINTERPRETED_WORD, data)
``` -/
def MTC1 (rt fs : W32) : Pseudo Unit := do
  -- data <- GPR[rt]31..0
  let data := low (← GPR (reg rt)) 32
  -- StoreFPR(fs, UNINTERPRETED_WORD, data)
  StoreFPR32 (reg fs) data

/-- **MFHC1 rt, fs** — MD00086 Vol II-A Rev 6.06, MFHC1, p.271.
```
data <- ValueFPR(fs, UNINTERPRETED_DOUBLEWORD)63..32
GPR[rt] <- data
```
Restrictions: "The results are UNPREDICTABLE if StatusFR = 0 and fs is odd" (`ValueFPR64`, the
oracle). -/
def MFHC1 (rt fs : W32) : Pseudo Unit := do
  -- data <- ValueFPR(fs, UNINTERPRETED_DOUBLEWORD)63..32
  let data := bits (← ValueFPR64 (reg fs)) 63 32
  -- GPR[rt] <- data
  setGPR (reg rt) data

/-- **MTHC1 rt, fs** — MD00086 Vol II-A Rev 6.06, MTHC1, p.295.
```
newdata <- GPR[rt]
olddata <- ValueFPR(fs, UNINTERPRETED_DOUBLEWORD)31..0
StoreFPR(fs, UNINTERPRETED_DOUBLEWORD, newdata || olddata)
```
Restrictions: "The results are UNPREDICTABLE if StatusFR = 0 and fs is odd" (the oracle). -/
def MTHC1 (rt fs : W32) : Pseudo Unit := do
  -- newdata <- GPR[rt]
  let newdata ← GPR (reg rt)
  -- olddata <- ValueFPR(fs, UNINTERPRETED_DOUBLEWORD)31..0
  let olddata := bits (← ValueFPR64 (reg fs)) 31 0
  -- StoreFPR(fs, UNINTERPRETED_DOUBLEWORD, newdata || olddata)
  StoreFPR64 (reg fs) (newdata ++ olddata)

/-- **MOV.S fd, fs** — MD00086 Vol II-A Rev 6.06, MOV.fmt, p.275 (fmt = S).
```
StoreFPR(fd, fmt, ValueFPR(fs, fmt))
``` -/
def MOV_S (fd fs : W32) : Pseudo Unit := do
  -- StoreFPR(fd, fmt, ValueFPR(fs, fmt))
  StoreFPR32 (reg fd) (← ValueFPR32 (reg fs))

/-- **MOV.D fd, fs** — MD00086 Vol II-A Rev 6.06, MOV.fmt, p.275 (fmt = D).
```
StoreFPR(fd, fmt, ValueFPR(fs, fmt))
``` -/
def MOV_D (fd fs : W32) : Pseudo Unit := do
  -- StoreFPR(fd, fmt, ValueFPR(fs, fmt))
  StoreFPR64 (reg fd) (← ValueFPR64 (reg fs))

/-- **MOVF.S fd, fs, cc** — MD00086 Vol II-A Rev 6.06, MOVF.fmt, p.277 (fmt = S).
```
if FPConditionCode(cc) = 0 then
   StoreFPR(fd, fmt, ValueFPR(fs, fmt))
else
   StoreFPR(fd, fmt, ValueFPR(fd, fmt))
endif
```
"If ... FPR fs is not copied and FPR fd retains its previous value in format fmt": the else arm
stores the value of `fd` read in format `fmt` (for a double and an odd `fd` the oracle). -/
def MOVF_S (fd fs cc : W32) : Pseudo Unit := do
  -- if FPConditionCode(cc) = 0 then
  if (← FPConditionCode cc.toNat) == false then
    -- StoreFPR(fd, fmt, ValueFPR(fs, fmt))
    StoreFPR32 (reg fd) (← ValueFPR32 (reg fs))
  else
    -- StoreFPR(fd, fmt, ValueFPR(fd, fmt))
    StoreFPR32 (reg fd) (← ValueFPR32 (reg fd))

/-- **MOVF.D fd, fs, cc** — MD00086 Vol II-A Rev 6.06, MOVF.fmt, p.277 (fmt = D).
```
if FPConditionCode(cc) = 0 then
   StoreFPR(fd, fmt, ValueFPR(fs, fmt))
else
   StoreFPR(fd, fmt, ValueFPR(fd, fmt))
endif
```
"If ... FPR fs is not copied and FPR fd retains its previous value in format fmt": the else arm
stores the value of `fd` read in format `fmt` (for a double and an odd `fd` the oracle). -/
def MOVF_D (fd fs cc : W32) : Pseudo Unit := do
  -- if FPConditionCode(cc) = 0 then
  if (← FPConditionCode cc.toNat) == false then
    -- StoreFPR(fd, fmt, ValueFPR(fs, fmt))
    StoreFPR64 (reg fd) (← ValueFPR64 (reg fs))
  else
    -- StoreFPR(fd, fmt, ValueFPR(fd, fmt))
    StoreFPR64 (reg fd) (← ValueFPR64 (reg fd))

/-- **MOVT.S fd, fs, cc** — MD00086 Vol II-A Rev 6.06, MOVT.fmt, p.282 (fmt = S).
```
if FPConditionCode(cc) = 1 then
   StoreFPR(fd, fmt, ValueFPR(fs, fmt))
else
   StoreFPR(fd, fmt, ValueFPR(fd, fmt))
endif
```
"If ... FPR fs is not copied and FPR fd retains its previous value in format fmt": the else arm
stores the value of `fd` read in format `fmt` (for a double and an odd `fd` the oracle). -/
def MOVT_S (fd fs cc : W32) : Pseudo Unit := do
  -- if FPConditionCode(cc) = 1 then
  if (← FPConditionCode cc.toNat) == true then
    -- StoreFPR(fd, fmt, ValueFPR(fs, fmt))
    StoreFPR32 (reg fd) (← ValueFPR32 (reg fs))
  else
    -- StoreFPR(fd, fmt, ValueFPR(fd, fmt))
    StoreFPR32 (reg fd) (← ValueFPR32 (reg fd))

/-- **MOVT.D fd, fs, cc** — MD00086 Vol II-A Rev 6.06, MOVT.fmt, p.282 (fmt = D).
```
if FPConditionCode(cc) = 1 then
   StoreFPR(fd, fmt, ValueFPR(fs, fmt))
else
   StoreFPR(fd, fmt, ValueFPR(fd, fmt))
endif
```
"If ... FPR fs is not copied and FPR fd retains its previous value in format fmt": the else arm
stores the value of `fd` read in format `fmt` (for a double and an odd `fd` the oracle). -/
def MOVT_D (fd fs cc : W32) : Pseudo Unit := do
  -- if FPConditionCode(cc) = 1 then
  if (← FPConditionCode cc.toNat) == true then
    -- StoreFPR(fd, fmt, ValueFPR(fs, fmt))
    StoreFPR64 (reg fd) (← ValueFPR64 (reg fs))
  else
    -- StoreFPR(fd, fmt, ValueFPR(fd, fmt))
    StoreFPR64 (reg fd) (← ValueFPR64 (reg fd))

/-- **MOVN.S fd, fs, rt** — MD00086 Vol II-A Rev 6.06, MOVN.fmt, p.280 (fmt = S).
```
if GPR[rt] != 0 then
   StoreFPR(fd, fmt, ValueFPR(fs, fmt))
else
   StoreFPR(fd, fmt, ValueFPR(fd, fmt))
endif
```
"If ... FPR fs is not copied and FPR fd retains its previous value in format fmt": the else arm
stores the value of `fd` read in format `fmt` (for a double and an odd `fd` the oracle). -/
def MOVN_S (fd fs rt : W32) : Pseudo Unit := do
  -- if GPR[rt] != 0 then
  if (← GPR (reg rt)) != 0#32 then
    -- StoreFPR(fd, fmt, ValueFPR(fs, fmt))
    StoreFPR32 (reg fd) (← ValueFPR32 (reg fs))
  else
    -- StoreFPR(fd, fmt, ValueFPR(fd, fmt))
    StoreFPR32 (reg fd) (← ValueFPR32 (reg fd))

/-- **MOVN.D fd, fs, rt** — MD00086 Vol II-A Rev 6.06, MOVN.fmt, p.280 (fmt = D).
```
if GPR[rt] != 0 then
   StoreFPR(fd, fmt, ValueFPR(fs, fmt))
else
   StoreFPR(fd, fmt, ValueFPR(fd, fmt))
endif
```
"If ... FPR fs is not copied and FPR fd retains its previous value in format fmt": the else arm
stores the value of `fd` read in format `fmt` (for a double and an odd `fd` the oracle). -/
def MOVN_D (fd fs rt : W32) : Pseudo Unit := do
  -- if GPR[rt] != 0 then
  if (← GPR (reg rt)) != 0#32 then
    -- StoreFPR(fd, fmt, ValueFPR(fs, fmt))
    StoreFPR64 (reg fd) (← ValueFPR64 (reg fs))
  else
    -- StoreFPR(fd, fmt, ValueFPR(fd, fmt))
    StoreFPR64 (reg fd) (← ValueFPR64 (reg fd))

/-- **MOVZ.S fd, fs, rt** — MD00086 Vol II-A Rev 6.06, MOVZ.fmt, p.285 (fmt = S).
```
if GPR[rt] = 0 then
   StoreFPR(fd, fmt, ValueFPR(fs, fmt))
else
   StoreFPR(fd, fmt, ValueFPR(fd, fmt))
endif
```
"If ... FPR fs is not copied and FPR fd retains its previous value in format fmt": the else arm
stores the value of `fd` read in format `fmt` (for a double and an odd `fd` the oracle). -/
def MOVZ_S (fd fs rt : W32) : Pseudo Unit := do
  -- if GPR[rt] = 0 then
  if (← GPR (reg rt)) == 0#32 then
    -- StoreFPR(fd, fmt, ValueFPR(fs, fmt))
    StoreFPR32 (reg fd) (← ValueFPR32 (reg fs))
  else
    -- StoreFPR(fd, fmt, ValueFPR(fd, fmt))
    StoreFPR32 (reg fd) (← ValueFPR32 (reg fd))

/-- **MOVZ.D fd, fs, rt** — MD00086 Vol II-A Rev 6.06, MOVZ.fmt, p.285 (fmt = D).
```
if GPR[rt] = 0 then
   StoreFPR(fd, fmt, ValueFPR(fs, fmt))
else
   StoreFPR(fd, fmt, ValueFPR(fd, fmt))
endif
```
"If ... FPR fs is not copied and FPR fd retains its previous value in format fmt": the else arm
stores the value of `fd` read in format `fmt` (for a double and an odd `fd` the oracle). -/
def MOVZ_D (fd fs rt : W32) : Pseudo Unit := do
  -- if GPR[rt] = 0 then
  if (← GPR (reg rt)) == 0#32 then
    -- StoreFPR(fd, fmt, ValueFPR(fs, fmt))
    StoreFPR64 (reg fd) (← ValueFPR64 (reg fs))
  else
    -- StoreFPR(fd, fmt, ValueFPR(fd, fmt))
    StoreFPR64 (reg fd) (← ValueFPR64 (reg fd))

/-- **MOVF rd, rs, cc** — MD00086 Vol II-A Rev 6.06, MOVF, p.276.
```
if FPConditionCode(cc) = 0 then
   GPR[rd] <- GPR[rs]
endif
``` -/
def MOVF (rs cc rd : W32) : Pseudo Unit := do
  -- if FPConditionCode(cc) = 0 then GPR[rd] <- GPR[rs] endif
  if (← FPConditionCode cc.toNat) == false then setGPR (reg rd) (← GPR (reg rs))

/-- **MOVT rd, rs, cc** — MD00086 Vol II-A Rev 6.06, MOVT, p.281.
```
if FPConditionCode(cc) = 1 then
   GPR[rd] <- GPR[rs]
endif
``` -/
def MOVT (rs cc rd : W32) : Pseudo Unit := do
  -- if FPConditionCode(cc) = 1 then GPR[rd] <- GPR[rs] endif
  if (← FPConditionCode cc.toNat) == true then setGPR (reg rd) (← GPR (reg rs))

end Manual.Ops
