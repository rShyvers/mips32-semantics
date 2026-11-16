import Semantics.Manual.FPU

/-!
# Manual.Ops.FpuMove — FP moves (MD00086 Vol II-A Rev 6.06)

`MFC1`, `MTC1`, `MFHC1`, `MTHC1`, `MOV.fmt` (Release 6 removed `MOVF.fmt`, `MOVT.fmt`, `MOVN.fmt`,
`MOVZ.fmt`, `MOVF`, `MOVT`). "The move is non-arithmetic; it causes no IEEE 754 exceptions, and the FCSR Cause and FCSR
Flags fields are not modified" (MOV.fmt, p.275), so no `FPResult`. The `PS` format is not in the
profile (SPEC-NOTES §9 item 13).
Transcribed for the Release 6 64-bit FPU (`Status.FR = 1`): a 32-bit value is the low half of a
64-bit FPR (`ValueFPR32`/`StoreFPR32`), `MFHC1`/`MTHC1` read and write bits 63..32 of `FPR[fs]`.
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
Restrictions: "The results are UNPREDICTABLE if StatusFR = 0 and fs is odd" (`Status.FR` reads 1
here). -/
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
Restrictions: "The results are UNPREDICTABLE if StatusFR = 0 and fs is odd" (`Status.FR` reads 1
here). -/
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

end Manual.Ops
