import Semantics.Manual.FPU

/-!
# Manual.Ops.FpuConvert — FP conversions (MD00086 Vol II-A Rev 6.06), 7B S4

`ROUND.W.fmt`, `TRUNC.W.fmt`, `CEIL.W.fmt`, `FLOOR.W.fmt`, `CVT.W.fmt`, `CVT.S.fmt`, `CVT.D.fmt`
for the formats of this profile (S, D, W). The `L` (64-bit fixed point) and `PS` formats are
UNPREDICTABLE with `FR = 0` ("The result of this instruction is UNPREDICTABLE if the processor is
executing in the FR=0 32-bit FPU register model", e.g. CVT.D.fmt p.153, CVT.L.fmt p.154) and are not
in the profile (SPEC-NOTES §9 item 13). `ConvertFmt` is the IEEE conversion of `Manual.IEEE`.
Each result goes through `FPResult` (Vol I-A §6.7.1, p.98-99): an Invalid Operation (Infinity, NaN, or
out of range) "If the Invalid Operation Enable bit is set in the FCSR, no result is written to fd and
an Invalid Operation exception is taken immediately. Otherwise, a default result is written to fd"
(ROUND.W.fmt, p.342). The default result for `FCSR.NAN2008 = 0` is `2^31 - 1` for the word format;
CVT.W.fmt p.160 prints "2^63-1", a typo (the result is a 32-bit word; ROUND.W.fmt p.342 and Vol I-A
Table 6.3 p.82 say `2^31 - 1`; SPEC-NOTES §9 item 13).
-/

namespace Manual.Ops

open Manual

/-- **ROUND.W.S fd, fs** — MD00086 Vol II-A Rev 6.06, ROUND.W.fmt, p.342 (fmt = S).
```
StoreFPR(fd, W, ConvertFmt(ValueFPR(fs, fmt), fmt, W))
```
The value is converted to 32-bit fixed point rounding to nearest/even (rounding mode 0). -/
def ROUND_W_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  -- ConvertFmt(x, S, W), rounding to nearest/even (rounding mode 0), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordS (IEEE.roundingMode 0#2) x)
  -- StoreFPR(fd, W, ...)
  StoreFPR32 (reg fd) r

/-- **ROUND.W.D fd, fs** — MD00086 Vol II-A Rev 6.06, ROUND.W.fmt, p.342 (fmt = D).
```
StoreFPR(fd, W, ConvertFmt(ValueFPR(fs, fmt), fmt, W))
```
The value is converted to 32-bit fixed point rounding to nearest/even (rounding mode 0). -/
def ROUND_W_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  -- ConvertFmt(x, D, W), rounding to nearest/even (rounding mode 0), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordD (IEEE.roundingMode 0#2) x)
  -- StoreFPR(fd, W, ...)
  StoreFPR32 (reg fd) r

/-- **TRUNC.W.S fd, fs** — MD00086 Vol II-A Rev 6.06, TRUNC.W.fmt, p.441 (fmt = S).
```
StoreFPR(fd, W, ConvertFmt(ValueFPR(fs, fmt), fmt, W))
```
The value is converted to 32-bit fixed point rounding toward zero (rounding mode 1). -/
def TRUNC_W_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  -- ConvertFmt(x, S, W), rounding toward zero (rounding mode 1), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordS (IEEE.roundingMode 1#2) x)
  -- StoreFPR(fd, W, ...)
  StoreFPR32 (reg fd) r

/-- **TRUNC.W.D fd, fs** — MD00086 Vol II-A Rev 6.06, TRUNC.W.fmt, p.441 (fmt = D).
```
StoreFPR(fd, W, ConvertFmt(ValueFPR(fs, fmt), fmt, W))
```
The value is converted to 32-bit fixed point rounding toward zero (rounding mode 1). -/
def TRUNC_W_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  -- ConvertFmt(x, D, W), rounding toward zero (rounding mode 1), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordD (IEEE.roundingMode 1#2) x)
  -- StoreFPR(fd, W, ...)
  StoreFPR32 (reg fd) r

/-- **CEIL.W.S fd, fs** — MD00086 Vol II-A Rev 6.06, CEIL.W.fmt, p.128 (fmt = S).
```
StoreFPR(fd, W, ConvertFmt(ValueFPR(fs, fmt), fmt, W))
```
The value is converted to 32-bit fixed point rounding toward +infinity (rounding mode 2). -/
def CEIL_W_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  -- ConvertFmt(x, S, W), rounding toward +infinity (rounding mode 2), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordS (IEEE.roundingMode 2#2) x)
  -- StoreFPR(fd, W, ...)
  StoreFPR32 (reg fd) r

/-- **CEIL.W.D fd, fs** — MD00086 Vol II-A Rev 6.06, CEIL.W.fmt, p.128 (fmt = D).
```
StoreFPR(fd, W, ConvertFmt(ValueFPR(fs, fmt), fmt, W))
```
The value is converted to 32-bit fixed point rounding toward +infinity (rounding mode 2). -/
def CEIL_W_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  -- ConvertFmt(x, D, W), rounding toward +infinity (rounding mode 2), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordD (IEEE.roundingMode 2#2) x)
  -- StoreFPR(fd, W, ...)
  StoreFPR32 (reg fd) r

/-- **FLOOR.W.S fd, fs** — MD00086 Vol II-A Rev 6.06, FLOOR.W.fmt, p.186 (fmt = S).
```
StoreFPR(fd, W, ConvertFmt(ValueFPR(fs, fmt), fmt, W))
```
The value is converted to 32-bit fixed point rounding toward -infinity (rounding mode 3). -/
def FLOOR_W_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  -- ConvertFmt(x, S, W), rounding toward -infinity (rounding mode 3), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordS (IEEE.roundingMode 3#2) x)
  -- StoreFPR(fd, W, ...)
  StoreFPR32 (reg fd) r

/-- **FLOOR.W.D fd, fs** — MD00086 Vol II-A Rev 6.06, FLOOR.W.fmt, p.186 (fmt = D).
```
StoreFPR(fd, W, ConvertFmt(ValueFPR(fs, fmt), fmt, W))
```
The value is converted to 32-bit fixed point rounding toward -infinity (rounding mode 3). -/
def FLOOR_W_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  -- ConvertFmt(x, D, W), rounding toward -infinity (rounding mode 3), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordD (IEEE.roundingMode 3#2) x)
  -- StoreFPR(fd, W, ...)
  StoreFPR32 (reg fd) r

/-- **CVT.W.S fd, fs** — MD00086 Vol II-A Rev 6.06, CVT.W.fmt, p.160 (fmt = S).
```
StoreFPR(fd, W, ConvertFmt(ValueFPR(fs, fmt), fmt, W))
```
The value is "rounded according to the current rounding mode in FCSR". -/
def CVT_W_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  -- ConvertFmt(x, S, W) under FCSR.RM
  let a ← Pseudo.get
  let r ← FPResult (IEEE.toWordS (IEEE.roundingMode (FCSR_RM a)) x)
  -- StoreFPR(fd, W, ...)
  StoreFPR32 (reg fd) r

/-- **CVT.W.D fd, fs** — MD00086 Vol II-A Rev 6.06, CVT.W.fmt, p.160 (fmt = D).
```
StoreFPR(fd, W, ConvertFmt(ValueFPR(fs, fmt), fmt, W))
```
The value is "rounded according to the current rounding mode in FCSR". -/
def CVT_W_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  -- ConvertFmt(x, D, W) under FCSR.RM
  let a ← Pseudo.get
  let r ← FPResult (IEEE.toWordD (IEEE.roundingMode (FCSR_RM a)) x)
  -- StoreFPR(fd, W, ...)
  StoreFPR32 (reg fd) r

/-- **CVT.D.S fd, fs** — MD00086 Vol II-A Rev 6.06, CVT.D.fmt, p.153 (fmt = S).
```
StoreFPR (fd, D, ConvertFmt(ValueFPR(fs, fmt), fmt, D))
```
"If fmt is S or W, then the operation is always exact." -/
def CVT_D_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  -- ConvertFmt(x, S, D), with FCSR Cause/Flags and CheckFPException
  let o ← Pseudo.oracle
  let r ← FPResult (IEEE.cvtDS o.cvtQNaNToD x)
  -- StoreFPR (fd, D, ...)
  StoreFPR64 (reg fd) r

/-- **CVT.D.W fd, fs** — MD00086 Vol II-A Rev 6.06, CVT.D.fmt, p.153 (fmt = W).
```
StoreFPR (fd, D, ConvertFmt(ValueFPR(fs, fmt), fmt, D))
``` -/
def CVT_D_W (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, W)
  let x ← ValueFPR32 (reg fs)
  -- ConvertFmt(x, W, D), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.cvtDW x)
  -- StoreFPR (fd, D, ...)
  StoreFPR64 (reg fd) r

/-- **CVT.S.D fd, fs** — MD00086 Vol II-A Rev 6.06, CVT.S.fmt, p.159 (fmt = D).
```
StoreFPR(fd, S, ConvertFmt(ValueFPR(fs, fmt), fmt, S))
```
The value is "rounded according to the current rounding mode in FCSR". -/
def CVT_S_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  -- ConvertFmt(x, D, S) under FCSR.RM, with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let o ← Pseudo.oracle
  let r ← FPResult (IEEE.cvtSD o.cvtQNaNToS a x)
  -- StoreFPR(fd, S, ...)
  StoreFPR32 (reg fd) r

/-- **CVT.S.W fd, fs** — MD00086 Vol II-A Rev 6.06, CVT.S.fmt, p.159 (fmt = W).
```
StoreFPR(fd, S, ConvertFmt(ValueFPR(fs, fmt), fmt, S))
``` -/
def CVT_S_W (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, W)
  let x ← ValueFPR32 (reg fs)
  -- ConvertFmt(x, W, S) under FCSR.RM, with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.cvtSW a x)
  -- StoreFPR(fd, S, ...)
  StoreFPR32 (reg fd) r

end Manual.Ops
