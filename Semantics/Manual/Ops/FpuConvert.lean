import Semantics.Manual.FPU

/-!
# Manual.Ops.FpuConvert — FP conversions (MD00086 Vol II-A Rev 6.06), Release 6

`ROUND.fmt`, `TRUNC.fmt`, `CEIL.fmt`, `FLOOR.fmt`, `CVT.W.fmt`, `CVT.L.fmt`, `CVT.S.fmt`, `CVT.D.fmt`
for the formats of this profile (S, D, W, L: "Release 6 on a 64-bit FPU requires S, D, W, and L data
formats", MD00082 Vol I-A Rev 6.01 Table 6.4 note 3, p.85; the L pages are predictable "if executing
on a 64-bit FPU in the FR=1 mode", e.g. CVT.L.fmt p.154). `ConvertFmt` is the IEEE conversion of
`Manual.IEEE`. Each result goes through `FPResult` (Vol I-A §6.7.1, p.98-99): an Invalid Operation
(Infinity, NaN, or out of range) "If the Invalid Operation Enable bit is set in the FCSR, no result is
written to fd and an Invalid Operation exception is taken immediately. Otherwise, a default result is
written to fd" (ROUND.W.fmt, p.342). The default results for `FCSR.NAN2008 = 1` are those of Vol I-A
Table 6.3, p.82 (0 for a NaN, `2^31 - 1` / `2^63 - 1` too big, `-2^31` / `-2^63` too small). The pages
print the too-small result as "-2^31–1" / "-2^63–1" (e.g. ROUND.L.fmt p.341, CVT.L.fmt p.154), which
is not representable; Table 6.3 gives `0x8000 0000` / `0x8000 0000 0000 0000` (misprint, SPEC-NOTES).
CVT.W.fmt (p.160) prints the doubleword values ("2^63–1", "-2^63–1") for its word result although
its range check is "-2^31 to 2^31-1" (same page): read as the Table 6.3 word values like the other
W pages (CEIL.W p.128, FLOOR.W p.186, ROUND.W p.342, TRUNC.W p.441).
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
  let a ← Pseudo.get
  -- ConvertFmt(x, S, W), rounding to nearest/even (rounding mode 0), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordS a (IEEE.roundingMode 0#2) x)
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
  let a ← Pseudo.get
  -- ConvertFmt(x, D, W), rounding to nearest/even (rounding mode 0), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordD a (IEEE.roundingMode 0#2) x)
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
  let a ← Pseudo.get
  -- ConvertFmt(x, S, W), rounding toward zero (rounding mode 1), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordS a (IEEE.roundingMode 1#2) x)
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
  let a ← Pseudo.get
  -- ConvertFmt(x, D, W), rounding toward zero (rounding mode 1), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordD a (IEEE.roundingMode 1#2) x)
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
  let a ← Pseudo.get
  -- ConvertFmt(x, S, W), rounding toward +infinity (rounding mode 2), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordS a (IEEE.roundingMode 2#2) x)
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
  let a ← Pseudo.get
  -- ConvertFmt(x, D, W), rounding toward +infinity (rounding mode 2), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordD a (IEEE.roundingMode 2#2) x)
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
  let a ← Pseudo.get
  -- ConvertFmt(x, S, W), rounding toward -infinity (rounding mode 3), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordS a (IEEE.roundingMode 3#2) x)
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
  let a ← Pseudo.get
  -- ConvertFmt(x, D, W), rounding toward -infinity (rounding mode 3), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordD a (IEEE.roundingMode 3#2) x)
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
  let a ← Pseudo.get
  -- ConvertFmt(x, S, W), rounding per FCSR.RM, with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordS a (IEEE.roundingMode (FCSR_RM a)) x)
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
  let a ← Pseudo.get
  -- ConvertFmt(x, D, W), rounding per FCSR.RM, with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toWordD a (IEEE.roundingMode (FCSR_RM a)) x)
  -- StoreFPR(fd, W, ...)
  StoreFPR32 (reg fd) r

/-- **ROUND.L.S fd, fs** — MD00086 Vol II-A Rev 6.06, ROUND.L.fmt, p.341 (fmt = S).
```
StoreFPR(fd, L, ConvertFmt(ValueFPR(fs, fmt), fmt, L))
```
The value is converted to 64-bit fixed point rounding to nearest/even (rounding mode 0). -/
def ROUND_L_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  let a ← Pseudo.get
  -- ConvertFmt(x, S, L), rounding to nearest/even (rounding mode 0), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toLongS a (IEEE.roundingMode 0#2) x)
  -- StoreFPR(fd, L, ...)
  StoreFPR64 (reg fd) r

/-- **ROUND.L.D fd, fs** — MD00086 Vol II-A Rev 6.06, ROUND.L.fmt, p.341 (fmt = D).
```
StoreFPR(fd, L, ConvertFmt(ValueFPR(fs, fmt), fmt, L))
```
The value is converted to 64-bit fixed point rounding to nearest/even (rounding mode 0). -/
def ROUND_L_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  let a ← Pseudo.get
  -- ConvertFmt(x, D, L), rounding to nearest/even (rounding mode 0), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toLongD a (IEEE.roundingMode 0#2) x)
  -- StoreFPR(fd, L, ...)
  StoreFPR64 (reg fd) r

/-- **TRUNC.L.S fd, fs** — MD00086 Vol II-A Rev 6.06, TRUNC.L.fmt, p.440 (fmt = S).
```
StoreFPR(fd, L, ConvertFmt(ValueFPR(fs, fmt), fmt, L))
```
The value is converted to 64-bit fixed point rounding toward zero (rounding mode 1). -/
def TRUNC_L_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  let a ← Pseudo.get
  -- ConvertFmt(x, S, L), rounding toward zero (rounding mode 1), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toLongS a (IEEE.roundingMode 1#2) x)
  -- StoreFPR(fd, L, ...)
  StoreFPR64 (reg fd) r

/-- **TRUNC.L.D fd, fs** — MD00086 Vol II-A Rev 6.06, TRUNC.L.fmt, p.440 (fmt = D).
```
StoreFPR(fd, L, ConvertFmt(ValueFPR(fs, fmt), fmt, L))
```
The value is converted to 64-bit fixed point rounding toward zero (rounding mode 1). -/
def TRUNC_L_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  let a ← Pseudo.get
  -- ConvertFmt(x, D, L), rounding toward zero (rounding mode 1), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toLongD a (IEEE.roundingMode 1#2) x)
  -- StoreFPR(fd, L, ...)
  StoreFPR64 (reg fd) r

/-- **CEIL.L.S fd, fs** — MD00086 Vol II-A Rev 6.06, CEIL.L.fmt, p.127 (fmt = S).
```
StoreFPR(fd, L, ConvertFmt(ValueFPR(fs, fmt), fmt, L))
```
The value is converted to 64-bit fixed point rounding toward +infinity (rounding mode 2). -/
def CEIL_L_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  let a ← Pseudo.get
  -- ConvertFmt(x, S, L), rounding toward +infinity (rounding mode 2), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toLongS a (IEEE.roundingMode 2#2) x)
  -- StoreFPR(fd, L, ...)
  StoreFPR64 (reg fd) r

/-- **CEIL.L.D fd, fs** — MD00086 Vol II-A Rev 6.06, CEIL.L.fmt, p.127 (fmt = D).
```
StoreFPR(fd, L, ConvertFmt(ValueFPR(fs, fmt), fmt, L))
```
The value is converted to 64-bit fixed point rounding toward +infinity (rounding mode 2). -/
def CEIL_L_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  let a ← Pseudo.get
  -- ConvertFmt(x, D, L), rounding toward +infinity (rounding mode 2), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toLongD a (IEEE.roundingMode 2#2) x)
  -- StoreFPR(fd, L, ...)
  StoreFPR64 (reg fd) r

/-- **FLOOR.L.S fd, fs** — MD00086 Vol II-A Rev 6.06, FLOOR.L.fmt, p.185 (fmt = S).
```
StoreFPR(fd, L, ConvertFmt(ValueFPR(fs, fmt), fmt, L))
```
The value is converted to 64-bit fixed point rounding toward -infinity (rounding mode 3). -/
def FLOOR_L_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  let a ← Pseudo.get
  -- ConvertFmt(x, S, L), rounding toward -infinity (rounding mode 3), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toLongS a (IEEE.roundingMode 3#2) x)
  -- StoreFPR(fd, L, ...)
  StoreFPR64 (reg fd) r

/-- **FLOOR.L.D fd, fs** — MD00086 Vol II-A Rev 6.06, FLOOR.L.fmt, p.185 (fmt = D).
```
StoreFPR(fd, L, ConvertFmt(ValueFPR(fs, fmt), fmt, L))
```
The value is converted to 64-bit fixed point rounding toward -infinity (rounding mode 3). -/
def FLOOR_L_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  let a ← Pseudo.get
  -- ConvertFmt(x, D, L), rounding toward -infinity (rounding mode 3), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toLongD a (IEEE.roundingMode 3#2) x)
  -- StoreFPR(fd, L, ...)
  StoreFPR64 (reg fd) r

/-- **CVT.L.S fd, fs** — MD00086 Vol II-A Rev 6.06, CVT.L.fmt, p.154 (fmt = S).
```
StoreFPR(fd, L, ConvertFmt(ValueFPR(fs, fmt), fmt, L))
```
The value is "rounded according to the current rounding mode in FCSR". -/
def CVT_L_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  let a ← Pseudo.get
  -- ConvertFmt(x, S, L), rounding per FCSR.RM, with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toLongS a (IEEE.roundingMode (FCSR_RM a)) x)
  -- StoreFPR(fd, L, ...)
  StoreFPR64 (reg fd) r

/-- **CVT.L.D fd, fs** — MD00086 Vol II-A Rev 6.06, CVT.L.fmt, p.154 (fmt = D).
```
StoreFPR(fd, L, ConvertFmt(ValueFPR(fs, fmt), fmt, L))
```
The value is "rounded according to the current rounding mode in FCSR". -/
def CVT_L_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  let a ← Pseudo.get
  -- ConvertFmt(x, D, L), rounding per FCSR.RM, with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.toLongD a (IEEE.roundingMode (FCSR_RM a)) x)
  -- StoreFPR(fd, L, ...)
  StoreFPR64 (reg fd) r

/-- **CVT.D.S fd, fs** — MD00086 Vol II-A Rev 6.06, CVT.D.fmt, p.153 (fmt = S).
```
StoreFPR (fd, D, ConvertFmt(ValueFPR(fs, fmt), fmt, D))
```
"If fmt is S or W, then the operation is always exact." -/
def CVT_D_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  let a ← Pseudo.get
  let o ← Pseudo.oracle
  -- ConvertFmt(x, S, D), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.cvtDS o.cvtQNaNToD a x)
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

/-- **CVT.D.L fd, fs** — MD00086 Vol II-A Rev 6.06, CVT.D.fmt, p.153 (fmt = L).
```
StoreFPR (fd, D, ConvertFmt(ValueFPR(fs, fmt), fmt, D))
```
"converted to a value in double floating point format and rounded according to the current rounding
mode in FCSR" (only S and W are "always exact"). -/
def CVT_D_L (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, L)
  let x ← ValueFPR64 (reg fs)
  let a ← Pseudo.get
  -- ConvertFmt(x, L, D), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.cvtDL a x)
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
  let a ← Pseudo.get
  let o ← Pseudo.oracle
  -- ConvertFmt(x, D, S), with FCSR Cause/Flags and CheckFPException
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
  let a ← Pseudo.get
  -- ConvertFmt(x, W, S), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.cvtSW a x)
  -- StoreFPR(fd, S, ...)
  StoreFPR32 (reg fd) r

/-- **CVT.S.L fd, fs** — MD00086 Vol II-A Rev 6.06, CVT.S.fmt, p.159 (fmt = L).
```
StoreFPR(fd, S, ConvertFmt(ValueFPR(fs, fmt), fmt, S))
``` -/
def CVT_S_L (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, L)
  let x ← ValueFPR64 (reg fs)
  let a ← Pseudo.get
  -- ConvertFmt(x, L, S), with FCSR Cause/Flags and CheckFPException
  let r ← FPResult (IEEE.cvtSL a x)
  -- StoreFPR(fd, S, ...)
  StoreFPR32 (reg fd) r

end Manual.Ops
