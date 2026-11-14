import Semantics.Manual.FPU

/-!
# Manual.Ops.FpuArith — FP arithmetic (MD00086 Vol II-A Rev 6.06)

Sub-wave 7A transcribes the pilot `ADD.S`; 7B S4 the rest of the S and D arithmetic: `ADD.fmt`,
`SUB.fmt`, `MUL.fmt`, `DIV.fmt`, `SQRT.fmt`, `ABS.fmt`, `NEG.fmt`, `RECIP.fmt`, `RSQRT.fmt`,
`MADD.fmt`, `MSUB.fmt`, `NMADD.fmt`, `NMSUB.fmt`. The Coprocessor Unusable check (`Status.CU1 = 0`)
is made for the whole COP1 encoding space before the Operation runs (MD00090 Vol III Rev 6.02
§6.2.22, p.100; `Manual.Cycle`). Every arithmetic result goes through `FPResult` (FCSR Cause,
`CheckFPException`, Flags; MD00082 Vol I-A Rev 6.01 §6.7.1, p.98-99). The paired-single format `PS`
is not part of the profile (UNPREDICTABLE with `FR = 0`, SPEC-NOTES §9 item 13).
-/

namespace Manual.Ops

open Manual

/-- **ADD.S fd, fs, ft** — MD00086 Vol II-A Rev 6.06, ADD.fmt, p.34 (fmt = S).
```
StoreFPR (fd, fmt, ValueFPR(fs, fmt) +fmt ValueFPR(ft, fmt))
```
`+fmt` is the IEEE addition with its exceptions recorded in FCSR and checked (`FPResult`, MD00082
Vol I-A Rev 6.01 §6.7.1, p.98-99): "Floating Point Exceptions: Unimplemented Operation, Invalid
Operation, Inexact, Overflow, Underflow" (p.34). -/
def ADD_S (fd fs ft : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S), ValueFPR(ft, S)
  let x ← ValueFPR32 (reg fs)
  let y ← ValueFPR32 (reg ft)
  -- ValueFPR(fs, fmt) +fmt ValueFPR(ft, fmt), with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.addS a x y)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR32 (reg fd) r

/-- **ADD.D fd, fs, ft** — MD00086 Vol II-A Rev 6.06, ADD.fmt, p.34 (fmt = D).
```
StoreFPR (fd, fmt, ValueFPR(fs, fmt) +fmt ValueFPR(ft, fmt))
```
-/
def ADD_D (fd fs ft : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D), ValueFPR(ft, D)
  let x ← ValueFPR64 (reg fs)
  let y ← ValueFPR64 (reg ft)
  -- ValueFPR(fs, fmt) +fmt ValueFPR(ft, fmt), with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.addD a x y)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR64 (reg fd) r

/-- **SUB.S fd, fs, ft** — MD00086 Vol II-A Rev 6.06, SUB.fmt, p.389 (fmt = S).
```
StoreFPR (fd, fmt, ValueFPR(fs, fmt) -fmt ValueFPR(ft, fmt))
```
-/
def SUB_S (fd fs ft : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S), ValueFPR(ft, S)
  let x ← ValueFPR32 (reg fs)
  let y ← ValueFPR32 (reg ft)
  -- ValueFPR(fs, fmt) -fmt ValueFPR(ft, fmt), with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.subS a x y)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR32 (reg fd) r

/-- **SUB.D fd, fs, ft** — MD00086 Vol II-A Rev 6.06, SUB.fmt, p.389 (fmt = D).
```
StoreFPR (fd, fmt, ValueFPR(fs, fmt) -fmt ValueFPR(ft, fmt))
```
-/
def SUB_D (fd fs ft : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D), ValueFPR(ft, D)
  let x ← ValueFPR64 (reg fs)
  let y ← ValueFPR64 (reg ft)
  -- ValueFPR(fs, fmt) -fmt ValueFPR(ft, fmt), with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.subD a x y)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR64 (reg fd) r

/-- **MUL.S fd, fs, ft** — MD00086 Vol II-A Rev 6.06, MUL.fmt, p.302 (fmt = S).
```
StoreFPR (fd, fmt, ValueFPR(fs, fmt) xfmt ValueFPR(ft, fmt))
```
-/
def MUL_S (fd fs ft : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S), ValueFPR(ft, S)
  let x ← ValueFPR32 (reg fs)
  let y ← ValueFPR32 (reg ft)
  -- ValueFPR(fs, fmt) xfmt ValueFPR(ft, fmt), with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.mulS a x y)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR32 (reg fd) r

/-- **MUL.D fd, fs, ft** — MD00086 Vol II-A Rev 6.06, MUL.fmt, p.302 (fmt = D).
```
StoreFPR (fd, fmt, ValueFPR(fs, fmt) xfmt ValueFPR(ft, fmt))
```
-/
def MUL_D (fd fs ft : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D), ValueFPR(ft, D)
  let x ← ValueFPR64 (reg fs)
  let y ← ValueFPR64 (reg ft)
  -- ValueFPR(fs, fmt) xfmt ValueFPR(ft, fmt), with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.mulD a x y)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR64 (reg fd) r

/-- **DIV.S fd, fs, ft** — MD00086 Vol II-A Rev 6.06, DIV.fmt, p.170 (fmt = S).
```
StoreFPR (fd, fmt, ValueFPR(fs, fmt) / ValueFPR(ft, fmt))
```
-/
def DIV_S (fd fs ft : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S), ValueFPR(ft, S)
  let x ← ValueFPR32 (reg fs)
  let y ← ValueFPR32 (reg ft)
  -- ValueFPR(fs, fmt) / ValueFPR(ft, fmt), with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.divS a x y)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR32 (reg fd) r

/-- **DIV.D fd, fs, ft** — MD00086 Vol II-A Rev 6.06, DIV.fmt, p.170 (fmt = D).
```
StoreFPR (fd, fmt, ValueFPR(fs, fmt) / ValueFPR(ft, fmt))
```
-/
def DIV_D (fd fs ft : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D), ValueFPR(ft, D)
  let x ← ValueFPR64 (reg fs)
  let y ← ValueFPR64 (reg ft)
  -- ValueFPR(fs, fmt) / ValueFPR(ft, fmt), with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.divD a x y)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR64 (reg fd) r

/-- **SQRT.S fd, fs** — MD00086 Vol II-A Rev 6.06, SQRT.fmt, p.382 (fmt = S).
```
StoreFPR(fd, fmt, SquareRoot(ValueFPR(fs, fmt)))
```
-/
def SQRT_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  -- ValueFPR(fs, fmt) -> SquareRoot, with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.sqrtS a x)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR32 (reg fd) r

/-- **SQRT.D fd, fs** — MD00086 Vol II-A Rev 6.06, SQRT.fmt, p.382 (fmt = D).
```
StoreFPR(fd, fmt, SquareRoot(ValueFPR(fs, fmt)))
```
-/
def SQRT_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  -- ValueFPR(fs, fmt) -> SquareRoot, with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.sqrtD a x)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR64 (reg fd) r

/-- **ABS.S fd, fs** — MD00086 Vol II-A Rev 6.06, ABS.fmt, p.32 (fmt = S).
```
StoreFPR(fd, fmt, AbsoluteValue(ValueFPR(fs, fmt)))
```
-/
def ABS_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  -- AbsoluteValue(ValueFPR(fs, fmt)); with FIR.Has2008 = 0 the operation is arithmetic (p.32)
  let r ← FPResult (IEEE.absS x)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR32 (reg fd) r

/-- **ABS.D fd, fs** — MD00086 Vol II-A Rev 6.06, ABS.fmt, p.32 (fmt = D).
```
StoreFPR(fd, fmt, AbsoluteValue(ValueFPR(fs, fmt)))
```
-/
def ABS_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  -- AbsoluteValue(ValueFPR(fs, fmt)); with FIR.Has2008 = 0 the operation is arithmetic (p.32)
  let r ← FPResult (IEEE.absD x)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR64 (reg fd) r

/-- **NEG.S fd, fs** — MD00086 Vol II-A Rev 6.06, NEG.fmt, p.307 (fmt = S).
```
StoreFPR(fd, fmt, Negate(ValueFPR(fs, fmt)))
```
-/
def NEG_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  -- Negate(ValueFPR(fs, fmt)); with FIR.Has2008 = 0 the operation is arithmetic (p.307)
  let r ← FPResult (IEEE.negS x)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR32 (reg fd) r

/-- **NEG.D fd, fs** — MD00086 Vol II-A Rev 6.06, NEG.fmt, p.307 (fmt = D).
```
StoreFPR(fd, fmt, Negate(ValueFPR(fs, fmt)))
```
-/
def NEG_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  -- Negate(ValueFPR(fs, fmt)); with FIR.Has2008 = 0 the operation is arithmetic (p.307)
  let r ← FPResult (IEEE.negD x)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR64 (reg fd) r

/-- **RECIP.S fd, fs** — MD00086 Vol II-A Rev 6.06, RECIP.fmt, p.336 (fmt = S).
```
StoreFPR(fd, fmt, 1.0 / valueFPR(fs, fmt))
```
-/
def RECIP_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  -- 1.0 / valueFPR(fs, fmt) (accuracy implementation dependent, p.336: pinned to DIV)
  let a ← Pseudo.get
  let r ← FPResult (IEEE.recipS a x)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR32 (reg fd) r

/-- **RECIP.D fd, fs** — MD00086 Vol II-A Rev 6.06, RECIP.fmt, p.336 (fmt = D).
```
StoreFPR(fd, fmt, 1.0 / valueFPR(fs, fmt))
```
-/
def RECIP_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  -- 1.0 / valueFPR(fs, fmt) (accuracy implementation dependent, p.336: pinned to DIV)
  let a ← Pseudo.get
  let r ← FPResult (IEEE.recipD a x)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR64 (reg fd) r

/-- **RSQRT.S fd, fs** — MD00086 Vol II-A Rev 6.06, RSQRT.fmt, p.343 (fmt = S).
```
StoreFPR(fd, fmt, 1.0 / SquareRoot(valueFPR(fs, fmt)))
```
-/
def RSQRT_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  -- 1.0 / SquareRoot(valueFPR(fs, fmt)) (accuracy implementation dependent, p.343: SQRT then DIV)
  let a ← Pseudo.get
  let r ← FPResult (IEEE.rsqrtS a x)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR32 (reg fd) r

/-- **RSQRT.D fd, fs** — MD00086 Vol II-A Rev 6.06, RSQRT.fmt, p.343 (fmt = D).
```
StoreFPR(fd, fmt, 1.0 / SquareRoot(valueFPR(fs, fmt)))
```
-/
def RSQRT_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  -- 1.0 / SquareRoot(valueFPR(fs, fmt)) (accuracy implementation dependent, p.343: SQRT then DIV)
  let a ← Pseudo.get
  let r ← FPResult (IEEE.rsqrtD a x)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR64 (reg fd) r

/-- **MADD.S fd, fr, fs, ft** — MD00086 Vol II-A Rev 6.06, MADD.fmt, p.256 (fmt = S).
```
vfr <- ValueFPR(fr, fmt)
vfs <- ValueFPR(fs, fmt)
vft <- ValueFPR(ft, fmt)
StoreFPR(fd, fmt, (vfs xfmt vft) +fmt vfr)
```
"The intermediate product is rounded according to the current rounding mode in FCSR ... The results
and flags are as if separate floating-point multiply and add instructions were executed" (p.256).
-/
def MADD_S (fd fr fs ft : W32) : Pseudo Unit := do
  -- vfr <- ValueFPR(fr, S)
  let vfr ← ValueFPR32 (reg fr)
  -- vfs <- ValueFPR(fs, S)
  let vfs ← ValueFPR32 (reg fs)
  -- vft <- ValueFPR(ft, S)
  let vft ← ValueFPR32 (reg ft)
  -- (vfs xfmt vft) combined with vfr, with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.maddS a vfr vfs vft)
  -- StoreFPR(fd, fmt, ...)
  StoreFPR32 (reg fd) r

/-- **MADD.D fd, fr, fs, ft** — MD00086 Vol II-A Rev 6.06, MADD.fmt, p.256 (fmt = D).
```
vfr <- ValueFPR(fr, fmt)
vfs <- ValueFPR(fs, fmt)
vft <- ValueFPR(ft, fmt)
StoreFPR(fd, fmt, (vfs xfmt vft) +fmt vfr)
```
"The intermediate product is rounded according to the current rounding mode in FCSR ... The results
and flags are as if separate floating-point multiply and add instructions were executed" (p.256).
-/
def MADD_D (fd fr fs ft : W32) : Pseudo Unit := do
  -- vfr <- ValueFPR(fr, D)
  let vfr ← ValueFPR64 (reg fr)
  -- vfs <- ValueFPR(fs, D)
  let vfs ← ValueFPR64 (reg fs)
  -- vft <- ValueFPR(ft, D)
  let vft ← ValueFPR64 (reg ft)
  -- (vfs xfmt vft) combined with vfr, with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.maddD a vfr vfs vft)
  -- StoreFPR(fd, fmt, ...)
  StoreFPR64 (reg fd) r

/-- **MSUB.S fd, fr, fs, ft** — MD00086 Vol II-A Rev 6.06, MSUB.fmt, p.287 (fmt = S).
```
vfr <- ValueFPR(fr, fmt)
vfs <- ValueFPR(fs, fmt)
vft <- ValueFPR(ft, fmt)
StoreFPR(fd, fmt, (vfs xfmt vft) -fmt vfr)
```
"The intermediate product is rounded according to the current rounding mode in FCSR ... The results
and flags are as if separate floating-point multiply and add instructions were executed" (p.287).
-/
def MSUB_S (fd fr fs ft : W32) : Pseudo Unit := do
  -- vfr <- ValueFPR(fr, S)
  let vfr ← ValueFPR32 (reg fr)
  -- vfs <- ValueFPR(fs, S)
  let vfs ← ValueFPR32 (reg fs)
  -- vft <- ValueFPR(ft, S)
  let vft ← ValueFPR32 (reg ft)
  -- (vfs xfmt vft) combined with vfr, with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.msubS a vfr vfs vft)
  -- StoreFPR(fd, fmt, ...)
  StoreFPR32 (reg fd) r

/-- **MSUB.D fd, fr, fs, ft** — MD00086 Vol II-A Rev 6.06, MSUB.fmt, p.287 (fmt = D).
```
vfr <- ValueFPR(fr, fmt)
vfs <- ValueFPR(fs, fmt)
vft <- ValueFPR(ft, fmt)
StoreFPR(fd, fmt, (vfs xfmt vft) -fmt vfr)
```
"The intermediate product is rounded according to the current rounding mode in FCSR ... The results
and flags are as if separate floating-point multiply and add instructions were executed" (p.287).
-/
def MSUB_D (fd fr fs ft : W32) : Pseudo Unit := do
  -- vfr <- ValueFPR(fr, D)
  let vfr ← ValueFPR64 (reg fr)
  -- vfs <- ValueFPR(fs, D)
  let vfs ← ValueFPR64 (reg fs)
  -- vft <- ValueFPR(ft, D)
  let vft ← ValueFPR64 (reg ft)
  -- (vfs xfmt vft) combined with vfr, with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.msubD a vfr vfs vft)
  -- StoreFPR(fd, fmt, ...)
  StoreFPR64 (reg fd) r

/-- **NMADD.S fd, fr, fs, ft** — MD00086 Vol II-A Rev 6.06, NMADD.fmt, p.308 (fmt = S).
```
vfr <- ValueFPR(fr, fmt)
vfs <- ValueFPR(fs, fmt)
vft <- ValueFPR(ft, fmt)
StoreFPR(fd, fmt, vfr +fmt (vfs xfmt vft)   [printed with a leading negation glyph, lost in the text])
```
"The intermediate product is rounded according to the current rounding mode in FCSR ... The results
and flags are as if separate floating-point multiply and add and negate instructions were executed" (p.308).
-/
def NMADD_S (fd fr fs ft : W32) : Pseudo Unit := do
  -- vfr <- ValueFPR(fr, S)
  let vfr ← ValueFPR32 (reg fr)
  -- vfs <- ValueFPR(fs, S)
  let vfs ← ValueFPR32 (reg fs)
  -- vft <- ValueFPR(ft, S)
  let vft ← ValueFPR32 (reg ft)
  -- (vfs xfmt vft) combined with vfr, with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.nmaddS a vfr vfs vft)
  -- StoreFPR(fd, fmt, ...)
  StoreFPR32 (reg fd) r

/-- **NMADD.D fd, fr, fs, ft** — MD00086 Vol II-A Rev 6.06, NMADD.fmt, p.308 (fmt = D).
```
vfr <- ValueFPR(fr, fmt)
vfs <- ValueFPR(fs, fmt)
vft <- ValueFPR(ft, fmt)
StoreFPR(fd, fmt, vfr +fmt (vfs xfmt vft)   [printed with a leading negation glyph, lost in the text])
```
"The intermediate product is rounded according to the current rounding mode in FCSR ... The results
and flags are as if separate floating-point multiply and add and negate instructions were executed" (p.308).
-/
def NMADD_D (fd fr fs ft : W32) : Pseudo Unit := do
  -- vfr <- ValueFPR(fr, D)
  let vfr ← ValueFPR64 (reg fr)
  -- vfs <- ValueFPR(fs, D)
  let vfs ← ValueFPR64 (reg fs)
  -- vft <- ValueFPR(ft, D)
  let vft ← ValueFPR64 (reg ft)
  -- (vfs xfmt vft) combined with vfr, with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.nmaddD a vfr vfs vft)
  -- StoreFPR(fd, fmt, ...)
  StoreFPR64 (reg fd) r

/-- **NMSUB.S fd, fr, fs, ft** — MD00086 Vol II-A Rev 6.06, NMSUB.fmt, p.310 (fmt = S).
```
vfr <- ValueFPR(fr, fmt)
vfs <- ValueFPR(fs, fmt)
vft <- ValueFPR(ft, fmt)
StoreFPR(fd, fmt, (vfs xfmt vft) -fmt vfr   [printed with a leading negation glyph, lost in the text])
```
"The intermediate product is rounded according to the current rounding mode in FCSR ... The results
and flags are as if separate floating-point multiply and add and negate instructions were executed" (p.310).
-/
def NMSUB_S (fd fr fs ft : W32) : Pseudo Unit := do
  -- vfr <- ValueFPR(fr, S)
  let vfr ← ValueFPR32 (reg fr)
  -- vfs <- ValueFPR(fs, S)
  let vfs ← ValueFPR32 (reg fs)
  -- vft <- ValueFPR(ft, S)
  let vft ← ValueFPR32 (reg ft)
  -- (vfs xfmt vft) combined with vfr, with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.nmsubS a vfr vfs vft)
  -- StoreFPR(fd, fmt, ...)
  StoreFPR32 (reg fd) r

/-- **NMSUB.D fd, fr, fs, ft** — MD00086 Vol II-A Rev 6.06, NMSUB.fmt, p.310 (fmt = D).
```
vfr <- ValueFPR(fr, fmt)
vfs <- ValueFPR(fs, fmt)
vft <- ValueFPR(ft, fmt)
StoreFPR(fd, fmt, (vfs xfmt vft) -fmt vfr   [printed with a leading negation glyph, lost in the text])
```
"The intermediate product is rounded according to the current rounding mode in FCSR ... The results
and flags are as if separate floating-point multiply and add and negate instructions were executed" (p.310).
-/
def NMSUB_D (fd fr fs ft : W32) : Pseudo Unit := do
  -- vfr <- ValueFPR(fr, D)
  let vfr ← ValueFPR64 (reg fr)
  -- vfs <- ValueFPR(fs, D)
  let vfs ← ValueFPR64 (reg fs)
  -- vft <- ValueFPR(ft, D)
  let vft ← ValueFPR64 (reg ft)
  -- (vfs xfmt vft) combined with vfr, with FCSR Cause/Flags and CheckFPException
  let a ← Pseudo.get
  let r ← FPResult (IEEE.nmsubD a vfr vfs vft)
  -- StoreFPR(fd, fmt, ...)
  StoreFPR64 (reg fd) r

end Manual.Ops
