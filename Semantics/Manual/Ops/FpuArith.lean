import Semantics.Manual.FPU

/-!
# Manual.Ops.FpuArith — FP arithmetic (MD00086 Vol II-A Rev 6.06)

The S and D arithmetic: `ADD.fmt`, `SUB.fmt`, `MUL.fmt`, `DIV.fmt`, `SQRT.fmt`, `ABS.fmt`, `NEG.fmt`, `RECIP.fmt`, `RSQRT.fmt` (Release 6
removed `MADD.fmt`, `MSUB.fmt`, `NMADD.fmt`, `NMSUB.fmt`). The Coprocessor Unusable check (`Status.CU1 = 0`)
is made for the whole COP1 encoding space before the Operation runs (MD00090 Vol III Rev 6.02
§6.2.22, p.100; `Manual.Cycle`). Every arithmetic result goes through `FPResult` (FCSR Cause,
`CheckFPException`, Flags; MD00082 Vol I-A Rev 6.01 §6.7.1, p.98-99). The paired-single format `PS`
is not part of the profile: "ADD.PS has been removed in Release 6" (ADD.fmt, p.34; likewise the other
`.PS` forms), so there is no `PS` arm (SPEC-NOTES §9 item 13).
Transcribed for the Release 6 FPU of this profile (`FR = 1`, `FCSR.NAN2008 = ABS2008 = 1`: `ABS`
and `NEG` are non-arithmetic, ABS.fmt p.32, NEG.fmt p.307).
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
  -- AbsoluteValue(ValueFPR(fs, fmt)); with FCSR.ABS2008 = 1 the operation is non-arithmetic (p.32):
  -- "No IEEE exception can be generated for this case, and the FCSRCause and FCSRFlags fields are
  -- not modified" (no `FPResult`)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR32 (reg fd) (IEEE.absS x)

/-- **ABS.D fd, fs** — MD00086 Vol II-A Rev 6.06, ABS.fmt, p.32 (fmt = D).
```
StoreFPR(fd, fmt, AbsoluteValue(ValueFPR(fs, fmt)))
```
-/
def ABS_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  -- AbsoluteValue(ValueFPR(fs, fmt)); with FCSR.ABS2008 = 1 the operation is non-arithmetic (p.32):
  -- "No IEEE exception can be generated for this case, and the FCSRCause and FCSRFlags fields are
  -- not modified" (no `FPResult`)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR64 (reg fd) (IEEE.absD x)

/-- **NEG.S fd, fs** — MD00086 Vol II-A Rev 6.06, NEG.fmt, p.307 (fmt = S).
```
StoreFPR(fd, fmt, Negate(ValueFPR(fs, fmt)))
```
-/
def NEG_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  -- Negate(ValueFPR(fs, fmt)); with FCSR.ABS2008 = 1 the operation is non-arithmetic (p.307):
  -- "No IEEE exception can be generated for this case, and the FCSRCause and FCSRFlags fields are
  -- not modified" (no `FPResult`)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR32 (reg fd) (IEEE.negS x)

/-- **NEG.D fd, fs** — MD00086 Vol II-A Rev 6.06, NEG.fmt, p.307 (fmt = D).
```
StoreFPR(fd, fmt, Negate(ValueFPR(fs, fmt)))
```
-/
def NEG_D (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, D)
  let x ← ValueFPR64 (reg fs)
  -- Negate(ValueFPR(fs, fmt)); with FCSR.ABS2008 = 1 the operation is non-arithmetic (p.307):
  -- "No IEEE exception can be generated for this case, and the FCSRCause and FCSRFlags fields are
  -- not modified" (no `FPResult`)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR64 (reg fd) (IEEE.negD x)

/-- **RECIP.S fd, fs** — MD00086 Vol II-A Rev 6.06, RECIP.fmt, p.336 (fmt = S).
```
StoreFPR(fd, fmt, 1.0 / valueFPR(fs, fmt))
```
-/
def RECIP_S (fd fs : W32) : Pseudo Unit := do
  -- ValueFPR(fs, S)
  let x ← ValueFPR32 (reg fs)
  -- 1.0 / valueFPR(fs, fmt): the implementation's approximation (`Impl.recipS`, p.336)
  let i ← Pseudo.impl
  let a ← Pseudo.get
  let r ← FPResult (i.recipS (IEEE.env a) x)
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
  -- 1.0 / valueFPR(fs, fmt): the implementation's approximation (`Impl.recipD`, p.336)
  let i ← Pseudo.impl
  let a ← Pseudo.get
  let r ← FPResult (i.recipD (IEEE.env a) x)
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
  -- 1.0 / SquareRoot(valueFPR(fs, fmt)): the implementation's approximation (`Impl.rsqrtS`, p.343)
  let i ← Pseudo.impl
  let a ← Pseudo.get
  let r ← FPResult (i.rsqrtS (IEEE.env a) x)
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
  -- 1.0 / SquareRoot(valueFPR(fs, fmt)): the implementation's approximation (`Impl.rsqrtD`, p.343)
  let i ← Pseudo.impl
  let a ← Pseudo.get
  let r ← FPResult (i.rsqrtD (IEEE.env a) x)
  -- StoreFPR (fd, fmt, ...)
  StoreFPR64 (reg fd) r

end Manual.Ops
