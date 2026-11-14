import Semantics.Manual.FPU

/-!
# Manual.Ops.FpuArith — FP arithmetic (MD00086 Vol II-A Rev 6.06)

Sub-wave 7A transcribes the pilot `ADD.S`. The Coprocessor Unusable check (`Status.CU1 = 0`) is made
for the whole COP1 encoding space before the Operation runs (MD00090 Vol III Rev 6.02 §6.2.22,
p.100; `Manual.Cycle`).
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

end Manual.Ops
