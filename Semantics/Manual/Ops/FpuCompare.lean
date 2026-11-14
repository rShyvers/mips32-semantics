import Semantics.Manual.FPU

/-!
# Manual.Ops.FpuCompare — FP compare (MD00086 Vol II-A Rev 6.06), 7B S4

`C.cond.fmt` for S and D. The Operation signals `InvalidOperation` for a signaling NaN, and for a
quiet NaN when `cond3` is set. This is the FP exception of Vol I-A §6.7.1 (p.98-99): the `Cause.V`
bit is set, and the exception is taken only "If the Invalid Operation Enable bit is set in the FCSR,
no result is written and an Invalid Operation exception is taken immediately. Otherwise, the Boolean
result is written into condition code CC" (C.cond.fmt, p.110), the `Flags.V` bit being set: that is
`FPResult`. The `PS` format is not in the profile (SPEC-NOTES §9 item 13).

`cc` is the 3-bit field (bits 10..8) of the format diagram (C.cond.fmt, p.110), so the condition code
written is `(low cc 3)` (7C S4a: the transcription used the whole `W32` operand of `Instruction.cCondS`,
which for a value ≥ 8 named no condition code; the diagram has only three bits).
-/

namespace Manual.Ops

open Manual

/-- **C.cond.S cc, fs, ft** — MD00086 Vol II-A Rev 6.06, C.cond.fmt, p.110-113 (fmt = S; the
format diagram is on p.110, the Operation on p.112-113).
```
if SNaN(ValueFPR(fs, fmt)) or SNaN(ValueFPR(ft, fmt)) or
   QNaN(ValueFPR(fs, fmt)) or QNaN(ValueFPR(ft, fmt)) then
   less <- false
   equal <- false
   unordered <- true
   if (SNaN(ValueFPR(fs,fmt)) or SNaN(ValueFPR(ft,fmt))) or
      (cond3 and (QNaN(ValueFPR(fs,fmt)) or QNaN(ValueFPR(ft,fmt)))) then
      SignalException(InvalidOperation)
   endif
else
   less <- ValueFPR(fs, fmt) <fmt ValueFPR(ft, fmt)
   equal <- ValueFPR(fs, fmt) =fmt ValueFPR(ft, fmt)
   unordered <- false
endif
condition <- (cond2 and less) or (cond1 and equal) or (cond0 and unordered)
SetFPConditionCode(cc, condition)
``` -/
def C_cond_S (cond cc fs ft : W32) : Pseudo Unit := do
  let x ← ValueFPR32 (reg fs)
  let y ← ValueFPR32 (reg ft)
  -- if SNaN(x) or SNaN(y) or QNaN(x) or QNaN(y) then
  --    less <- false; equal <- false; unordered <- true
  --    if (SNaN(x) or SNaN(y)) or (cond3 and (QNaN(x) or QNaN(y))) then SignalException(InvalidOperation)
  -- else less <- x <fmt y; equal <- x =fmt y; unordered <- false
  let isNaN := IEEE.isSNaNS x || IEEE.isSNaNS y || IEEE.isQNaNS x || IEEE.isQNaNS y
  let invalid := (IEEE.isSNaNS x || IEEE.isSNaNS y) ||
    (bit cond 3 && (IEEE.isQNaNS x || IEEE.isQNaNS y))
  let less := if isNaN then false else IEEE.ltS x y
  let equal := if isNaN then false else IEEE.eqS x y
  let unordered := isNaN
  -- condition <- (cond2 and less) or (cond1 and equal) or (cond0 and unordered)
  let condition := (bit cond 2 && less) || (bit cond 1 && equal) || (bit cond 0 && unordered)
  -- the Invalid Operation exception (FCSR Cause, CheckFPException, Flags)
  let r ← FPResult (condition, if invalid then Mips.Fp.Flags.invalidOnly else Mips.Fp.Flags.none)
  -- SetFPConditionCode(cc, condition); `cc` is the 3-bit field 10..8 of the format diagram (p.110)
  SetFPConditionCode (low cc 3).toNat r

/-- **C.cond.D cc, fs, ft** — MD00086 Vol II-A Rev 6.06, C.cond.fmt, p.110-113 (fmt = D; the
format diagram is on p.110, the Operation on p.112-113).
```
if SNaN(ValueFPR(fs, fmt)) or SNaN(ValueFPR(ft, fmt)) or
   QNaN(ValueFPR(fs, fmt)) or QNaN(ValueFPR(ft, fmt)) then
   less <- false
   equal <- false
   unordered <- true
   if (SNaN(ValueFPR(fs,fmt)) or SNaN(ValueFPR(ft,fmt))) or
      (cond3 and (QNaN(ValueFPR(fs,fmt)) or QNaN(ValueFPR(ft,fmt)))) then
      SignalException(InvalidOperation)
   endif
else
   less <- ValueFPR(fs, fmt) <fmt ValueFPR(ft, fmt)
   equal <- ValueFPR(fs, fmt) =fmt ValueFPR(ft, fmt)
   unordered <- false
endif
condition <- (cond2 and less) or (cond1 and equal) or (cond0 and unordered)
SetFPConditionCode(cc, condition)
``` -/
def C_cond_D (cond cc fs ft : W32) : Pseudo Unit := do
  let x ← ValueFPR64 (reg fs)
  let y ← ValueFPR64 (reg ft)
  -- if SNaN(x) or SNaN(y) or QNaN(x) or QNaN(y) then
  --    less <- false; equal <- false; unordered <- true
  --    if (SNaN(x) or SNaN(y)) or (cond3 and (QNaN(x) or QNaN(y))) then SignalException(InvalidOperation)
  -- else less <- x <fmt y; equal <- x =fmt y; unordered <- false
  let isNaN := IEEE.isSNaND x || IEEE.isSNaND y || IEEE.isQNaND x || IEEE.isQNaND y
  let invalid := (IEEE.isSNaND x || IEEE.isSNaND y) ||
    (bit cond 3 && (IEEE.isQNaND x || IEEE.isQNaND y))
  let less := if isNaN then false else IEEE.ltD x y
  let equal := if isNaN then false else IEEE.eqD x y
  let unordered := isNaN
  -- condition <- (cond2 and less) or (cond1 and equal) or (cond0 and unordered)
  let condition := (bit cond 2 && less) || (bit cond 1 && equal) || (bit cond 0 && unordered)
  -- the Invalid Operation exception (FCSR Cause, CheckFPException, Flags)
  let r ← FPResult (condition, if invalid then Mips.Fp.Flags.invalidOnly else Mips.Fp.Flags.none)
  -- SetFPConditionCode(cc, condition); `cc` is the 3-bit field 10..8 of the format diagram (p.110)
  SetFPConditionCode (low cc 3).toNat r

end Manual.Ops
