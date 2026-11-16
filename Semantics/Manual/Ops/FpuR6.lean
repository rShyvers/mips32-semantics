import Semantics.Manual.FPU

/-!
# Manual.Ops.FpuR6 — the Release 6 FP instructions (MD00086 Vol II-A Rev 6.06)

`CMP.condn.fmt` (p.136-140), `BC1EQZ`/`BC1NEZ` (p.54-55), `SEL.fmt` (p.368), `SELEQZ.fmt`/`SELNEZ.fmt`
(p.371-372), `MADDF.fmt`/`MSUBF.fmt` (p.259-260), `MAX.fmt`/`MIN.fmt`/`MAXA.fmt`/`MINA.fmt`
(p.262-265), `CLASS.fmt` (p.132-133), `RINT.fmt` (p.337-338), for fmt = S and D. The Coprocessor
Unusable check is made for the whole COP1 encoding space before the Operation runs (`Manual.Cycle`).

* A `SignalException(InvalidOperation)` / `SignalFPException(...)` of an Operation, and every
  arithmetic result, go through `FPResult` (FCSR Cause, `CheckFPException`, Flags; MD00082 Vol I-A Rev
  6.01 §6.7.1, p.98-99): "If the Invalid Operation Enable bit is set in the FCSR, no result is written
  and an Invalid Operation exception is taken immediately. Otherwise, the mask result is written into
  FPR fd" (CMP.condn.fmt, p.136).
* `SEL`, `SELEQZ`, `SELNEZ`: "This instruction does not cause data-dependent exceptions. It does not
  trap on NaNs, and the FCSRCause and FCSRFlags fields are not modified" (p.368; p.371 alike), and
  `CLASS` has "No data-dependent exceptions" and no FCSR statement in its Operation (p.132): no
  `FPResult`.
* `StoreFPR(fd, S, …)` of a 32-bit result leaves the upper half of the 64-bit FPR UNPREDICTABLE
  (`StoreFPR32`, `Oracle.fprUpper`); CMP.condn.S, CLASS.S and SELEQZ/SELNEZ.S say so on their pages
  too (p.136, p.132, p.371).
* `ValueFPR(fpr, UNINTERPRETED_WORD)` is the low word of the FPR (`ValueFPR32`).
-/

namespace Manual.Ops

open Manual

/-! ## CMP.condn.fmt -/

/-- The mask a CMP.condn.S writes (p.136: "true is all 1s and false is all 0s, repeated the operand
width of fmt"; the Operation's `ExtendBit.fmt(condition)`). -/
def ExtendBitS (b : Bool) : W32 := if b then BitVec.allOnes 32 else 0#32
/-- As `ExtendBitS`, for CMP.condn.D (64 bits). -/
def ExtendBitD (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0#64

/-- **CMP.condn.S fd, fs, ft** — MD00086 Vol II-A Rev 6.06, CMP.condn.fmt, p.136-140 (fmt = S;
Operation p.140).
```
if SNaN(ValueFPR(fs, fmt)) or SNaN(ValueFPR(ft, fmt)) or
   QNaN(ValueFPR(fs, fmt)) or QNaN(ValueFPR(ft, fmt))
then
   less ← false
   equal ← false
   unordered ← true
   if (SNaN(ValueFPR(fs,fmt)) or SNaN(ValueFPR(ft,fmt))) or
       (cond3 and (QNaN(ValueFPR(fs,fmt)) or QNaN(ValueFPR(ft,fmt)))) then
          SignalException(InvalidOperation)
   endif
   else
       less ← ValueFPR(fs, fmt) <fmt ValueFPR(ft, fmt)
       equal ← ValueFPR(fs, fmt) =fmt ValueFPR(ft, fmt)
       unordered ← false
   endif
   condition ← cond4 xor (
          (cond2 and less)
          or (cond1 and equal)
          or (cond0 and unordered) )
    StoreFPR (fd, fmt, ExtendBit.fmt(condition))
```
`condn` is bits 4..0 of the word (`cond0` = bit 0 … `cond4` = bit 4). The operands are compared after
the input flush of `FCSR.FS = 1`, which for a comparison signals no Inexact (MD00082 Vol I-A Rev 6.01
§6.7.2.4, p.102: "For floating-point comparisons, the Inexact exception is not signaled when subnormal
input operands are flushed"). -/
def CMP_S (cond fd fs ft : W32) : Pseudo Unit := do
  -- ValueFPR(fs, fmt), ValueFPR(ft, fmt); subnormals flushed with FCSR.FS = 1 (`IEEE.flushInS`)
  let a ← Pseudo.get
  let x := IEEE.flushInS a (← ValueFPR32 (reg fs))
  let y := IEEE.flushInS a (← ValueFPR32 (reg ft))
  -- if SNaN(x) or SNaN(y) or QNaN(x) or QNaN(y) then less ← false; equal ← false; unordered ← true
  --   if (SNaN(x) or SNaN(y)) or (cond3 and (QNaN(x) or QNaN(y))) then SignalException(InvalidOperation)
  -- else less ← x <fmt y; equal ← x =fmt y; unordered ← false
  let isNaN := IEEE.isSNaNS x || IEEE.isSNaNS y || IEEE.isQNaNS x || IEEE.isQNaNS y
  let invalid := (IEEE.isSNaNS x || IEEE.isSNaNS y) ||
    (bit cond 3 && (IEEE.isQNaNS x || IEEE.isQNaNS y))
  let less := if isNaN then false else IEEE.ltS x y
  let equal := if isNaN then false else IEEE.eqS x y
  let unordered := isNaN
  -- condition ← cond4 xor ((cond2 and less) or (cond1 and equal) or (cond0 and unordered))
  let condition := bit cond 4 ^^ ((bit cond 2 && less) || (bit cond 1 && equal) || (bit cond 0 && unordered))
  -- the Invalid Operation exception (FCSR Cause, CheckFPException, Flags)
  let r ← FPResult (condition, if invalid then Mips.Fp.Flags.invalidOnly else Mips.Fp.Flags.none)
  -- StoreFPR (fd, fmt, ExtendBit.fmt(condition))
  StoreFPR32 (reg fd) (ExtendBitS r)

/-- **CMP.condn.D fd, fs, ft** — MD00086 Vol II-A Rev 6.06, CMP.condn.fmt, p.136-140 (fmt = D; the
Operation of `CMP_S`, p.140). -/
def CMP_D (cond fd fs ft : W32) : Pseudo Unit := do
  let a ← Pseudo.get
  let x := IEEE.flushInD a (← ValueFPR64 (reg fs))
  let y := IEEE.flushInD a (← ValueFPR64 (reg ft))
  let isNaN := IEEE.isSNaND x || IEEE.isSNaND y || IEEE.isQNaND x || IEEE.isQNaND y
  let invalid := (IEEE.isSNaND x || IEEE.isSNaND y) ||
    (bit cond 3 && (IEEE.isQNaND x || IEEE.isQNaND y))
  let less := if isNaN then false else IEEE.ltD x y
  let equal := if isNaN then false else IEEE.eqD x y
  let unordered := isNaN
  let condition := bit cond 4 ^^ ((bit cond 2 && less) || (bit cond 1 && equal) || (bit cond 0 && unordered))
  let r ← FPResult (condition, if invalid then Mips.Fp.Flags.invalidOnly else Mips.Fp.Flags.none)
  StoreFPR64 (reg fd) (ExtendBitD r)

/-! ## BC1EQZ, BC1NEZ -/

/-- **BC1EQZ ft, offset** — MD00086 Vol II-A Rev 6.06, BC1EQZ BC1NEZ, p.54-55.
```
tmp ← ValueFPR(ft, UNINTERPRETED_WORD)
BC1EQZ: cond ← tmp & 1 = 0
if cond then
   I:     target_PC ← ( PC+4 + sign_extend( offset << 2 )
   I+1:   PC ← target_PC
```
"A 18-bit signed offset (the 16-bit offset field shifted left 2 bits) is added to the address of the
instruction following the branch (not the branch itself) ... Execute the instruction in the delay slot
before the instruction at the target" (p.54): `offset << 2` is `offset || 0^2`, sign-extended. When the
condition is false the delay slot still follows the branch (`Delay.fallThrough`). -/
def BC1EQZ (ft offset : W32) : Pseudo Unit := do
  -- tmp ← ValueFPR(ft, UNINTERPRETED_WORD)
  let tmp ← ValueFPR32 (reg ft)
  -- cond ← tmp & 1 = 0
  let condition := tmp &&& 1#32 == 0#32
  let pc ← PC
  -- I: target_PC ← PC + 4 + sign_extend(offset << 2); I+1: PC ← target_PC
  if condition then I1 (.jump ((pc + 4#32) + sign_extend (imm16 offset ++ 0#2))) else I1 .fallThrough

/-- **BC1NEZ ft, offset** — MD00086 Vol II-A Rev 6.06, BC1EQZ BC1NEZ, p.54-55; as `BC1EQZ` with
```
BC1NEZ: cond ← tmp & 1 ≠ 0
```
-/
def BC1NEZ (ft offset : W32) : Pseudo Unit := do
  let tmp ← ValueFPR32 (reg ft)
  -- cond ← tmp & 1 ≠ 0
  let condition := tmp &&& 1#32 != 0#32
  let pc ← PC
  if condition then I1 (.jump ((pc + 4#32) + sign_extend (imm16 offset ++ 0#2))) else I1 .fallThrough

/-! ## SEL.fmt, SELEQZ.fmt, SELNEZ.fmt -/

/-- **SEL.S fd, fs, ft** — MD00086 Vol II-A Rev 6.06, SEL.fmt, p.368 (fmt = S).
```
tmp ← ValueFPR(fd, UNINTERPRETED_WORD)
cond ← tmp.bit0
if cond then
   tmp ← ValueFPR(ft, fmt)
else
   tmp ← ValueFPR(fs, fmt)
endif
StoreFPR(fd, fmt, tmp)
```
-/
def SEL_S (fd fs ft : W32) : Pseudo Unit := do
  let c ← ValueFPR32 (reg fd)
  let tmp ← if bit c 0 then ValueFPR32 (reg ft) else ValueFPR32 (reg fs)
  StoreFPR32 (reg fd) tmp

/-- **SEL.D fd, fs, ft** — MD00086 Vol II-A Rev 6.06, SEL.fmt, p.368 (fmt = D; the Operation of
`SEL_S`). -/
def SEL_D (fd fs ft : W32) : Pseudo Unit := do
  let c ← ValueFPR32 (reg fd)
  let tmp ← if bit c 0 then ValueFPR64 (reg ft) else ValueFPR64 (reg fs)
  StoreFPR64 (reg fd) tmp

/-- **SELEQZ.S fd, fs, ft** — MD00086 Vol II-A Rev 6.06, SELEQZ.fmt SELNEQZ.fmt, p.371-372 (fmt = S).
```
tmp ← ValueFPR(ft, UNINTERPRETED_WORD)
SELEQZ: cond ← tmp.bit0 = 0
if cond then
   tmp ← ValueFPR(fs, fmt)
else
   tmp ← 0 /* all bits set to zero */
endif
StoreFPR(fd, fmt, tmp)
```
-/
def SELEQZ_S (fd fs ft : W32) : Pseudo Unit := do
  let c ← ValueFPR32 (reg ft)
  let tmp ← if !bit c 0 then ValueFPR32 (reg fs) else pure 0#32
  StoreFPR32 (reg fd) tmp

/-- **SELEQZ.D fd, fs, ft** — p.371-372 (fmt = D; the Operation of `SELEQZ_S`). -/
def SELEQZ_D (fd fs ft : W32) : Pseudo Unit := do
  let c ← ValueFPR32 (reg ft)
  let tmp ← if !bit c 0 then ValueFPR64 (reg fs) else pure 0#64
  StoreFPR64 (reg fd) tmp

/-- **SELNEZ.S fd, fs, ft** — p.371-372 (fmt = S): as `SELEQZ_S` with
```
SELNEZ: cond ← tmp.bit0 ≠ 0
```
-/
def SELNEZ_S (fd fs ft : W32) : Pseudo Unit := do
  let c ← ValueFPR32 (reg ft)
  let tmp ← if bit c 0 then ValueFPR32 (reg fs) else pure 0#32
  StoreFPR32 (reg fd) tmp

/-- **SELNEZ.D fd, fs, ft** — p.371-372 (fmt = D). -/
def SELNEZ_D (fd fs ft : W32) : Pseudo Unit := do
  let c ← ValueFPR32 (reg ft)
  let tmp ← if bit c 0 then ValueFPR64 (reg fs) else pure 0#64
  StoreFPR64 (reg fd) tmp

/-! ## MADDF.fmt, MSUBF.fmt -/

/-- **MADDF.S / MSUBF.S fd, fs, ft** (`sub` = MSUBF) — MD00086 Vol II-A Rev 6.06, MADDF.fmt MSUBF.fmt,
p.259-260 (fmt = S).
```
vfr ← ValueFPR(fr, fmt)
vfs ← ValueFPR(fs, fmt)
vfd ← ValueFPR(fd, fmt)
MADDF.fmt: vinf ← vfd + (vfs * vft)
MSUBF.fmt: vinf ← vfd - (vfs * vft)
StoreFPR(fd, fmt, vinf)
```
(The page reads `vfr ← ValueFPR(fr, fmt)` and prints both lines as `MADDF.fmt`; the instruction has no
`fr` field: the third operand is `ft`, as the Description `FPR[fd] ← FPR[fd] ± (FPR[fs] × FPR[ft])`
and the diagram say.) Cause bits are set and checked (`FPResult`): "Cause bits are ORed into the Flag
bits if no exception is taken" (p.259). -/
def MADDF_S (sub : Bool) (fd fs ft : W32) : Pseudo Unit := do
  let vft ← ValueFPR32 (reg ft)
  let vfs ← ValueFPR32 (reg fs)
  let vfd ← ValueFPR32 (reg fd)
  let a ← Pseudo.get
  let vinf ← FPResult (IEEE.fmaS a sub vfd vfs vft)
  StoreFPR32 (reg fd) vinf

/-- **MADDF.D / MSUBF.D fd, fs, ft** — p.259-260 (fmt = D; the Operation of `MADDF_S`). -/
def MADDF_D (sub : Bool) (fd fs ft : W32) : Pseudo Unit := do
  let vft ← ValueFPR64 (reg ft)
  let vfs ← ValueFPR64 (reg fs)
  let vfd ← ValueFPR64 (reg fd)
  let a ← Pseudo.get
  let vinf ← FPResult (IEEE.fmaD a sub vfd vfs vft)
  StoreFPR64 (reg fd) vinf

/-! ## MAX.fmt, MIN.fmt, MAXA.fmt, MINA.fmt -/

/-- **MAX/MIN/MAXA/MINA.S fd, fs, ft** (`op`) — MD00086 Vol II-A Rev 6.06, p.262-265 (fmt = S).
```
v1 ← ValueFPR(fs,fmt)
v2 ← ValueFPR(ft,fmt)
if SNaN(v1) or SNaN(v2) then
   then SignalException(InvalidOperand) endif
if NaN(v1) and NaN(v2)then
   ftmp ← v1
elseif NaN(v1) then
   ftmp ← v2
elseif NaN(v2) then
   ftmp ← v1
else
   case instruction of
     FMAX.fmt:  ftmp ← MaxFP.fmt(ValueFPR(fs,fmt),ValueFPR(ft,fmt))
     FMIN.fmt:  ftmp ← MinFP.fmt(ValueFPR(fs,fmt),ValueFPR(ft,fmt))
     FMAXA.fmt: ftmp ← MaxAbsoluteFP.fmt(ValueFPR(fs,fmt),ValueFPR(ft,fmt))
     FMINA.fmt: ftmp ← MinAbsoluteFP.fmt(ValueFPR(fs,fmt),ValueFPR(ft,fmt))
   end case
endif
StoreFPR (fd, fmt, ftmp)
```
The whole Operation (the NaN cases, the signed zeros of Table 4.1, p.264-265: "Treat as if the SNaN
were a QNaN (do not quieten the result)") is the core's `IEEE.minMaxS`; the Invalid Operation goes
through `FPResult`. -/
def MINMAX_S (op : IEEE.MinMaxOp) (fd fs ft : W32) : Pseudo Unit := do
  let v1 ← ValueFPR32 (reg fs)
  let v2 ← ValueFPR32 (reg ft)
  let a ← Pseudo.get
  let ftmp ← FPResult (IEEE.minMaxS a op v1 v2)
  StoreFPR32 (reg fd) ftmp

/-- **MAX/MIN/MAXA/MINA.D fd, fs, ft** — p.262-265 (fmt = D; the Operation of `MINMAX_S`). -/
def MINMAX_D (op : IEEE.MinMaxOp) (fd fs ft : W32) : Pseudo Unit := do
  let v1 ← ValueFPR64 (reg fs)
  let v2 ← ValueFPR64 (reg ft)
  let a ← Pseudo.get
  let ftmp ← FPResult (IEEE.minMaxD a op v1 v2)
  StoreFPR64 (reg fd) ftmp

/-! ## CLASS.fmt, RINT.fmt -/

/-- **CLASS.S fd, fs** — MD00086 Vol II-A Rev 6.06, CLASS.fmt, p.132-133 (fmt = S).
```
fin ← ValueFPR(fs,fmt)
masktmp ← ClassFP(fin, fmt)
StoreFPR (fd, fmt, ftmp )
```
(`ftmp` is the `masktmp` of the line before.) No FCSR update: "No data-dependent exceptions are
possible" (p.132). -/
def CLASS_S (fd fs : W32) : Pseudo Unit := do
  let fin ← ValueFPR32 (reg fs)
  StoreFPR32 (reg fd) (IEEE.classS fin)

/-- **CLASS.D fd, fs** — p.132-133 (fmt = D). -/
def CLASS_D (fd fs : W32) : Pseudo Unit := do
  let fin ← ValueFPR64 (reg fs)
  StoreFPR64 (reg fd) (IEEE.classD fin)

/-- **RINT.S fd, fs** — MD00086 Vol II-A Rev 6.06, RINT.fmt, p.337-338 (fmt = S).
```
fin ← ValueFPR(fs,fmt)
ftmp ← RoundIntFP(fin, fmt)
if( fin ≠ ftmp ) SignalFPException(InExact)
StoreFPR (fd, fmt, ftmp )
```
`RoundIntFP` and its Inexact are the core's `IEEE.rintS`, under FCSR.RM; the exceptions go through
`FPResult` ("Floating Point Exceptions: Unimplemented Operation, Invalid Operation, Inexact, Overflow,
Underflow", p.338). -/
def RINT_S (fd fs : W32) : Pseudo Unit := do
  let fin ← ValueFPR32 (reg fs)
  let a ← Pseudo.get
  let ftmp ← FPResult (IEEE.rintS a fin)
  StoreFPR32 (reg fd) ftmp

/-- **RINT.D fd, fs** — p.337-338 (fmt = D). -/
def RINT_D (fd fs : W32) : Pseudo Unit := do
  let fin ← ValueFPR64 (reg fs)
  let a ← Pseudo.get
  let ftmp ← FPResult (IEEE.rintD a fin)
  StoreFPR64 (reg fd) ftmp

end Manual.Ops
