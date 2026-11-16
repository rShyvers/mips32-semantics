import Semantics.Manual.Pseudocode
import Semantics.FpOps

/-!
# Manual.FPU — floating-point registers, FCSR, and the IEEE core

MD00086 Vol II-A Rev 6.06 §2.2.2.3 (p.21-24): `ValueFPR`, `StoreFPR`, `CheckFPException`
(Release 6 has no FP condition codes: `FPConditionCode`/`SetFPConditionCode` belong to the removed
C.cond.fmt, BC1F/BC1T and MOVF/MOVT). The FPU is the Release 6 64-bit FPU of this profile:
`Status.FR = 1` read-only (MD00090 Vol III Rev 6.02 §9.32, Table 9.47, p.191), `FIR.Has2008 = 1`,
`FCSR.NAN2008 = ABS2008 = 1` read-only (MD00082 Vol I-A Rev 6.01 Table 6.5, p.88; Table 6.8,
p.93-94). FCSR fields: MD00082 Vol I-A Rev 6.01 §6.5.4, Table 6.8 (p.92-95). Exception handling:
§6.7.1 (p.98-99).

**Shared dependency.** The IEEE 754 arithmetic itself (the exact result, the one correctly rounded
pack under the rounding mode, the five IEEE flags) is the rounding core of `Semantics/FpOps.lean`
(`Mips.Fp.f32Add`, `f32Sub`, `f32Mul`, `f32Div`, `f32Sqrt`, the conversions, and their 64-bit
forms), wrapped below as `Manual.IEEE.*`. Since wave 10 the core's rounding and `ADD`/`SUB`/`MUL`/
`DIV`/`SQRT` are proved correct against the IEEE definition of `Semantics/FpOpsSpec.lean`
(`Semantics/FpOpsCorrect*.lean`; docs/MANUAL-SPEC.md I.8), and since wave 11 every function used here
on every operand (special operands, the NaN rule, conversions, compares; MANUAL-SPEC I.9); what stays
trusted is the reference of `Semantics/FpOpsSpec.lean` and the pins it names. The FCSR bookkeeping around it (Cause, Enables, Flags,
the trap) is transcribed here again from the manual; `Mips.Fp.fpUpdate`, `Mips.Fp.envOf` and the
FCSR masks of `FpOps.lean` are not used.

**What the core fixes that the manual leaves to the implementation** (7R). The model's choices are
kept out of the core where they are cheap to lift:

* `ABS.fmt`/`NEG.fmt` (non-arithmetic with `FCSR.ABS2008 = 1`): transcribed here (`absS` …), the
  core's `f32Abs`/`f32Neg` are not used.
* The upper half of a 64-bit FPR after a 32-bit result is stored: `Oracle.fprUpper`.
* `RECIP.fmt`/`RSQRT.fmt`: `Impl.recipS/D`, `Impl.rsqrtS/D` (accuracy and rounding-mode dependence
  implementation dependent, p.336, p.343).
* The QNaN of a format conversion (`CVT.D.S`, `CVT.S.D`): `Oracle.cvtQNaNToD/ToS`.
* **Remaining core choices — which NaN operand an operation passes to its result, and what a
  conversion makes of a signaling NaN.** "When possible, this QNaN result is one of the operand QNaN
  values" and, with `FCSR.NAN2008 = 1`, "If the chosen input is a SNAN, the only change is to set
  the leftmost/most-significant mantissa bit" (MD00082 Vol I-A Rev 6.01 §6.3.1.5, p.82-83) do not
  say which operand is chosen. The core (`Mips.Fp.Format.nanResult`) passes the first signaling NaN
  in operand order, made quiet, else the first QNaN (SPEC-NOTES §9 item 13); a conversion passes the
  operand made quiet (`Mips.Fp.Format.convertNaN`). These are implementation choices inside the
  trusted core (not lifted to `Impl`: they are parameters of every operation of the core); the
  operand order the spec passes is the printed order of each Operation.
* **Input subnormals with `FCSR.FS = 1`** are flushed by the core (`Mips.Fp.Format.flushIn`: "As of
  Release 5, every input subnormal value is replaced with zero of the same sign", Table 6.8, `FS`,
  p.93), which reads `FS` from `IEEE.env`; outside the comparisons the core also signals Inexact for
  the flush (`Mips.Fp.Format.withFlush`: "Flushing of subnormal input operands in all instructions
  except comparisons causes Inexact exception to be signaled", §6.7.2.4, p.102). The comparisons
  flush without a flag (`flushInS`/`flushInD`; MAX/MIN/MAXA/MINA in the core).
-/

namespace Manual

/-! ## FCSR fields (Vol I-A Table 6.8, p.92-95) -/

/-- `FCSR.RM` (bits 1..0), the rounding mode. -/
def FCSR_RM (a : Arch) : BitVec 2 := a.FCSR.extractLsb' 0 2
/-- `FCSR.Enables` (bits 11..7: V Z O U I). -/
def FCSR_Enables (a : Arch) : BitVec 5 := a.FCSR.extractLsb' 7 5
/-- `FCSR.FS` (bit 24), flush to zero. -/
def FCSR_FS (a : Arch) : Bool := bit a.FCSR 24

/-! ## The IEEE core (shared, `Semantics/FpOps.lean`; proved correct in wave 10) -/

namespace IEEE

/-- The arithmetic environment the IEEE core needs, read from the FCSR fields: rounding mode `RM`,
the `Enables` (an enabled Underflow changes when Underflow is signalled, Vol I-A §6.7.2), and `FS`.
Flag order of `Mips.Fp.Flags.ofBits`: bit 4 = V, 3 = Z, 2 = O, 1 = U, 0 = I (the FCSR order). -/
def env (a : Arch) : Mips.Fp.Env :=
  { rm := Mips.Fp.RoundingMode.ofBits (FCSR_RM a), enables := Mips.Fp.Flags.ofBits (FCSR_Enables a),
    flush := FCSR_FS a }

/-- `fs +S ft` with its IEEE exceptions. -/
def addS (a : Arch) (x y : W32) : W32 × Mips.Fp.Flags := Mips.Fp.f32Add (env a) x y

end IEEE

/-! ## Formats and the FPRs (§2.2.2.3.1-2, p.21-23) -/

/-- The formats `ValueFPR`/`StoreFPR` take (Figure 2.22, p.21). -/
inductive Fmt where | S | W | D | L
  deriving DecidableEq

/-- `FP32RegistersMode` (MD00086 Vol II-A Rev 6.06, "About This Book" symbol table, p.7: "computed
from the FR bit in the Status register"): 1 when `Status.FR = 1`, the 64-bit FPR model in which
"valueFPR ← FPR[fpr]" for every format (Figures 2.22, 2.23, p.22-23). `Status.FR` reads 1 on this
profile (`StatusFR`), so the 32-bit-register arms of `ValueFPR`/`StoreFPR` (`FP32RegistersMode =
0`) are not reached and are not transcribed. -/
def FP32RegistersMode : Bool := true

/-- **`ValueFPR(fpr, fmt)` for a 32-bit format** (Figure 2.22, p.21-22): "S, W, UNINTERPRETED_WORD:
valueFPR ← FPR[fpr]" — the 32-bit value held in the low 32 bits of the 64-bit FPR (§6.6.2, p.98:
"writes a 32-bit result (S or W format) to the low 32-bits of a 64-bit FPR"). -/
def ValueFPR32 (fpr : Fin 32) : Pseudo W32 := fun _ f => (.ok ((f.arch.FPR fpr).extractLsb' 0 32), f)

/-- **`StoreFPR(fpr, fmt, value)` for a 32-bit format** (Figure 2.23, p.22-23): "S, W,
UNINTERPRETED_WORD: FPR[fpr] ← value": the low 32 bits; "Any FPU instruction that writes a 32-bit
result (S or W format) to the low 32-bits of a 64-bit FPR leaves the upper bits of the FPR
UNPREDICTABLE" (MD00082 Vol I-A Rev 6.01 §6.6.2, p.98): `Oracle.fprUpper`. -/
def StoreFPR32 (fpr : Fin 32) (value : W32) : Pseudo Unit := fun c f =>
  (.ok (), { f with arch := { f.arch with
    FPR := update f.arch.FPR fpr (c.oracle.fprUpper f.arch fpr ++ value) } })

/-! ## Exceptions (§2.2.2.3.3, p.23; Vol I-A §6.7.1, p.98-99) -/

/-- **`CheckFPException()`** (Figure 2.24, p.23): "A floating point exception is signaled if the E
bit of the Cause field is a 1 (Unimplemented Operations have no enable) or if any bit in the Cause
field and the corresponding bit in the Enable field are both 1":
```
if ( (FCSR17 = 1) or ((FCSR16..12 and FCSR11..7) ≠ 0)) ) then
   SignalException(FloatingPointException)
endif
```
-/
def CheckFPException : Pseudo Unit := do
  let a ← Pseudo.get
  if bit a.FCSR 17 || (a.FCSR.extractLsb' 12 5 &&& a.FCSR.extractLsb' 7 5) != 0#5 then
    SignalException .FloatingPoint
  else pure ()

/-- **The FCSR side of one FP arithmetic operation** that produced `r.1` and raised the IEEE
exceptions `r.2` (MD00082 Vol I-A Rev 6.01 §6.7.1, p.99): "The Cause bits are written during each
floating point arithmetic operation ... The bit is set to 1 if the corresponding exception condition
arises; otherwise it is set to 0" (so `E`, bit 17, is 0: the core raises no Unimplemented
Operation); then the trap check ("A floating point trap is generated any time both a Cause bit and its
corresponding Enable bit are set"; "a trap occurs before the instruction that causes the trap ... can
complete and write its results"); then, when no trap was taken, "The Flag bits are set to 1 if the
corresponding IEEE exception is raised, otherwise the bits are unchanged ... instructions that trap do
not update the Flag bits". Returns the value to store. -/
def FPResult {α} (r : α × Mips.Fp.Flags) : Pseudo α := do
  let fl : W32 := r.2.toBits.setWidth 32
  Pseudo.modify fun a => { a with FCSR := (a.FCSR &&& ~~~(0x3F#32 <<< 12)) ||| (fl <<< 12) }
  CheckFPException
  Pseudo.modify fun a => { a with FCSR := a.FCSR ||| (fl <<< 2) }
  pure r.1

/-! ## 7B S4 FPU: the rest of the FP vocabulary -/

namespace IEEE

/-- `fs -S ft`. -/
def subS (a : Arch) (x y : W32) : W32 × Mips.Fp.Flags := Mips.Fp.f32Sub (env a) x y
/-- `fs xS ft`. -/
def mulS (a : Arch) (x y : W32) : W32 × Mips.Fp.Flags := Mips.Fp.f32Mul (env a) x y
/-- `fs /S ft`. -/
def divS (a : Arch) (x y : W32) : W32 × Mips.Fp.Flags := Mips.Fp.f32Div (env a) x y
/-- `SquareRoot(fs)`, single. -/
def sqrtS (a : Arch) (x : W32) : W32 × Mips.Fp.Flags := Mips.Fp.f32Sqrt (env a) x
/-- `AbsoluteValue(fs)`, single, with `FCSR.ABS2008 = 1` (ABS.fmt, p.32): "this operation is
non-arithmetic. For this case, both regular floating point numbers and NAN values are treated alike,
only the sign bit is affected by this instruction. No IEEE exception can be generated for this case,
and the FCSRCause and FCSRFlags fields are not modified": the sign bit (31) cleared. -/
def absS (x : W32) : W32 := x &&& ~~~(1#32 <<< 31)
/-- `Negate(fs)`, single, with `FCSR.ABS2008 = 1` (NEG.fmt, p.307: "The value is negated by changing
the sign bit value"; non-arithmetic as `absS`): the sign bit (31) flipped. -/
def negS (x : W32) : W32 := x ^^^ (1#32 <<< 31)

/-- `fs +D ft`. -/
def addD (a : Arch) (x y : BitVec 64) : BitVec 64 × Mips.Fp.Flags := Mips.Fp.f64Add (env a) x y
/-- `fs -D ft`. -/
def subD (a : Arch) (x y : BitVec 64) : BitVec 64 × Mips.Fp.Flags := Mips.Fp.f64Sub (env a) x y
/-- `fs xD ft`. -/
def mulD (a : Arch) (x y : BitVec 64) : BitVec 64 × Mips.Fp.Flags := Mips.Fp.f64Mul (env a) x y
/-- `fs /D ft`. -/
def divD (a : Arch) (x y : BitVec 64) : BitVec 64 × Mips.Fp.Flags := Mips.Fp.f64Div (env a) x y
/-- `SquareRoot(fs)`, double. -/
def sqrtD (a : Arch) (x : BitVec 64) : BitVec 64 × Mips.Fp.Flags := Mips.Fp.f64Sqrt (env a) x
/-- `AbsoluteValue(fs)`, double (as `absS`): the sign bit (63) cleared. -/
def absD (x : BitVec 64) : BitVec 64 := x &&& ~~~(1#64 <<< 63)
/-- `Negate(fs)`, double (as `negS`): the sign bit (63) flipped. -/
def negD (x : BitVec 64) : BitVec 64 := x ^^^ (1#64 <<< 63)

/-- The rounding modes by their number (MD00082 Vol I-A Rev 6.01 Table 6.8, p.92-95: `RM` 0 RN,
1 RZ, 2 RP, 3 RM), as the `convert_and_round` of `ROUND/TRUNC/CEIL/FLOOR.W.fmt` fixes them (pages
342, 441, 128, 186: "rounding mode 0/1/2/3"). -/
def roundingMode (n : BitVec 2) : Mips.Fp.RoundingMode := Mips.Fp.RoundingMode.ofBits n

/-- `ConvertFmt(fs, S, W)` rounding in mode `rm`: the word and the exceptions (Invalid, with the
`FCSR.NAN2008 = 1` default results of Table 6.3, p.82 — 0 for a NaN, `2^31 - 1` too big, `-2^31` too
small; Inexact); the operand flushed per `FCSR.FS`. -/
def toWordS (a : Arch) (rm : Mips.Fp.RoundingMode) (x : W32) : W32 × Mips.Fp.Flags :=
  Mips.Fp.f32ToW32 rm (FCSR_FS a) x
/-- `ConvertFmt(fs, D, W)` rounding in mode `rm`. -/
def toWordD (a : Arch) (rm : Mips.Fp.RoundingMode) (x : BitVec 64) : W32 × Mips.Fp.Flags :=
  Mips.Fp.f64ToW32 rm (FCSR_FS a) x
/-- `ConvertFmt(fs, S, L)` rounding in mode `rm` (Table 6.3: 0 for a NaN, `2^63 - 1` too big, `-2^63`
too small). -/
def toLongS (a : Arch) (rm : Mips.Fp.RoundingMode) (x : W32) : BitVec 64 × Mips.Fp.Flags :=
  Mips.Fp.f32ToW64 rm (FCSR_FS a) x
/-- `ConvertFmt(fs, D, L)` rounding in mode `rm`. -/
def toLongD (a : Arch) (rm : Mips.Fp.RoundingMode) (x : BitVec 64) : BitVec 64 × Mips.Fp.Flags :=
  Mips.Fp.f64ToW64 rm (FCSR_FS a) x
/-- `ConvertFmt(fs, S, D)`, exact (CVT.D.fmt p.153: "If fmt is S or W, then the operation is always
exact"). A QNaN operand gives the oracle's double QNaN `q` (`Oracle.cvtQNaNToD`) without an
exception (Vol I-A §6.3.1.5, p.82); a signaling NaN signals Invalid Operation (§6.3.1.4, p.81). -/
def cvtDS (q : W32 → BitVec 64) (a : Arch) (x : W32) : BitVec 64 × Mips.Fp.Flags :=
  if Mips.Fp.isQNaN32 x then (q x, Mips.Fp.Flags.none) else Mips.Fp.f32ToF64 (FCSR_FS a) x
/-- `ConvertFmt(fs, W, D)`, exact. -/
def cvtDW (x : W32) : BitVec 64 × Mips.Fp.Flags := Mips.Fp.w32ToF64F x
/-- `ConvertFmt(fs, D, S)`, rounded per `FCSR.RM`; a QNaN operand gives the oracle's single QNaN
(`Oracle.cvtQNaNToS`), as `cvtDS`. -/
def cvtSD (q : BitVec 64 → W32) (a : Arch) (x : BitVec 64) : W32 × Mips.Fp.Flags :=
  if Mips.Fp.isQNaN64 x then (q x, Mips.Fp.Flags.none) else Mips.Fp.f64ToF32 (env a) x
/-- `ConvertFmt(fs, W, S)`, rounded per `FCSR.RM`. -/
def cvtSW (a : Arch) (x : W32) : W32 × Mips.Fp.Flags := Mips.Fp.w32ToF32 (env a) x
/-- `ConvertFmt(fs, L, S)`, rounded per `FCSR.RM` (CVT.S.fmt, p.159). -/
def cvtSL (a : Arch) (x : BitVec 64) : W32 × Mips.Fp.Flags := Mips.Fp.w64ToF32 (env a) x
/-- `ConvertFmt(fs, L, D)`, rounded per `FCSR.RM` (CVT.D.fmt, p.153: "converted to a value in double
floating point format and rounded according to the current rounding mode in FCSR"). -/
def cvtDL (a : Arch) (x : BitVec 64) : BitVec 64 × Mips.Fp.Flags := Mips.Fp.w64ToF64 (env a) x

/-- `SNaN(x)`, single. -/
def isSNaNS (x : W32) : Bool := Mips.Fp.isSNaN32 x
/-- `QNaN(x)`, single. -/
def isQNaNS (x : W32) : Bool := Mips.Fp.isQNaN32 x
/-- `SNaN(x)`, double. -/
def isSNaND (x : BitVec 64) : Bool := Mips.Fp.isSNaN64 x
/-- `QNaN(x)`, double. -/
def isQNaND (x : BitVec 64) : Bool := Mips.Fp.isQNaN64 x

-- BEGIN R6-6B
/-- An operand of a comparison as compared, single: with `FCSR.FS = 1` "every input subnormal value
is replaced with zero of the same sign" (MD00082 Vol I-A Rev 6.01 §6.7.2.4, p.102), and "For
floating-point comparisons, the Inexact exception is not signaled when subnormal input operands are
flushed" (same page): no flag. The core's flush. -/
def flushInS (a : Arch) (x : W32) : W32 := BitVec.ofNat 32 (Mips.Fp.binary32.flushIn (FCSR_FS a) x.toNat)
/-- As `flushInS`, double. -/
def flushInD (a : Arch) (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (Mips.Fp.binary64.flushIn (FCSR_FS a) x.toNat)

/-- `ValueFPR(fs, S) <fmt ValueFPR(ft, S)` on two non-NaN operands (the ordering of the core,
`Mips.Fp.f32Relation`; `-0 = +0`: "Comparisons ignore the sign of zero", CMP.condn.fmt, p.136). -/
def ltS (x y : W32) : Bool := (Mips.Fp.f32Relation x y).less
/-- `ValueFPR(fs, S) =fmt ValueFPR(ft, S)` on two non-NaN operands. -/
def eqS (x y : W32) : Bool := (Mips.Fp.f32Relation x y).equal
/-- `<fmt`, double. -/
def ltD (x y : BitVec 64) : Bool := (Mips.Fp.f64Relation x y).less
/-- `=fmt`, double. -/
def eqD (x y : BitVec 64) : Bool := (Mips.Fp.f64Relation x y).equal

/-- `vfd + (vfs * vft)` (`sub = false`) or `vfd - (vfs * vft)` (`sub = true`), single: "The
intermediate product is calculated to infinite precision ... The result sum is calculated to infinite
precision, rounded according to the current rounding mode in FCSR" (MADDF.fmt MSUBF.fmt, p.259), with
its IEEE exceptions; the core's fused operation. -/
def fmaS (a : Arch) (sub : Bool) (d x y : W32) : W32 × Mips.Fp.Flags :=
  Mips.Fp.f32Fma (env a) sub d x y
/-- As `fmaS`, double. -/
def fmaD (a : Arch) (sub : Bool) (d x y : BitVec 64) : BitVec 64 × Mips.Fp.Flags :=
  Mips.Fp.f64Fma (env a) sub d x y

/-- The operations of MAX/MIN/MAXA/MINA.fmt (p.262: "MAX.fmt corresponds to the IEEE 754-2008
operation maxNum", MIN `minNum`, MAXA `maxNumMag`, MINA `minNumMag`), on the core's `MinMaxOp`. -/
abbrev MinMaxOp := Mips.Fp.Format.MinMaxOp

/-- MAX/MIN/MAXA/MINA.S: the Operation of p.263-264 (`SNaN` → Invalid Operation; both NaN → `fs`; one
NaN → the other operand; otherwise `MaxFP`/`MinFP`/`MaxAbsoluteFP`/`MinAbsoluteFP`, Table 4.1 p.264-265
for `±0`), with the IEEE exceptions; the core's operation. -/
def minMaxS (a : Arch) (op : MinMaxOp) (x y : W32) : W32 × Mips.Fp.Flags :=
  Mips.Fp.f32MinMax op (env a) x y
/-- As `minMaxS`, double. -/
def minMaxD (a : Arch) (op : MinMaxOp) (x y : BitVec 64) : BitVec 64 × Mips.Fp.Flags :=
  Mips.Fp.f64MinMax op (env a) x y

/-- `ClassFP(fin, S)` (CLASS.fmt, p.132): "Bits 0 and 1 indicate NaN values: signaling NaN (bit 0) and
quiet NaN (bit 1). Bits 2, 3, 4, 5 classify negative values: infinity (bit 2), normal (bit 3),
subnormal (bit 4), and zero (bit 5). Bits 6, 7, 8, 9 classify positive values ... The input values and
generated bit masks are not affected by the flush-subnormal-to-zero mode FCSR.FS"; "zero extended to
fmt-width bits". The core's class operation. -/
def classS (x : W32) : W32 := Mips.Fp.f32Class x
/-- As `classS`, double. -/
def classD (x : BitVec 64) : BitVec 64 := Mips.Fp.f64Class x

/-- `RoundIntFP(fin, S)` and its exceptions (RINT.fmt, p.337: "rounded to an integral valued floating-
point number in the same format based on the rounding mode bits RM"; "The Inexact exception is
signaled if the result does not have the same numerical value as the input operand"; IEEE 754-2008
`roundToIntegralExact`). The core's operation. -/
def rintS (a : Arch) (x : W32) : W32 × Mips.Fp.Flags := Mips.Fp.f32Rint (env a) x
/-- As `rintS`, double. -/
def rintD (a : Arch) (x : BitVec 64) : BitVec 64 × Mips.Fp.Flags := Mips.Fp.f64Rint (env a) x
-- END R6-6B
end IEEE

/-! ### `ValueFPR` / `StoreFPR` for the 64-bit formats (Figures 2.22, 2.23, p.22-23) -/

/-- **`ValueFPR(fpr, D/L)`** and `UNINTERPRETED_DOUBLEWORD` (Figure 2.22, p.22), with
`FP32RegistersMode` 1 (`Status.FR = 1`): "valueFPR ← FPR[fpr]". -/
def ValueFPR64 (fpr : Fin 32) : Pseudo (BitVec 64) := fun _ f => (.ok (f.arch.FPR fpr), f)

/-- **`StoreFPR(fpr, D/L, value)`** and `UNINTERPRETED_DOUBLEWORD` (Figure 2.23, p.22-23), with
`FP32RegistersMode` 1: "FPR[fpr] ← value". -/
def StoreFPR64 (fpr : Fin 32) (value : BitVec 64) : Pseudo Unit :=
  Pseudo.modify fun a => { a with FPR := update a.FPR fpr value }

end Manual
