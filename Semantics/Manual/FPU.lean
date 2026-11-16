import Semantics.Manual.Pseudocode
import Semantics.FpOps

/-!
# Manual.FPU — floating-point registers, FCSR, and the IEEE core

MD00086 Vol II-A Rev 6.06 §2.2.2.3 (p.21-24): `ValueFPR`, `StoreFPR`, `CheckFPException`
(Release 6 has no FP condition codes: `FPConditionCode`/`SetFPConditionCode` belong to the removed
C.cond.fmt, BC1F/BC1T and MOVF/MOVT).
-- W5: the FPU here is the pre-Release 6 32-bit FPU (`Status.FR = 0`, `FIR.Has2008 = 0`); this
-- profile's Release 6 FPU (`FR = 1`, NAN2008/ABS2008) replaces it. FCSR fields: MD00082 Vol I-A Rev 6.01 §6.5.4, Table 6.8
(p.92-95). Exception handling: §6.7.1 (p.98-99).

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

* `ABS.fmt`/`NEG.fmt` with a NaN operand: transcribed here (`signOpS`/`signOpD`) with the reading
  `Oracle.absNegNaN`; the core's `f32Abs`/`f32Neg` are not used.
* `RECIP.fmt`/`RSQRT.fmt`: `Impl.recipS/D`, `Impl.rsqrtS/D` (accuracy and rounding-mode dependence
  implementation dependent, p.336, p.343).
* The QNaN of a format conversion (`CVT.D.S`, `CVT.S.D`): `Oracle.cvtQNaNToD/ToS`.
* **Remaining core choice — which QNaN an operation with several QNaN operands returns.** "When
  possible, this QNaN result is one of the operand QNaN values" (MD00082 Vol I-A Rev 6.01 §6.3.1.5,
  p.82) does not say which one. The core (`Mips.Fp.Format.nanResult`) returns the first QNaN in
  operand order (SPEC-NOTES §9 item 13). This is an implementation choice inside the trusted core
  (not lifted to `Impl`: it is a parameter of every binary operation of the core); the operand
  order the spec passes is the printed order of each Operation.
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

/-- **`ValueFPR(fpr, fmt)` for a 32-bit format** (Figure 2.22, p.21-22): "S, W, UNINTERPRETED_WORD:
valueFPR ← FPR[fpr]". -/
def ValueFPR32 (fpr : Fin 32) : Pseudo W32 := fun _ f => (.ok (f.arch.FPR fpr), f)

/-- **`StoreFPR(fpr, fmt, value)` for a 32-bit format** (Figure 2.23, p.22-23): "S, W,
UNINTERPRETED_WORD: FPR[fpr] ← value". -/
def StoreFPR32 (fpr : Fin 32) (value : W32) : Pseudo Unit :=
  Pseudo.modify fun a => { a with FPR := update a.FPR fpr value }

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
/-- `AbsoluteValue(fs)` / `Negate(fs)` on a 32-bit pattern, arithmetic (`FIR.Has2008 = 0`; ABS.fmt
p.32, NEG.fmt p.307: "If FIRHas2008=0 or FCSRABS2008=0 then this operation is arithmetic. For
this case, any NaN operand signals invalid operation"; NEG: "The value is negated by changing the
sign bit value"). `sgn` computes the sign-changed pattern. A signaling NaN: Invalid Operation and,
untrapped, the default QNaN (Vol I-A §6.3.1.4 p.81, Table 6.3 p.82). A quiet NaN: the reading
`r` (`Oracle.absNegNaN`). Anything else: `sgn x`, no exception. -/
def signOpS (r : AbsNegNaN) (sgn : W32 → W32) (x : W32) : W32 × Mips.Fp.Flags :=
  if Mips.Fp.isSNaN32 x then (Mips.Fp.defaultQNaN32, Mips.Fp.Flags.invalidOnly)
  else if Mips.Fp.isQNaN32 x then
    match r with
    | .A => (x, Mips.Fp.Flags.invalidOnly)
    | .A' => (sgn x, Mips.Fp.Flags.invalidOnly)
    | .B => (sgn x, Mips.Fp.Flags.none)
  else (sgn x, Mips.Fp.Flags.none)

/-- `AbsoluteValue(fs)`, single: the sign bit (31) cleared. -/
def absS (r : AbsNegNaN) (x : W32) : W32 × Mips.Fp.Flags := signOpS r (fun v => v &&& ~~~(1#32 <<< 31)) x
/-- `Negate(fs)`, single: the sign bit (31) flipped. -/
def negS (r : AbsNegNaN) (x : W32) : W32 × Mips.Fp.Flags := signOpS r (fun v => v ^^^ (1#32 <<< 31)) x

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
/-- As `signOpS`, on a 64-bit pattern. -/
def signOpD (r : AbsNegNaN) (sgn : BitVec 64 → BitVec 64) (x : BitVec 64) :
    BitVec 64 × Mips.Fp.Flags :=
  if Mips.Fp.isSNaN64 x then (Mips.Fp.defaultQNaN64, Mips.Fp.Flags.invalidOnly)
  else if Mips.Fp.isQNaN64 x then
    match r with
    | .A => (x, Mips.Fp.Flags.invalidOnly)
    | .A' => (sgn x, Mips.Fp.Flags.invalidOnly)
    | .B => (sgn x, Mips.Fp.Flags.none)
  else (sgn x, Mips.Fp.Flags.none)

/-- `AbsoluteValue(fs)`, double: the sign bit (63) cleared. -/
def absD (r : AbsNegNaN) (x : BitVec 64) : BitVec 64 × Mips.Fp.Flags :=
  signOpD r (fun v => v &&& ~~~(1#64 <<< 63)) x
/-- `Negate(fs)`, double: the sign bit (63) flipped. -/
def negD (r : AbsNegNaN) (x : BitVec 64) : BitVec 64 × Mips.Fp.Flags :=
  signOpD r (fun v => v ^^^ (1#64 <<< 63)) x

/-- The rounding modes by their number (MD00082 Vol I-A Rev 6.01 Table 6.8, p.92-95: `RM` 0 RN,
1 RZ, 2 RP, 3 RM), as the `convert_and_round` of `ROUND/TRUNC/CEIL/FLOOR.W.fmt` fixes them (pages
342, 441, 128, 186: "rounding mode 0/1/2/3"). -/
def roundingMode (n : BitVec 2) : Mips.Fp.RoundingMode := Mips.Fp.RoundingMode.ofBits n

/-- `ConvertFmt(fs, S, W)` rounding in mode `rm`: the word and the exceptions (Invalid, with the
default result `2^31 - 1`, for Infinity, NaN and out of range, p.342; Inexact). -/
def toWordS (rm : Mips.Fp.RoundingMode) (x : W32) : W32 × Mips.Fp.Flags := Mips.Fp.f32ToW32 rm x
/-- `ConvertFmt(fs, D, W)` rounding in mode `rm`. -/
def toWordD (rm : Mips.Fp.RoundingMode) (x : BitVec 64) : W32 × Mips.Fp.Flags :=
  Mips.Fp.f64ToW32 rm x
/-- `ConvertFmt(fs, S, D)`, exact (CVT.D.fmt p.153: "If fmt is S or W, then the operation is always
exact"). A QNaN operand gives the oracle's double QNaN `q` (`Oracle.cvtQNaNToD`) without an
exception (Vol I-A §6.3.1.5, p.82); a signaling NaN signals Invalid Operation (§6.3.1.4, p.81). -/
def cvtDS (q : W32 → BitVec 64) (x : W32) : BitVec 64 × Mips.Fp.Flags :=
  if Mips.Fp.isQNaN32 x then (q x, Mips.Fp.Flags.none) else Mips.Fp.f32ToF64 x
/-- `ConvertFmt(fs, W, D)`, exact. -/
def cvtDW (x : W32) : BitVec 64 × Mips.Fp.Flags := Mips.Fp.w32ToF64F x
/-- `ConvertFmt(fs, D, S)`, rounded per `FCSR.RM`; a QNaN operand gives the oracle's single QNaN
(`Oracle.cvtQNaNToS`), as `cvtDS`. -/
def cvtSD (q : BitVec 64 → W32) (a : Arch) (x : BitVec 64) : W32 × Mips.Fp.Flags :=
  if Mips.Fp.isQNaN64 x then (q x, Mips.Fp.Flags.none) else Mips.Fp.f64ToF32 (env a) x
/-- `ConvertFmt(fs, W, S)`, rounded per `FCSR.RM`. -/
def cvtSW (a : Arch) (x : W32) : W32 × Mips.Fp.Flags := Mips.Fp.w32ToF32 (env a) x

/-- `SNaN(x)`, single. -/
def isSNaNS (x : W32) : Bool := Mips.Fp.isSNaN32 x
/-- `QNaN(x)`, single. -/
def isQNaNS (x : W32) : Bool := Mips.Fp.isQNaN32 x
/-- `SNaN(x)`, double. -/
def isSNaND (x : BitVec 64) : Bool := Mips.Fp.isSNaN64 x
/-- `QNaN(x)`, double. -/
def isQNaND (x : BitVec 64) : Bool := Mips.Fp.isQNaN64 x
end IEEE

/-! ### `ValueFPR` / `StoreFPR` for the 64-bit formats (Figures 2.22, 2.23, p.22-23) -/

/-- `FP32RegistersMode` (MD00086 Vol II-A Rev 6.06, "About This Book" symbol table, p.7: "computed
from the FR bit in the Status register"): 0 when the FPU has 32 32-bit FPRs (`Status.FR = 0`,
bit 26). On this profile `Status.FR` reads 0 (not writable, `Manual/CP0.lean`). -/
def FP32RegistersMode : Bool := false

/-- **`ValueFPR(fpr, D)`** and `UNINTERPRETED_DOUBLEWORD` (Figure 2.22, p.22), 32-bit FPR model:
```
if (FP32RegistersMode = 0)
   if (fpr_0 != 0) then valueFPR <- UNPREDICTABLE
   else valueFPR <- FPR[fpr+1]31..0 || FPR[fpr]31..0
   endif
else valueFPR <- FPR[fpr] endif
```
(The comparison glyphs of the pseudocode are lost in the text extraction; the 32-bit model is the
one where the doubleword is a pair of registers, "In MIPS32 Release 1 ... 64-bit data types are
stored in even-odd pairs of FPRs", p.7.) The `FR = 1` arm names a 64-bit FPR, which `Arch.FPR` does
not have; it is unreachable here. -/
def ValueFPR64 (fpr : Fin 32) : Pseudo (BitVec 64) := fun c f =>
  if FP32RegistersMode == false then
    if bit (BitVec.ofNat 5 fpr.val) 0 then (.ok (c.oracle.fprOddRead f.arch fpr), f)
    else (.ok (f.arch.FPR (fpr + 1) ++ f.arch.FPR fpr), f)
  else (.ok (f.arch.FPR (fpr + 1) ++ f.arch.FPR fpr), f)

/-- **`StoreFPR(fpr, D, value)`** and `UNINTERPRETED_DOUBLEWORD` (Figure 2.23, p.22-23), 32-bit FPR
model:
```
if (fpr_0 != 0) then UNPREDICTABLE
else FPR[fpr] <- UNPREDICTABLE32 || value31..0 ; FPR[fpr+1] <- UNPREDICTABLE32 || value63..32
```
`UNPREDICTABLE32` is the upper half of a 64-bit register, which a 32-bit FPR does not have. The odd
`fpr` case is `Oracle.fprOddWrite` (an exception, a state, or no write). -/
def StoreFPR64 (fpr : Fin 32) (value : BitVec 64) : Pseudo Unit := fun c f =>
  if bit (BitVec.ofNat 5 fpr.val) 0 then resolve (c.oracle.fprOddWrite f.arch fpr value) c f
  else
    (.ok (), { f with arch := { f.arch with
      FPR := update (update f.arch.FPR fpr (value.extractLsb' 0 32)) (fpr + 1)
        (value.extractLsb' 32 32) } })


end Manual
