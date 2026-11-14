import Semantics.Manual.Pseudocode
import Semantics.FpOps

/-!
# Manual.FPU — floating-point registers, FCSR, and the IEEE core

MD00086 Vol II-A Rev 6.06 §2.2.2.3 (p.21-24): `ValueFPR`, `StoreFPR`, `CheckFPException`,
`FPConditionCode`, `SetFPConditionCode`. FCSR fields: MD00082 Vol I-A Rev 6.01 §6.5.4, Table 6.8
(p.92-95). Exception handling: §6.7.1 (p.98-99).

**Trusted dependency.** The IEEE 754 arithmetic itself (the exact result, the one correctly rounded
pack under the rounding mode, the five IEEE flags) is the rounding core of `Semantics/FpOps.lean`
(`Mips.Fp.f32Add` …), wrapped below as `Manual.IEEE.*`. The FCSR bookkeeping around it (Cause,
Enables, Flags, the trap) is transcribed here again from the manual; `Mips.Fp.fpUpdate`,
`Mips.Fp.envOf` and the FCSR masks of `FpOps.lean` are not used.
-/

namespace Manual

/-! ## FCSR fields (Vol I-A Table 6.8, p.92-95) -/

/-- `FCSR.RM` (bits 1..0), the rounding mode. -/
def FCSR_RM (a : Arch) : BitVec 2 := a.FCSR.extractLsb' 0 2
/-- `FCSR.Enables` (bits 11..7: V Z O U I). -/
def FCSR_Enables (a : Arch) : BitVec 5 := a.FCSR.extractLsb' 7 5
/-- `FCSR.FS` (bit 24), flush to zero. -/
def FCSR_FS (a : Arch) : Bool := bit a.FCSR 24

/-! ## The IEEE core (trusted, `Semantics/FpOps.lean`) -/

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

end Manual
