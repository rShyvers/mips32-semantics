import Semantics.Step
import Semantics.Env
import Semantics.Specs.WellFormed

/-!
# Defs — vocabulary of the spec statements

The definitions that appear in theorem *statements* but are not part of the simulator itself.
A reviewer must read these to know what the statements say; `Semantics/Statements.lean` (the
`lake comparator` challenge) imports exactly this file on top of the model.

* `Instruction.WellFormed` (re-exported from `WellFormed.lean`): the side condition of `decode_encode`.
* `…Spec` abbreviations: other names for `Step.lean` definitions (the same definition, not a copy).
* The environment layer (`Semantics/Env.lean`: `load`, `hostStep`, `runHosted`) is imported so
  that the statements about the hosted run can be stated; it is not part of the processor.
* `State.RegFilesWF`: both register files have 32 entries.
* `fcsrTrapped`, `fpCompletesS`/`D`/`Cmp`: how an FP arithmetic instruction completes (result written
  and flags accumulated, or Floating Point exception with the destination untouched).
-/

set_option maxRecDepth 4000

/-- Spec-side name for `Step.lean`'s `regIdx` — the same definition, not a copy. -/
abbrev regIdxSpec := regIdx

/-- Spec-side name for `Step.lean`'s `addOverflows` — the same definition, not a copy. -/
abbrev addOverflowsSpec := addOverflows

/-- Spec-side name for `Step.lean`'s `subOverflows` — the same definition, not a copy. -/
abbrev subOverflowsSpec := subOverflows

/-- Spec-side name for `Step.lean`'s `isBranchLike` — the same definition, not a copy. -/
abbrev isBranchLikeSpec := isBranchLike

/-- Spec-side name for `Step.lean`'s `zeroExtByte` — the same definition, not a copy. -/
abbrev zeroExtByteSpec := zeroExtByte

/-- Spec-side name for `Step.lean`'s `setByteSlot` — the same definition, not a copy. -/
abbrev setByteSlotSpec := setByteSlot

/-- Spec-side name for `Step.lean`'s `getByteSlot` — the same definition, not a copy. -/
abbrev getByteSlotSpec := getByteSlot

/-- Spec-side name for `Step.lean`'s `countLeadingZerosFrom` — the same definition, not a copy. -/
abbrev countLeadingZerosFromSpec := countLeadingZerosFrom

/-- Spec-side name for `Step.lean`'s `countLeadingZeros` — the same definition, not a copy. -/
abbrev countLeadingZerosSpec := countLeadingZeros

/-- Spec-side name for `Step.lean`'s `countLeadingOnes` — the same definition, not a copy. -/
abbrev countLeadingOnesSpec := countLeadingOnes

/-- Spec-side name for `Step.lean`'s `signExtLowByte` — the same definition, not a copy. -/
abbrev signExtLowByteSpec := signExtLowByte

/-- Spec-side name for `Step.lean`'s `lowBitsMask` — the same definition, not a copy. -/
abbrev lowBitsMaskSpec := lowBitsMask

/-- Both register files of `s` have 32 entries (`RegFileSize.lean`: an invariant of `step`/`run`,
satisfied by `initialState`). -/
def State.RegFilesWF (s : State) : Prop := s.regs.size = 32 ∧ s.fpRegs.size = 32

/-- Spec-side name for `Env.lean`'s `readCString` — the same definition, not a copy. -/
abbrev readCStringSpec := readCString

/-- Spec-side name for `Env.lean`'s `printStringFuel` — the same definition, not a copy. -/
abbrev printStringFuelSpec := printStringFuel

/-- FCSR after an FP instruction that traps: `Cause` (bits 17..12) becomes
exactly the exceptions `f` of this operation (`E` clear); nothing else
changes — in particular `Flags` are **not** updated. -/
def fcsrTrapped (fcsr : W32) (f : Mips.Fp.Flags) : W32 :=
  (fcsr &&& ~~~Mips.Fp.fcsrCauseMask) ||| ((f.toBits.zeroExtend 32 : BitVec 32) <<< 12)

/-- **How an FP instruction with a 32-bit result completes** (`r.1` the
result bits for `FPR[fd]`, `r.2` the IEEE exceptions it raised), outside a
delay slot. If one of the exceptions is enabled in FCSR, the Floating Point
exception is taken (ExcCode 15) from a state in which only FCSR.Cause has
changed — **the destination is not written**. Otherwise the result is
written, FCSR.Cause is set to `r.2` and `r.2` is ORed into FCSR.Flags
(`Mips.Fp.raiseFlags`), and `pc` advances
(MD00082 Vol I-A Rev 6.01 §6.7.1, p.98-99; Table 6.8, p.94). -/
def fpCompletesS (s : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags) : State :=
  if Mips.Fp.fpeEnabled s.fcsr r.2 then
    takeException { s with fcsr := fcsrTrapped s.fcsr r.2 } excCodeFPE
  else
    { s with fpRegs := s.fpRegs.set! (regIdx fd).val r.1, fcsr := Mips.Fp.raiseFlags s.fcsr r.2,
               pc := s.pc + 4#32 }

/-- As `fpCompletesS`, for a 64-bit result: the low word goes to `FPR[fd]`,
the high word to `FPR[fd+1]` (the `Status.FR = 0` register pair). -/
def fpCompletesD (s : State) (fd : W32) (r : BitVec 64 × Mips.Fp.Flags) : State :=
  if Mips.Fp.fpeEnabled s.fcsr r.2 then
    takeException { s with fcsr := fcsrTrapped s.fcsr r.2 } excCodeFPE
  else
    { s with
          fpRegs := (s.fpRegs.set! (regIdx fd).val (r.1.extractLsb' 0 32)).set!
            (regIdx (fd + 1#32)).val (r.1.extractLsb' 32 32)
          fcsr := Mips.Fp.raiseFlags s.fcsr r.2
          pc := s.pc + 4#32 }

/-- As `fpCompletesS`, for a compare: the "result" is the Boolean `r.1`
written to condition code `cc`; no FP register changes. -/
def fpCompletesCmp (s : State) (cc : W32) (r : Bool × Mips.Fp.Flags) : State :=
  if Mips.Fp.fpeEnabled s.fcsr r.2 then
    takeException { s with fcsr := fcsrTrapped s.fcsr r.2 } excCodeFPE
  else
    { s with fcsr := Mips.Fp.setCC (Mips.Fp.raiseFlags s.fcsr r.2) (ccIdx cc) r.1,
               pc := s.pc + 4#32 }
