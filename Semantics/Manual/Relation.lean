import Semantics.Manual.Cycle

/-!
# Manual.Relation — the manual's relation, the limits on its choices, and its choice points (7D, 8)

`InstructionTime impl oracle dec` is deterministic once an oracle is given. The manual itself allows
every outcome some *valid* oracle gives.

**The limits** (MD00086 Vol II-A Rev 6.06 §1.2.1, p.3-4). "UNPREDICTABLE results or operations have
several implementation restrictions":

1. "Implementations of operations generating UNPREDICTABLE results must not depend on any data source
   (memory or internal state) which is inaccessible in the current processor mode" (p.3):
   non-interference, `NIValue`/`NIOutcome` on every UNPREDICTABLE field of the oracle: in User Mode,
   two states that agree on the state accessible in that mode (`AccessibleSame`) get the same value,
   or outcomes that agree on that state (`OutcomeAgree`).
2. "UNPREDICTABLE operations must not read, write, or modify the contents of memory or internal state
   which is inaccessible in the current processor mode. For example, UNPREDICTABLE operations executed
   in user mode must not access memory or internal state that is only accessible in Kernel Mode or
   Debug Mode or in another process" (p.4): the inaccessible state is unchanged (`InaccessibleSame`,
   in `UnpredictableLimits`). "Must not read" is restriction 1 again.
3. "UNPREDICTABLE operations must not halt or hang the processor" (p.4): the state does not enter the
   lower power mode (`LowPower` unchanged, in `UnpredictableLimits`; a non-terminating sequence of
   instruction times is not a property of one instruction time).

A model-side strengthening (no sentence of §1.2 states it): an UNPREDICTABLE or UNDEFINED outcome
leaves the hardware interrupt inputs `HW` unchanged (they are inputs, MD00090 Vol III Rev 6.02
Table 6.2, p.73, read through the read-only `Cause.IP7..IP2`, Table 9.52, p.211), as a Reset does.

The state inaccessible in User Mode: the physical memory that no User Mode address reaches (with
`ERL = 0`, kuseg `0x0000_0000`–`0x7FFF_FFFF` maps to physical `0x4000_0000`–`0xBFFF_FFFF`, MD00090
Vol III Rev 6.02 Table A.1, p.313-314; `FixedMapping`; "an attempt to reference kseg0 from User Mode
still results in an address error exception", §A.1.1, p.313), and the CP0 registers unless `CU0 = 1`
("Coprocessor 0 is usable": "The processor is running in Kernel Mode or Debug Mode ... The CU0 bit in
the Status register is 1", Vol III §3.5.3, p.23; `CP0Usable`).

UNDEFINED operations (`cp0Undefined`: MTC0/MFC0 of a register CP0 does not contain;
`ebaseWriteBEV0`) have one restriction only: "UNDEFINED operations or behavior must not cause the
processor to hang" (MD00086 Vol II-A Rev 6.06 §1.2.2, p.4; "UNDEFINED operations or behavior may
cause data loss"): `UndefinedOutcomeValid` (with the `HW` clause above).

The value fields that are not UNPREDICTABLE results are not restricted: `causeCE` ("The CE field is
loaded, but not defined", Vol III §6.2.3, p.87), `storeClearsLL`/`loadClearsLL` ("success is not
predictable", SC p.347-348). The QNaN fields must give a QNaN ("a QNaN operand causes an arithmetic
operation to supply a QNaN result", MD00082 Vol I-A Rev 6.01 §6.3.1.5, p.82; `QNaNValid`); "When
possible, this QNaN result is one of the operand QNaN values" is not formalized (a single QNaN is not a
double). A Reset leaves memory and the input lines alone ("only the following registers have defined
state", Vol III §6.2.5, p.89: the others are registers).

* `Step i dec a a'`: some valid oracle takes `a` to `a'` in one instruction time.
* `ChoiceFree i dec a`: decidable; `false` exactly where the instruction time from `a` reaches a choice
  of the oracle whose value can change the result (`manual_step_deterministic`,
  `Refine/Determinism.lean`, is the soundness direction; the module doc there lists what is proved of
  the other direction). The choices are: `Cause.CE` of every exception other than Coprocessor Unusable
  (an interrupt included, and the Reserved Instruction of a CTI in a delay slot); a word with an UNPREDICTABLE field value (unless a
  coprocessor-unusable check comes first); and in an Operation the points listed by `ConsultsOracle`.
-/

namespace Manual

/-! ## The limits on UNPREDICTABLE and UNDEFINED outcomes -/

/-- A physical address that some User Mode address reaches (User Mode: kuseg, `ERL = 0`). -/
def UserPAddr (pa : PAddr) : Prop := ∃ va : W32, bit va 31 = false ∧ FixedMapping false va = pa

/-- The CP0 state of `x` and `y` is the same (the registers of `Arch` that MD00090 Vol III Rev 6.02
chapter 9 names, and the interrupt lines `Cause.IP7..IP2` read). -/
def CP0Same (x y : Arch) : Prop :=
  x.Status = y.Status ∧ x.Cause = y.Cause ∧ x.EPC = y.EPC ∧ x.BadVAddr = y.BadVAddr ∧
  x.ErrorEPC = y.ErrorEPC ∧ x.EBase = y.EBase ∧ x.ConfigK0 = y.ConfigK0 ∧
  x.ConfigK23 = y.ConfigK23 ∧ x.ConfigKU = y.ConfigKU ∧ x.Count = y.Count ∧
  x.Compare = y.Compare ∧ x.CauseTI = y.CauseTI ∧ x.HWREna = y.HWREna ∧ x.HW = y.HW

/-- **The state inaccessible in the mode of `a` is the same in `x` and `y`**: in User Mode the
physical memory no User Mode address reaches, and the CP0 registers while CP0 is not usable. -/
def InaccessibleSame (a x y : Arch) : Prop :=
  (UserMode a = true → ∀ pa : PAddr, ¬ UserPAddr pa → x.Mem pa = y.Mem pa) ∧
  (CP0Usable a = false → CP0Same x y)

/-- **The state accessible in the mode of `a` is the same in `x` and `y`**: everything but what
`InaccessibleSame` names (`GPR` as read: register 0 reads 0). -/
def AccessibleSame (a x y : Arch) : Prop :=
  x.PC = y.PC ∧ (∀ r, readGPR x r = readGPR y r) ∧ x.FPR = y.FPR ∧
  x.FCSR = y.FCSR ∧ x.LLbit = y.LLbit ∧ x.LLAddr = y.LLAddr ∧ x.LowPower = y.LowPower ∧
  x.BranchDelay = y.BranchDelay ∧
  (∀ pa : PAddr, (UserMode a = true → UserPAddr pa) → x.Mem pa = y.Mem pa) ∧
  (CP0Usable a = true → CP0Same x y)

/-- `b` is in the same processor mode as the User Mode state `a`, with the same access to CP0. -/
def SameMode (a b : Arch) : Prop := UserMode b = UserMode a ∧ CP0Usable b = CP0Usable a

/-- **The limits on the state an UNPREDICTABLE operation leaves** (restrictions 2 and 3 of the module
doc), and the hardware interrupt inputs `HW` unchanged.

The `HW` clause is a **model-side strengthening** of the manual's limits: MD00086 Vol II-A Rev 6.06
§1.2.1 (p.3-4) has no sentence about the interrupt inputs. `HW5..HW0` are inputs to the processor, the
"Interrupt Source" of `IP7..IP2` (MD00090 Vol III Rev 6.02 §6.1.1.1, Table 6.2, p.73), and the
`IP7..IP2` field that reads them is read-only (Vol III §9.36, p.209: "all fields in the Cause register
are read-only" but `IP1..0`, `DC`, `IV`, `WP`; Table 9.52, p.211: `IP7..IP2` "R"): no instruction
writes them, so no UNPREDICTABLE operation of an instruction may either. Without the clause a valid
oracle could change `HW` in Kernel Mode (where `InaccessibleSame` does not name the CP0 state, which
includes `HW` through `CP0Same`). The model's oracle and the witness oracles satisfy it. -/
def UnpredictableLimits (a a' : Arch) : Prop :=
  a'.LowPower = a.LowPower ∧ InaccessibleSame a a a' ∧ a'.HW = a.HW

/-- An UNPREDICTABLE outcome for state `a` is within the limits. -/
def OutcomeValid (a : Arch) : Outcome → Prop
  | .arbitrary a' => UnpredictableLimits a a'
  | _ => True

/-- An UNDEFINED outcome for state `a` does not hang the processor (MD00086 Vol II-A Rev 6.06 §1.2.2,
p.4), and leaves the hardware interrupt inputs `HW` unchanged. The `HW` clause is a **model-side
strengthening**, as in `UnpredictableLimits`: §1.2.2 says only that UNDEFINED behaviour "may cause data
loss" and "must not cause the processor to hang"; the inputs `HW5..HW0` (MD00090 Vol III Rev 6.02
Table 6.2, p.73) are not state an instruction writes (`IP7..IP2` read-only, Vol III §9.36, Table 9.52,
p.211). The model's oracle and the witness oracles satisfy it. -/
def UndefinedOutcomeValid (a : Arch) : Outcome → Prop
  | .arbitrary a' => a'.LowPower = a.LowPower ∧ a'.HW = a.HW
  | _ => True

/-- Two outcomes agree on the state accessible in the mode of `a`: the same exception, both
`proceed`, or two states equal on that state. -/
def OutcomeAgree (a : Arch) : Outcome → Outcome → Prop
  | .signal e, .signal e' => e = e'
  | .proceed, .proceed => True
  | .arbitrary x, .arbitrary y => AccessibleSame a x y
  | _, _ => False

/-- **Restriction 1 for an UNPREDICTABLE value** `F`: in User Mode it does not depend on the state
inaccessible in that mode. -/
def NIValue {β : Type} (F : Arch → β) : Prop :=
  ∀ a b, UserMode a = true → SameMode a b → AccessibleSame a a b → F a = F b

/-- **Restriction 1 for an UNPREDICTABLE operation** `F`: in User Mode its outcome, restricted to the
accessible state, does not depend on the state inaccessible in that mode. -/
def NIOutcome (F : Arch → Outcome) : Prop :=
  ∀ a b, UserMode a = true → SameMode a b → AccessibleSame a a b → OutcomeAgree a (F a) (F b)

/-- **The QNaN fields deliver a QNaN** for a QNaN operand (MD00082 Vol I-A Rev 6.01 §6.3.1.5, p.82). -/
def QNaNValid (o : Oracle) : Prop :=
  (∀ x, Mips.Fp.isQNaN32 x = true → Mips.Fp.isQNaN64 (o.cvtQNaNToD x) = true) ∧
  (∀ x, Mips.Fp.isQNaN64 x = true → Mips.Fp.isQNaN32 (o.cvtQNaNToS x) = true)

/-- **A valid oracle** (module doc): every UNPREDICTABLE outcome within the limits and
non-interfering, every UNPREDICTABLE value non-interfering, every UNDEFINED outcome not hanging the
processor, the QNaN fields giving QNaNs, and a Reset changing registers only. No UNPREDICTABLE or
UNDEFINED outcome and no Reset changes the interrupt inputs `HW` (the `HW` clauses of
`UnpredictableLimits` and `UndefinedOutcomeValid`, a model-side strengthening). -/
def Oracle.Valid (o : Oracle) : Prop :=
  -- restrictions 2 and 3 on every UNPREDICTABLE operation
  (∀ a i, OutcomeValid a (o.jalrRsIsRd a i)) ∧
  -- BEGIN R6-3
  (∀ a i, OutcomeValid a (o.linkSourceIs31 a i)) ∧
  -- END R6-3
  (∀ a r v, OutcomeValid a (o.fprOddWrite a r v)) ∧
  (∀ a fs t, OutcomeValid a (o.ctc1Unpredictable a fs t)) ∧
  (∀ a, OutcomeValid a (o.extOutOfRange a)) ∧
  (∀ a, OutcomeValid a (o.insLsbAboveMsb a)) ∧
  (∀ a w, OutcomeValid a (o.unpredictableEncoding a w)) ∧
  -- restriction 1 on every UNPREDICTABLE operation and value
  (∀ i, NIOutcome (o.jalrRsIsRd · i)) ∧
  -- BEGIN R6-3
  (∀ i, NIOutcome (o.linkSourceIs31 · i)) ∧
  -- END R6-3
  (∀ r v, NIOutcome (o.fprOddWrite · r v)) ∧
  (∀ fs t, NIOutcome (o.ctc1Unpredictable · fs t)) ∧
  NIOutcome o.extOutOfRange ∧
  NIOutcome o.insLsbAboveMsb ∧
  (∀ w, NIOutcome (o.unpredictableEncoding · w)) ∧
  (∀ r, NIValue (o.fprOddRead · r)) ∧
  (∀ fs, NIValue (o.cfc1Unpredictable · fs)) ∧
  -- the UNDEFINED operations
  (∀ a i, UndefinedOutcomeValid a (o.cp0Undefined a i)) ∧
  (∀ a v, UndefinedOutcomeValid a (o.ebaseWriteBEV0 a v)) ∧
  -- the QNaN fields
  QNaNValid o ∧
  -- Reset
  (∀ a, (o.resetUndefined a).Mem = a.Mem ∧ (o.resetUndefined a).HW = a.HW)

/-- **The manual's instruction time as a relation**: some valid resolution of the manual's choices
takes `a` to `a'`. -/
def Step (i : Impl) (dec : W32 → Option Instruction) (a a' : Arch) : Prop :=
  ∃ o : Oracle, o.Valid ∧ InstructionTime i o dec a = some a'

/-- **`n` instruction times** under one resolution of the choices (`none` only if an instruction
time is `none`, which no constructor causes since 7B). -/
def InstructionTimes (i : Impl) (o : Oracle) (dec : W32 → Option Instruction) : Nat → Arch → Option Arch
  | 0, a => some a
  | n + 1, a => (InstructionTime i o dec a).bind (InstructionTimes i o dec n)

/-! ## Choice points -/

/-- `fpr` names an odd FPR: `ValueFPR(fpr, D)` is `UNPREDICTABLE` and `StoreFPR(fpr, D, value)` is
UNPREDICTABLE with the 32-bit FPR model (MD00086 Vol II-A Rev 6.06, Figures 2.22, 2.23, p.22-23). -/
def OddFPR (fpr : W32) : Bool := bit (BitVec.ofNat 5 (reg fpr).val) 0

/-- The doubleword `ValueFPR(fpr, D)` reads for an even `fpr` (Figure 2.22, p.22). -/
def FPRPair (a : Arch) (fpr : W32) : BitVec 64 := a.FPR (reg fpr + 1) ++ a.FPR (reg fpr)

/-- `CTC1 rt, fs` with `temp = GPR[rt]` takes one of the `UNPREDICTABLE` arms of its Operation
(MD00086 Vol II-A Rev 6.06, CTC1, p.150). -/
def CTC1Unpredictable (fs temp : W32) : Bool :=
  if fs == 25#32 then bits temp 31 8 != 0#24
  else if fs == 26#32 then bits temp 31 18 != 0#14 || bits temp 11 7 != 0#5 || bits temp 2 0 != 0#3
  else if fs == 28#32 then bits temp 31 12 != 0#20 || bits temp 6 3 != 0#4
  else if fs == 31#32 then bits temp 22 18 != 0#5
  else true

/-- **The Operation of `ins`, run from `a`, reaches an oracle choice whose value can change the
result** (exact, provided the Operation does not signal before reaching it; an Operation that signals
is not choice-free anyway, `ChoiceFree`). One row per Operation that reads the oracle:

* the loads (`Oracle.loadClearsLL`) and stores (`storeClearsLL`), while `LLbit = 1`: the choice is
  whether `LLbit` becomes 0. Not `LL` and `SC`, which set `LLbit` themselves afterwards;
* an odd FPR read or written as a double (`fprOddRead`, `fprOddWrite`), on the path the Operation
  takes;
* `CFC1` of a register that does not exist (`cfc1Unpredictable`), unless `rt = 0` (the value is
  written to `GPR[0]`, which has no effect); `CTC1` in an `UNPREDICTABLE` arm;
* `MFC0`/`MTC0` of a register CP0 does not contain (`cp0Undefined`); `MTC0` of a different Exception
  Base to `EBase` while `BEV = 0` (`ebaseWriteBEV0`);
* `EXT`/`INS` with an UNPREDICTABLE field combination; `JALR`/`JALR.HB` with `rs = rd`;
* the Release 6 compact branch-and-link (`BLEZALC`, ..., `BNEZALC`) with `rt = 31`
  (`linkSourceIs31`);
* `ABS.fmt`/`NEG.fmt` of a quiet NaN (`absNegNaN`); `CVT.D.S`/`CVT.S.D` of a quiet NaN
  (`cvtQNaNToD`, `cvtQNaNToS`).

`MFHC1` with `rt = 0` is not a row: the odd-register value is written to `GPR[0]`, which has no effect
(wave 9). (Release 6 removed the instructions of the former rows `DIV`/`DIVU`/`MUL` (HI/LO), the
delay-slot branch-and-link with `rs = 31`, `NMADD`/`NMSUB`, `MADD.D`/`MSUB.D`, `C.cond.D`, `MOVF.D`/`MOVT.D`/
`MOVN.D`/`MOVZ.D` and the indexed FP loads and stores.)
-- W5: the odd-FPR rows go with the 64-bit FPU (`Status.FR = 1`). -/
def ConsultsOracle : Instruction → Arch → Bool
  | .lb .., a | .lbu .., a | .lh .., a | .lhu .., a | .lw .., a
  | .lwc1 .., a | .sb .., a | .sh .., a | .sw .., a | .swc1 .., a => a.LLbit
  | .ldc1 _ ft _, a | .sdc1 _ ft _, a => a.LLbit || OddFPR ft
  | .cfc1 rt fs, _ =>
    !(fs == 0#32 || fs == 25#32 || fs == 26#32 || fs == 28#32 || fs == 31#32) && reg rt != 0
  | .ctc1 rt fs, a => CTC1Unpredictable fs (low (readGPR a (reg rt)) 32)
  | .mfc0 _ rd sel, _ => !IsCoprocessorRegisterImplemented rd.toNat sel.toNat
  | .mtc0 rt rd sel, a =>
    !IsCoprocessorRegisterImplemented rd.toNat sel.toNat ||
      (rd.toNat == 15 && sel.toNat == 1 && !StatusBEV a &&
        bits (readGPR a (reg rt)) 29 12 != bits a.EBase 29 12)
  | .ext _ _ pos size, _ => decide ((low pos 5).toNat + (low (size - 1#32) 5).toNat > 31)
  | .ins _ _ pos size, _ => decide (((low pos 5).toNat : Int) > ((low (pos + size - 1#32) 5).toNat : Int))
  | .jalr rs rd, _ | .jalrHb rs rd, _ => reg rs == reg rd
  -- BEGIN R6-3
  | .blezalc rt _, _ | .bgezalc rt _, _ | .bgtzalc rt _, _ | .bltzalc rt _, _ | .beqzalc rt _, _
  | .bnezalc rt _, _ => reg rt == 31
  -- END R6-3
  | .absS _ fs, a | .negS _ fs, a => Mips.Fp.isQNaN32 (a.FPR (reg fs))
  | .absD fd fs, a | .negD fd fs, a =>
    OddFPR fs || OddFPR fd || Mips.Fp.isQNaN64 (FPRPair a fs)
  | .addD fd fs ft, _ | .subD fd fs ft, _ | .mulD fd fs ft, _ | .divD fd fs ft, _ =>
    OddFPR fs || OddFPR ft || OddFPR fd
  | .sqrtD fd fs, _ | .recipD fd fs, _ | .rsqrtD fd fs, _ | .movD fd fs, _ => OddFPR fs || OddFPR fd
  | .roundWD _ fs, _ | .truncWD _ fs, _ | .ceilWD _ fs, _ | .floorWD _ fs, _ | .cvtWD _ fs, _ =>
    OddFPR fs
  | .cvtDS fd fs, a => OddFPR fd || Mips.Fp.isQNaN32 (a.FPR (reg fs))
  | .cvtDW fd _, _ => OddFPR fd
  | .cvtSD _ fs, a => OddFPR fs || Mips.Fp.isQNaN64 (FPRPair a fs)
  | .mfhc1 rt fs, _ => OddFPR fs && reg rt != 0
  | .mthc1 _ fs, _ => OddFPR fs
  | _, _ => false

/-- A context that differs from another in the oracle only. -/
def ctxOf (i : Impl) (o : Oracle) : Ctx := { impl := i, oracle := o }

/-- **No oracle choice that can change the result is made in the instruction time from `a`**
(decidable; module doc). `false` when an interrupt or an exception other than Coprocessor Unusable is
taken (its `Cause.CE` "is loaded, but not defined", Vol III §6.2.3, p.87), for a word with an
UNPREDICTABLE field value whose coprocessor is usable, for a CTI in a delay slot (Reserved Instruction,
whose `Cause.CE` is not defined), and when the
Operation reaches a choice (`ConsultsOracle`). Whether the Operation signals is computed with the model's
oracle `modelOracle`; when `ConsultsOracle` is `false` every oracle gives the same run. -/
def ChoiceFree (i : Impl) (dec : W32 → Option Instruction) (a : Arch) : Bool :=
  if InterruptTaken i a then false
  else if a.LowPower then true
  else
    match InstructionFetch.run (ctxOf i modelOracle) { arch := a } with
    | (.signal _, _) => false
    | (.ok w, _) =>
      match dec w with
      | none =>
        if UnpredictableEncoding w then
          (InCop1Space w && !StatusCU1 a) || (InCop0Space w && !CP0Usable a)
        else
          match Undecodable w a with
          | .CoprocessorUnusable _ => true
          | _ => false
      | some ins =>
        !(IsCTI ins && a.BranchDelay.isSome) &&
          (if InCop1Space w && !StatusCU1 a then true
           else if InCop0Space w && !CP0Usable a then true
           else
             !ConsultsOracle ins a &&
               match Operation ins with
               | none => true
               | some op =>
                 match op.run (ctxOf i modelOracle) { arch := a } with
                 | (.ok (), _) => true
                 | (.signal (.CoprocessorUnusable _), _) => true
                 | (.signal _, _) => false)

end Manual
