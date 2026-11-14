import Semantics.Manual.Cycle

/-!
# Manual.Relation — the manual's relation, the limits on its choices, and its choice points (7D)

`InstructionTime impl oracle dec` is deterministic once an oracle is given. The manual itself allows
every outcome some *valid* oracle gives:

* `UnpredictableLimits a a'`: the restrictions on an UNPREDICTABLE operation (MD00086 Vol II-A Rev
  6.06 §1.2.1, p.3-4) that can be stated on one instruction time:
  - "UNPREDICTABLE operations must not read, write, or modify the contents of memory or internal
    state which is inaccessible in the current processor mode. For example, UNPREDICTABLE
    operations executed in user mode must not access memory or internal state that is only
    accessible in Kernel Mode": in User Mode the CP0 state and the physical memory that no User
    Mode address reaches are unchanged (`KernelState`);
  - "UNPREDICTABLE operations must not halt or hang the processor": the state does not enter the
    lower power mode (formalized only as `LowPower` unchanged; a non-terminating sequence of
    instruction times is not a property of one instruction time).
  The first restriction, "must not depend on any data source (memory or internal state) which is
  inaccessible in the current processor mode", is a property of the oracle as a function and is not
  formalized here.
* `OutcomeValid`, `Oracle.Valid`: every `Outcome` the oracle gives is a signalled exception (allowed:
  "UNPREDICTABLE operations may cause arbitrary exceptions", p.3), `proceed`, or an `arbitrary` state
  within the limits; a Reset leaves memory and the input lines alone (it is "only the following
  registers have defined state", Vol III §6.2.5, p.89: the others are registers). The value-valued
  fields (`causeCE`, `storeClearsLL`, `loadClearsLL`, `divByZero`, `divuByZero`, `mulHILO`,
  `fprOddRead`, `cfc1Unpredictable`, `absNegNaN`) may be any value. The QNaN fields (`cvtQNaNToD`,
  `cvtQNaNToS`) are constrained by their docstrings ("must be a double QNaN") and that constraint is
  not formalized.
* `Step i dec a a'`: some valid oracle takes `a` to `a'` in one instruction time.
* `ChoiceFree i dec a`: a decidable test that is `false` at every point where the instruction time
  consults the oracle (`manual_step_deterministic`, `Refine/Determinism.lean`). It is conservative:
  it is `false` for every instruction outside the list `OracleFreeOp`, even when that
  instruction's choice is not reached.
-/

namespace Manual

/-- **The state only Kernel Mode can access**: the CP0 registers and the physical memory that no
User Mode address reaches (with `ERL = 0`, kuseg `0x0000_0000`–`0x7FFF_FFFF` maps to physical
`0x4000_0000`–`0xBFFF_FFFF`, MD00090 Vol III Rev 6.02 Table A.1, p.313-314; `FixedMapping`). -/
def KernelState (a a' : Arch) : Prop :=
  a'.Status = a.Status ∧ a'.Cause = a.Cause ∧ a'.EPC = a.EPC ∧ a'.BadVAddr = a.BadVAddr ∧
  a'.ErrorEPC = a.ErrorEPC ∧ a'.EBase = a.EBase ∧ a'.ConfigK0 = a.ConfigK0 ∧
  a'.ConfigK23 = a.ConfigK23 ∧ a'.ConfigKU = a.ConfigKU ∧ a'.Count = a.Count ∧
  a'.Compare = a.Compare ∧ a'.CauseTI = a.CauseTI ∧ a'.HWREna = a.HWREna ∧ a'.HW = a.HW ∧
  ∀ pa : PAddr, (∀ va : W32, bit va 31 = false → FixedMapping false va ≠ pa) → a'.Mem pa = a.Mem pa

/-- **The limits on the state an UNPREDICTABLE operation leaves** (MD00086 Vol II-A Rev 6.06
§1.2.1, p.3-4; see the module doc for what is formalized). -/
def UnpredictableLimits (a a' : Arch) : Prop :=
  a'.LowPower = a.LowPower ∧ (UserMode a = true → KernelState a a')

/-- An oracle's outcome for state `a` is within the manual's limits. -/
def OutcomeValid (a : Arch) : Outcome → Prop
  | .arbitrary a' => UnpredictableLimits a a'
  | _ => True

/-- **A valid oracle**: every outcome it gives is within the limits, and the registers a Reset
leaves undefined are the only state its `resetUndefined` changes. -/
def Oracle.Valid (o : Oracle) : Prop :=
  (∀ a i, OutcomeValid a (o.ctiInSlot a i)) ∧
  (∀ a i, OutcomeValid a (o.cp0Undefined a i)) ∧
  (∀ a i, OutcomeValid a (o.linkSourceIs31 a i)) ∧
  (∀ a i, OutcomeValid a (o.jalrRsIsRd a i)) ∧
  (∀ a r v, OutcomeValid a (o.fprOddWrite a r v)) ∧
  (∀ a fs t, OutcomeValid a (o.ctc1Unpredictable a fs t)) ∧
  (∀ a, OutcomeValid a (o.extOutOfRange a)) ∧
  (∀ a, OutcomeValid a (o.insLsbAboveMsb a)) ∧
  (∀ a w, OutcomeValid a (o.unpredictableEncoding a w)) ∧
  (∀ a v, OutcomeValid a (o.ebaseWriteBEV0 a v)) ∧
  (∀ a, (o.resetUndefined a).Mem = a.Mem ∧ (o.resetUndefined a).HW = a.HW)

/-- **The manual's instruction time as a relation**: some valid resolution of the manual's choices
takes `a` to `a'`. -/
def Step (i : Impl) (dec : W32 → Option Instruction) (a a' : Arch) : Prop :=
  ∃ o : Oracle, o.Valid ∧ InstructionTime i o dec a = some a'

/-- **`n` instruction times** under one resolution of the choices (`none` if an untranscribed
Operation is reached). -/
def InstructionTimes (i : Impl) (o : Oracle) (dec : W32 → Option Instruction) : Nat → Arch → Option Arch
  | 0, a => some a
  | n + 1, a => (InstructionTime i o dec a).bind (InstructionTimes i o dec n)

/-! ## Choice points -/

/-- **Instructions whose Operation reads no oracle field on any path** (a sufficient list, proved in
`Refine/Determinism.lean`, `operation_oracleFree`): the integer ALU operations that cannot signal,
`J`/`JAL`, `SYNC`, `PREF`, `DI`, `EI`, `WAIT`, `RDPGPR`, `WRPGPR`. Every other instruction counts as
a possible choice point (conservative; e.g. the loads and stores read `Oracle.loadClearsLL`/
`storeClearsLL`, `DIV` the zero-divisor result, `MUL` the `HI`/`LO` values, the branch-and-link
instructions the `rs = 31` outcome). -/
def OracleFreeOp : Instruction → Bool
  | .addu .. | .subu .. | .and .. | .or .. | .xor .. | .nor .. | .sll .. | .srl .. | .sra ..
  | .sllv .. | .srlv .. | .srav .. | .rotr .. | .rotrv .. | .mult .. | .multu .. | .mfhi ..
  | .mflo .. | .mthi .. | .mtlo .. | .madd .. | .maddu .. | .msub .. | .msubu .. | .clo .. | .clz ..
  | .seb .. | .seh .. | .wsbh .. | .addiu .. | .andi .. | .ori .. | .xori .. | .lui ..
  | .j .. | .jal .. | .sync .. | .pref .. | .di .. | .ei .. | .wait .. | .rdpgpr .. | .wrpgpr .. => true
  | _ => false

/-- A context that differs from another in the oracle only. -/
def ctxOf (i : Impl) (o : Oracle) : Ctx := { impl := i, oracle := o }

/-- **No oracle choice is made in the instruction time from `a`** (decidable, conservative; see the
module doc). `false` when an exception other than Coprocessor Unusable is taken (its `Cause.CE`
"is loaded, but not defined", Vol III §6.2.3, p.87), for an `UnpredictableEncoding` word, for a CTI
in a delay slot, and for an instruction that is not `OracleFreeOp`. The Operation's outcome is
computed with the model's oracle `modelOracle`; for an `OracleFreeOp` instruction every oracle gives
the same one. -/
def ChoiceFree (i : Impl) (dec : W32 → Option Instruction) (a : Arch) : Bool :=
  if InterruptTaken i a then false
  else if a.LowPower then true
  else if a.Nullify then true
  else
    match InstructionFetch.run (ctxOf i modelOracle) { arch := a } with
    | (.signal _, _) => false
    | (.ok w, _) =>
      match dec w with
      | none =>
        !UnpredictableEncoding w &&
          (match Undecodable w a with
           | .CoprocessorUnusable _ => true
           | _ => false)
      | some ins =>
        !(IsCTI ins && a.BranchDelay.isSome) &&
          (if InCop1Space w && !StatusCU1 a then true
           else if InCop0Space w && !CP0Usable a then true
           else
             OracleFreeOp ins &&
               match Operation ins with
               | none => true
               | some op =>
                 match op.run (ctxOf i modelOracle) { arch := a } with
                 | (.ok (), _) => true
                 | (.signal (.CoprocessorUnusable _), _) => true
                 | (.signal _, _) => false)

end Manual
