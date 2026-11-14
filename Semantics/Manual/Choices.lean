import Semantics.Manual.Arch
import Semantics.Instruction

/-!
# Manual.Choices — what one implementation fixes, and what the manual leaves open

* `Impl` holds the **implementation-dependent constants and rates** that the manual leaves to the
  implementation but that are then fixed for that implementation (the rate of `Count`, `PRId`, the
  read-only parts of `Config`, `Config1`, `IntCtl`, `SRSCtl`, `CCRes`, `SYNCI_Step`, whether `WAIT`
  restarts on a request that is not enabled).
* `Oracle` has **one field for each place where the manual allows several outcomes** (UNPREDICTABLE,
  UNDEFINED, "may succeed or may fail", "loaded, but not defined"). The spec takes an oracle as an
  argument; the manual's relation `Manual.Step` quantifies over all of them (`docs/MANUAL-SPEC.md`).

`modelImpl` and `modelOracle` are the model's choices. Each field cites the SPEC-NOTES pin it
corresponds to. Nothing here names a definition of `Step.lean`/`State.lean`.
-/

namespace Manual

/-- An exception, as `SignalException` names it (MD00086 Vol II-A Rev 6.06 §2.2.2.5.1, p.26), with
the exception-dependent argument, and the extra state each one saves (MD00090 Vol III Rev 6.02
§6.2.9-§6.2.26). -/
inductive Exception where
  | Interrupt
  /-- Address Error on a load or an instruction fetch, with the failing address (§6.2.9, p.92-93). -/
  | AddressErrorLoad (badVAddr : W32)
  /-- Address Error on a store (§6.2.9, p.92-93). -/
  | AddressErrorStore (badVAddr : W32)
  | SystemCall
  | Breakpoint
  | ReservedInstruction
  /-- Coprocessor Unusable, with the unit number (§6.2.22, p.100: "CauseCE unit number of the
  coprocessor being referenced"). -/
  | CoprocessorUnusable (unit : Nat)
  | IntegerOverflow
  | Trap
  | FloatingPoint
  deriving Repr, DecidableEq

/-- What the processor does for one UNPREDICTABLE or UNDEFINED operation that the oracle resolves:
signal an exception, execute the instruction as if the condition did not hold, or produce some
other architectural state. The limits on that state (MD00086 Vol II-A Rev 6.06 §1.2, p.3-4) are
`Manual.UnpredictableLimits` (7D). -/
inductive Outcome where
  | signal (e : Exception)
  | proceed
  | arbitrary (a : Arch)

/-- The implementation's constants. -/
structure Impl where
  /-- The amount `Count` advances by in one instruction time while `Cause.DC = 0` (MD00090 Vol III
  Rev 6.02 §9.27, p.183: "The rate at which the counter increments is implementation-dependent"). -/
  CountIncrement : W32
  /-- `PRId` (15, 0; Vol III §9.40, Table 9.57, p.221), read-only. -/
  PRId : W32
  /-- The read-only part of `Config` (16, 0; Vol III §9.45, Table 9.64, p.233-235): every bit but
  the R/W fields `K23` (30..28), `KU` (27..25) and `K0` (2..0), which must be 0 here. -/
  ConfigFixed : W32
  /-- `Config1` (16, 1; Vol III §9.46, Table 9.65, p.237-240), read-only. -/
  Config1 : W32
  /-- `IntCtl` (12, 1; Vol III §9.33, Table 9.48, p.199), read-only here (`VS = 0`). -/
  IntCtl : W32
  /-- `SRSCtl` (12, 2; Vol III §9.34, Table 9.49, p.203), read-only here (`HSS = 0`). -/
  SRSCtl : W32
  /-- `RDHWR` register 3, `CCRes` (MD00086 Vol II-A Rev 6.06, RDHWR, Table 5.4, p.332). -/
  CCRes : W32
  /-- `RDHWR` register 1, `SYNCI_Step` (RDHWR, Table 5.4, p.332). -/
  SYNCIStep : W32
  /-- `WAIT` restarts the pipeline on a request that is pending and not masked out by `IM` even when
  interrupts are not enabled (MD00086 Vol II-A Rev 6.06, WAIT, p.442: "It is implementation-dependent
  whether the pipeline restarts when a non-enabled interrupt is requested"). -/
  WaitRestartsOnNotEnabled : Bool

/-- One resolution of every choice the manual leaves open, as far as the transcribed operations
need it (later sub-waves add fields as they transcribe more pages). -/
structure Oracle where
  /-- A CTI in a branch delay slot: "Processor operation is UNPREDICTABLE if a control transfer
  instruction (CTI) is placed in the delay slot of a branch or jump" (MD00086 Vol II-A Rev 6.06,
  BEQ, Restrictions, p.72). -/
  ctiInSlot : Arch → Instruction → Outcome
  /-- `MTC0`/`MFC0` of a register `(rd, sel)` that coprocessor 0 does not contain: "Pre-Release 6:
  The results are UNDEFINED if coprocessor 0 does not contain a register as specified by rd and sel"
  (MD00086 Vol II-A Rev 6.06, MTC0, Restrictions, p.290; MFC0 p.266). -/
  cp0Undefined : Arch → Instruction → Outcome
  /-- A store executed between `LL` and `SC`: "If either of the following events occurs between the
  execution of LL and SC, the SC may succeed or it may fail" (MD00086 Vol II-A Rev 6.06, SC, p.347).
  `true`: this store makes the `SC` fail (`LLbit ← 0`). -/
  storeClearsLL : Arch → Bool
  /-- `Cause.CE` for an exception other than Coprocessor Unusable: "The CE field is loaded, but not
  defined, for any exception type other than a coprocessor unusable exception" (MD00090 Vol III Rev
  6.02 §6.2.3, p.87). -/
  causeCE : Arch → Exception → BitVec 2
  /-- The registers whose state after a Reset is not defined: "On a Reset Exception, only the
  following registers have defined state" (MD00090 Vol III Rev 6.02 §6.2.5, p.89). The oracle gives
  the state before the listed assignments of the Operation are made (p.89-90). -/
  resetUndefined : Arch → Arch
  -- 7B S1 integer ALU: begin
  /-- `DIV` by a zero divisor: "If the divisor in GPR rt is zero, the arithmetic result value is
  UNPREDICTABLE" (MD00086 Vol II-A Rev 6.06, DIV, Restrictions, p.165). The `(HI, LO)` pair the
  instruction leaves; no exception ("No arithmetic exception occurs under any circumstances", p.165). -/
  divByZero : Arch → W32 × W32
  /-- `DIVU` by a zero divisor: "If the divisor in GPR rt is zero, the arithmetic result value is
  UNPREDICTABLE" (DIVU, Restrictions, p.171). The `(HI, LO)` pair the instruction leaves. -/
  divuByZero : Arch → W32 × W32
  /-- `MUL`: "The contents of HI and LO are UNPREDICTABLE after the operation" (MUL, Description and
  Operation `HI ← UNPREDICTABLE`, `LO ← UNPREDICTABLE`, p.299). The `(HI, LO)` pair left. -/
  mulHILO : Arch → W32 × W32
  /-- `EXT` with `lsb + msbd > 31`: "The operation is UNPREDICTABLE if lsb+msbd > 31" (EXT,
  Restrictions and Operation, p.183). `.proceed`: compute the Operation's formula anyway. -/
  extOutOfRange : Arch → Outcome
  /-- `INS` with `lsb > msb`: "The operation is UNPREDICTABLE if lsb > msb" (INS, Restrictions,
  p.193). `.proceed`: compute the Operation's formula anyway. -/
  insLsbAboveMsb : Arch → Outcome
  -- 7B S1 integer ALU: end

/-- Whether an instruction is `PAUSE`, whose format diagram is SPECIAL, `0`, `0`, `0`, `5`, SLL
(MD00086 Vol II-A Rev 6.06, PAUSE, p.317): the encoding of `SLL r0, r0, 5`. -/
def IsPAUSE : Instruction → Bool
  | .sll rd rt shamt => rd == 0#32 && rt == 0#32 && shamt == 5#32
  | _ => false

/-- **The model's implementation constants** (SPEC-NOTES §9, the pins listed there): `Count` + 1 per
instruction time (`timerTick` pin); `PRId = 0x0001_0000`; `Config` read-only part `0x8000_8580`
(`M = 1`, `BE = 1`, `AT = 0`, `AR = 1`, `MT = 3`); `Config1 = 0x0000_0001` (`FP = 1`); `IntCtl`
with `IPTI = 7` (`0xE000_0000`), `SRSCtl = 0`; `CCRes = 1`; `SYNCI_Step = 0`; `WAIT` restarts on any
pending request not masked by `IM`. -/
def modelImpl : Impl where
  CountIncrement := 1#32
  PRId := 0x00010000#32
  ConfigFixed := 0x80008580#32
  Config1 := 0x00000001#32
  IntCtl := 0xE0000000#32
  SRSCtl := 0#32
  CCRes := 1#32
  SYNCIStep := 0#32
  WaitRestartsOnNotEnabled := true

/-- **The model's choices** (SPEC-NOTES §9): a CTI in a delay slot signals Reserved Instruction,
except `PAUSE`, which the model executes as the `SLL` it is encoded as (item 1); an `MTC0`/`MFC0` of
a register coprocessor 0 does not contain signals Reserved Instruction; every store clears `LLbit`
(the `LLbit` pin); `Cause.CE` is loaded with 0 for every exception other than Coprocessor Unusable;
a Reset keeps every register whose reset state is undefined, except `Config.K23 = Config.KU = 2` and
`LLbit = 0` (SPEC-NOTES, Reset pins). -/
def modelOracle : Oracle where
  ctiInSlot := fun _ i => if IsPAUSE i then .proceed else .signal .ReservedInstruction
  cp0Undefined := fun _ _ => .signal .ReservedInstruction
  storeClearsLL := fun _ => true
  causeCE := fun _ _ => 0#2
  resetUndefined := fun a => { a with ConfigK23 := 2#3, ConfigKU := 2#3, LLbit := false }
  -- 7B S1 integer ALU: begin (SPEC-NOTES §11 rows)
  divByZero := fun a => (a.HI, a.LO)
  divuByZero := fun a => (a.HI, a.LO)
  mulHILO := fun a => (a.HI, a.LO)
  extOutOfRange := fun _ => .proceed
  insLsbAboveMsb := fun _ => .proceed
  -- 7B S1 integer ALU: end

end Manual
