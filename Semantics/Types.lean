import Std.Data.HashMap.Basic
import Semantics.Word

/-!
# Types — core simulator datatypes

Foundation module (DESIGN.md §3): `Program`, `State`, `HaltReason`, `StepResult`,
instruction-word constructors, and environment constants. Depends only on `Word`.
-/

/-- A program is a sparse map from program-counter words to raw instruction words. -/
abbrev Program := Std.HashMap W32 W32

/-- The full machine state of the simulator between steps. -/
structure State where
  /-- Program counter. -/
  pc : W32
  /-- General-purpose registers, size 32; index = register number. -/
  regs : Array W32
  /-- `hi` register (mult/div results). -/
  hi : W32
  /-- `lo` register (mult/div results). -/
  lo : W32
  /-- Coprocessor-1 (FPU) registers `$f0`..`$f31`, size 32; index = FP
  register number. Each holds a raw 32-bit pattern (same raw-bit-pattern
  storage convention as `regs`): an IEEE-754 single, or one half of a double.
  Double-precision values occupy an even/odd register pair (`$fN` = low word,
  `$f(N+1)` = high word; the 32-bit FPU register model, `Status.FR = 0`:
  MD00082 Vol I-A Rev 6.01 §6.4.1, p.84). All arithmetic is done on these bit
  patterns by `Semantics/FpOps.lean`; no host float is involved. -/
  fpRegs : Array W32
  /-- The Floating Point Control and Status Register (FCSR, CP1 control
  register 31; MD00082 Vol I-A Rev 6.01 §6.5.4, Figure 6.14 / Table 6.8,
  p.92-95), as a raw word with the layout and accessors of `Mips.Fp`
  (`Semantics/FpOps.lean` §9): the eight condition codes `FCC7..1` (bits
  31..25) and `FCC0` (bit 23), `FS` (24), `Cause` (17..12, `E V Z O U I`),
  `Enables` (11..7), `Flags` (6..2), `RM` (1..0). Bits 22..18 (`Impl`, the
  reserved bit 20, and `ABS2008`/`NAN2008`, which do not exist because
  `FIR.Has2008 = 0`) read as zero and ignore writes. `FCCR`/`FEXR`/`FENR` are
  views of this one register (`cfc1`/`ctc1`). -/
  fcsr : W32
  /-- Byte-addressable, sparse memory. -/
  mem : Std.HashMap W32 UInt8
  /-- Accumulated syscall output. -/
  out : String
  /-- The delay-slot marker. `some t` means **the instruction at `pc` is in a
  branch delay slot**, and control goes to `t` once it has executed; `none`
  means it is not in a delay slot.

  Every branch/jump sets this and leaves `pc` at the delay-slot instruction
  (`pc + 4`): a **taken** branch/jump records its real target, a **not-taken**
  conditional branch records the fall-through address `pc + 8`. The next
  step then (a) executes the delay-slot instruction and commits `t` to `pc`
  (`Step.lean`'s `advance`), or (b) if that instruction raises an exception,
  abandons `t` and records `EPC = pc - 4`, `Cause.BD = 1`
  (`exceptionEntry`), or (c) if that instruction is itself a branch, jump
  or `eret`, halts with `HaltReason.branchInDelaySlot`.

  Representing "not taken" as a pending fall-through target (rather than a
  separate Boolean) keeps one field for one fact: `pendingBranch.isSome` *is*
  "in a delay slot", for taken and not-taken branches alike.

  The branch-likely family does not use this when not taken: its delay-slot
  instruction is nullified, so the branch-likely's own step moves `pc`
  straight to `pc + 8` and leaves this `none`. -/
  pendingBranch : Option W32 := none
  /-- The link bit (`LLbit`) set by `ll` and tested/cleared by `sc` (MD00086
  Rev 6.06, "LL"/"SC"). Cleared by `sc` (success or failure), by `eret`,
  and by every exception entry ("Exceptions between the LL and SC cause SC
  to fail"). Pinned model choice: every store-class
  instruction (`sb`, `sh`, `sw`, `swl`, `swr`, `swc1`, `sdc1`) also clears
  it. MD00086 "SC": when a memory access instruction (load, store or
  prefetch) executes on the same processor between `ll` and `sc`, "the SC
  may succeed or it may fail; the success or failure is not predictable".
  Failing the `sc` after an intervening store is therefore one legal
  outcome, chosen here; it is not architecturally mandated. (After an
  intervening *load* the model lets the `sc` succeed — equally legal.)
  Defaults `false`. -/
  llBit : Bool := false
  /-- Coprocessor 0 `Status` (register 12, sel 0). The model gives meaning to
  exactly these bits, and `mtc0` can write only these (`statusWriteMask`);
  all others read as zero:

  * `IE` (bit 0), `IM7..IM0` (bits 15..8) — stored and read back only; no
    interrupt is ever raised by this model.
  * `EXL` (bit 1) — set by every exception, cleared by `eret`.
  * `ERL` (bit 2) — selects `ErrorEPC` in `eret`; never set by the model
    itself (no Reset/NMI/Cache-Error exception), only by `mtc0`.
  * `BEV` (bit 22) — selects the bootstrap exception vector.
  * `CU1` (bit 29) — coprocessor 1 usable. When it is 0 every COP1/COP1X
    instruction, `lwc1`/`swc1`/`ldc1`/`sdc1` and `movf`/`movt` raises
    Coprocessor Unusable (MD00090 Vol III Rev 6.02 §6.2.22, p.100).

  **Not modeled:** `UM`/`KSU` (no user/kernel mode distinction — every
  instruction, including `mfc0`/`mtc0`/`eret`, executes as if in kernel
  mode, so Coprocessor Unusable is never raised for CP0), `CU0`, `RP`, `FR`,
  `RE`, `MX`, `PX`, `TS`, `SR`, `NMI`. -/
  cp0Status : W32
  /-- Coprocessor 0 `Cause` (register 13, sel 0). Exception entry writes
  `ExcCode` (bits 6..2), `CE` (bits 29..28: the coprocessor unit number for
  Coprocessor Unusable; "loaded, but not defined" for every other exception —
  MD00090 Vol III Rev 6.02 §6.2.3, p.87 — pinned to 0) and, when `Status.EXL`
  was 0, `BD` (bit 31); it leaves every other bit alone. `mtc0` can write
  only `DC` (27), `IV` (23) and `IP1..IP0` (9..8) (`causeWriteMask`). `WP`,
  `IP7..IP2`, `TI`, `PCI` are never set. -/
  cp0Cause : W32
  /-- Coprocessor 0 `EPC` (register 14, sel 0): the restart address recorded
  by exception entry when `Status.EXL` was 0 — the faulting instruction's
  address, or the preceding branch's address if it was in a delay slot.
  Read by `eret`; readable and writable with `mfc0`/`mtc0`. -/
  cp0Epc : W32
  /-- Coprocessor 0 `BadVAddr` (register 8, sel 0): the failing virtual
  address of the most recent Address Error exception (AdEL/AdES).
  Read-only to software (`mtc0` to it is ignored). -/
  cp0BadVAddr : W32 := 0#32
  /-- Coprocessor 0 `ErrorEPC` (register 30, sel 0): `eret`'s return address
  when `Status.ERL = 1`. Only ever written by `mtc0` (the model raises no
  error-level exception). -/
  cp0ErrorEpc : W32 := 0#32
  /-- The aligned effective address of the most recent `ll` (the address the
  RMW sequence monitors). `sc` fails unless its own address equals it:
  "an SC must always compare its address against that of the LL. An SC will
  fail if the aligned address of the SC does not match that of the preceding
  LL" (MD00086 Vol II-A Rev 6.06, SC, p.347). Meaningful only while `llBit`
  is set. Defaults `0`. -/
  llAddr : W32 := 0#32
  /-- Coprocessor 0 `EBase` (register 15, sel 1; MD00090 Vol III Rev 6.02
  §9.41, Figure 9.42 / Table 9.58, p.223-224), without the optional write
  gate: bits 31..30 read `10`, the Exception Base field (bits 29..12) is
  read/write, bits 11..10 and `CPUNum` (9..0) read zero. It supplies the
  exception vector base when `Status.BEV = 0`. Reset value `0x8000_0000`. -/
  cp0EBase : W32 := 0x80000000#32

/-- Reasons the simulator halts instead of producing a next state.

Architectural exceptions (Reserved Instruction, Address Error, Integer
Overflow, Syscall, Breakpoint, Trap) are **not** halts: they are ordinary
state transitions to the exception vector (`Step.lean`'s `exceptionEntry`).
The halts below are model-level conventions for where the modeled machine
stops. -/
inductive HaltReason where
  /-- Clean exit via the environment-call convention's service 10
  (`syscall` with `$v0 = 10`). -/
  | exit
  /-- An exception was taken and there is no handler: the fetch at the
  exception vector found no instruction in the `Program` while
  `Status.EXL = 1`. Carries the `Cause.ExcCode`, the `EPC` and the
  `BadVAddr` register values at that point (`badVAddr` is meaningful only
  for address errors, `code` 4 or 5). This is a model-level convention that
  keeps the reason for an unhandled exception visible instead of reporting
  a bare fetch failure at the vector address. -/
  | unhandledException (code epc badVAddr : W32)
  /-- The word-aligned `pc` holds no instruction in the `Program` (control
  ran outside the program text) and the machine is not at the exception
  vector with `EXL = 1`. A model boundary, not an architectural exception:
  real memory always holds *some* word. -/
  | noInstruction (pc : W32)
  /-- A branch, jump or `eret` was fetched in a branch delay slot
  (`State.pendingBranch = some _`). The architecture makes this
  UNPREDICTABLE; `step` halts with this reason so the condition stays
  diagnosable (SPEC-NOTES §9 item 1; INSTRUCTION-REF Global rule 3). -/
  | branchInDelaySlot
  deriving Repr, DecidableEq

/-- Result of a single simulation step: either a new state, or a halt. -/
inductive StepResult where
  | next (s : State)
  | halt (r : HaltReason)

/-- Mask `w` to `n` bits and shift it left by `shift`. Internal helper for the
instruction-word constructors below. -/
def field (n shift : Nat) (w : W32) : W32 :=
  (maskLow n w) <<< shift

/-- Build an R-format instruction word from its fields.
Layout: `rs` bits 25..21, `rt` bits 20..16, `rd` bits 15..11, `shamt` bits 10..6,
`funct` bits 5..0 (opcode field is implicitly 0, as for all R-type instructions). -/
def mkRT (rs rt rd shamt funct : W32) : W32 :=
  field 5 21 rs ||| field 5 16 rt ||| field 5 11 rd ||| field 5 6 shamt ||| field 6 0 funct

/-- Build an I-format instruction word from its fields.
Layout: `opcode` bits 31..26, `rs` bits 25..21, `rt` bits 20..16, `imm` bits 15..0. -/
def mkIT (opcode rs rt imm : W32) : W32 :=
  field 6 26 opcode ||| field 5 21 rs ||| field 5 16 rt ||| field 16 0 imm

/-- Build a J-format instruction word's target field.
Layout: `target` in bits 25..0 (opcode is left as 0; callers combine as needed). -/
def mkJT (target : W32) : W32 :=
  field 26 0 target

/-- Base address of the `.text` segment (MARS default configuration). -/
def textBase : W32 := 0x00400000

/-- Initial value of `$sp` (MARS default configuration). -/
def spInit : W32 := 0x7fffeffc

/-- General exception vector when `Status.BEV = 0` and `EBase` holds its
reset value (MD00090 Vol III Rev 6.02 §6.2.2 "Exception Vector Locations":
base `0x8000_0000`, offset `0x180`). -/
def exceptionVectorAddr : W32 := 0x80000180

/-- Offset of the general exception vector from the vector base. -/
def exceptionVectorOffset : W32 := 0x180

/-- The read/write Exception Base field of `EBase`, bits 29..12. -/
def ebaseWriteMask : W32 := 0x3ffff000

/-- The fixed bits 31..30 = `10` of `EBase`. -/
def ebaseFixedBits : W32 := 0x80000000

/-- General exception vector when `Status.BEV = 1` (bootstrap vectors: base
`0xBFC0_0200`, offset `0x180`). -/
def exceptionVectorBevAddr : W32 := 0xBFC00380

/-- `Cause.ExcCode` values (MD00090 Table "Cause Register ExcCode field"). -/
def excCodeAdEL : W32 := 4
/-- Address error, store. -/
def excCodeAdES : W32 := 5
/-- Syscall. -/
def excCodeSys : W32 := 8
/-- Breakpoint (`break`). -/
def excCodeBp : W32 := 9
/-- Reserved Instruction. -/
def excCodeRI : W32 := 10
/-- Coprocessor Unusable: a coprocessor-1 instruction with `Status.CU1 = 0`
(user mode is not modeled, so coprocessor 0 is always usable). -/
def excCodeCpU : W32 := 11
/-- Integer Overflow (`add`/`addi`/`sub`). -/
def excCodeOv : W32 := 12
/-- Trap (`teq`/`tne`/`tlt`/`tge`/`tltu`/`tgeu` and their immediate forms).
All share this one code; `Cause` does not say which condition fired. -/
def excCodeTr : W32 := 13
/-- Floating Point exception (MD00090 Vol III Rev 6.02 §6.2.23, p.100;
Table 9.53 `FPE`): an enabled IEEE exception, or FCSR `Cause.E`. -/
def excCodeFPE : W32 := 15

/-- `Status.IE` (bit 0). -/
def statusIeMask : W32 := 0x1
/-- `Status.EXL` (bit 1): set on exception entry, cleared by `eret`. -/
def statusExlMask : W32 := 0x2
/-- `Status.ERL` (bit 2). -/
def statusErlMask : W32 := 0x4
/-- `Status.IM7..IM0` (bits 15..8). -/
def statusImMask : W32 := 0xff00
/-- `Status.BEV` (bit 22). -/
def statusBevMask : W32 := 0x00400000
/-- `Status.CU1` (bit 29). -/
def statusCu1Mask : W32 := 0x20000000
/-- The `Status` bits `mtc0` can write: `IE`, `EXL`, `ERL`, `IM7..IM0`,
`BEV`, `CU1`. Every other bit reads as zero. -/
def statusWriteMask : W32 := 0x2040ff07

/-- `Cause.BD` (bit 31): the exception was taken in a branch delay slot. -/
def causeBdMask : W32 := 0x80000000
/-- `Cause.ExcCode` (bits 6..2). -/
def causeExcCodeMask : W32 := 0x7c
/-- `Cause.CE` (bits 29..28): coprocessor unit number of a Coprocessor
Unusable exception. -/
def causeCeMask : W32 := 0x30000000
/-- The `Cause` bits `mtc0` can write: `DC` (27), `IV` (23) and `IP1..IP0`
(9..8). MD00090 Vol III Rev 6.02 §9.36 (p.209): "With the exception of the
IP1..0, DC, IV, and WP fields, all fields in the Cause register are
read-only"; Table 9.52 (p.210) makes `DC` R/W and Required in Release 2. `DC`
("Disable Count register") is stored and read back but has no effect: the
model has no `Count` register. `WP` (22) is not writable here: it is
"Required if watch registers are implemented", and the model has none
(`Config1.WR = 0`). -/
def causeWriteMask : W32 := 0x08800300

-- ## Tests

-- `mkRT`: rs=5, rt=6, rd=7, shamt=3, funct=0x20 (add)
-- 000000 00101 00110 00111 00011 100000
example :
    mkRT (5#32) (6#32) (7#32) (3#32) (0x20#32)
      = 0b00000000101001100011100011100000#32 := by decide
#guard mkRT (5#32) (6#32) (7#32) (3#32) (0x20#32)
    = 0b00000000101001100011100011100000#32

-- masking: out-of-range field bits are discarded
example : mkRT (0xff#32) (0#32) (0#32) (0#32) (0#32) = field 5 21 (0xff#32) := by decide

-- `mkIT`: opcode=0x23 (lw), rs=29 ($sp), rt=8 ($t0), imm=0x1234
example :
    mkIT (0x23#32) (29#32) (8#32) (0x1234#32)
      = 0b100011_11101_01000_0001001000110100#32 := by decide
#guard mkIT (0x23#32) (29#32) (8#32) (0x1234#32)
    = 0b100011_11101_01000_0001001000110100#32

-- `mkJT`: target = 0x3ffffff (all 26 bits set)
example : mkJT (0x3ffffff#32) = 0x3ffffff#32 := by decide
#guard mkJT (0xffffffff#32) = 0x3ffffff#32

-- `State` construction and field read-back
def sampleState : State :=
  { pc := textBase
    regs := (Array.replicate 32 (0#32)).set! 29 spInit
    hi := 0#32
    lo := 0#32
    fpRegs := Array.replicate 32 (0#32)
    fcsr := 0#32
    mem := ∅
    out := ""
    cp0Status := 0#32
    cp0Cause := 0#32
    cp0Epc := 0#32 }

example : sampleState.pc = textBase := by decide
example : sampleState.regs.size = 32 := by decide
example : sampleState.regs[29]! = spInit := by decide
example : sampleState.fpRegs.size = 32 := by decide
example : sampleState.fpRegs[0]! = 0#32 := by decide
example : sampleState.fcsr = 0#32 := by decide
example : sampleState.out = "" := by decide
#guard sampleState.pc = textBase
#guard sampleState.regs.size = 32
#guard sampleState.regs[29]! = spInit
#guard sampleState.fpRegs.size = 32
#guard sampleState.fcsr = 0#32

-- `HaltReason` / `StepResult` sanity
example : HaltReason.exit ≠ HaltReason.branchInDelaySlot := by decide
example : HaltReason.unhandledException 12#32 0#32 0#32 ≠ HaltReason.noInstruction 0#32 := by decide
example : (StepResult.halt HaltReason.exit) = (StepResult.halt HaltReason.exit) := by rfl

-- `State.pendingBranch` defaults to `none` when omitted from a literal
example : sampleState.pendingBranch = none := by decide
#guard sampleState.pendingBranch = none
-- `State.llBit` defaults to `false` when omitted from a literal
example : sampleState.llBit = false := by decide
#guard sampleState.llBit = false
-- the two CP0 registers with defaults
example : sampleState.cp0BadVAddr = 0#32 := by decide
example : sampleState.cp0ErrorEpc = 0#32 := by decide
example : sampleState.llAddr = 0#32 := by decide
example : sampleState.cp0EBase = 0x80000000#32 := by decide
example : excCodeFPE = 15#32 := by decide
example : causeCeMask = 3#32 <<< 28 := by decide
example : ebaseFixedBits ||| exceptionVectorOffset = exceptionVectorAddr := by decide
-- CP0 fields: `sampleState` reads back the zero-initialized fields; the
-- exception constants are distinct small values as documented.
example : sampleState.cp0Status = 0#32 := by decide
example : sampleState.cp0Cause = 0#32 := by decide
example : sampleState.cp0Epc = 0#32 := by decide
#guard sampleState.cp0Status = 0#32
example : exceptionVectorAddr = 0x80000180#32 := by decide
example : excCodeBp ≠ excCodeTr := by decide
example : excCodeBp = 9#32 := by decide
example : excCodeTr = 13#32 := by decide
example : statusExlMask = 2#32 := by decide
example : exceptionVectorBevAddr = 0xbfc00380#32 := by decide
example : statusWriteMask = statusIeMask ||| statusExlMask ||| statusErlMask ||| statusImMask
    ||| statusBevMask ||| statusCu1Mask := by decide
example : causeWriteMask = (1#32 <<< 27) ||| (1#32 <<< 23) ||| (3#32 <<< 8) := by decide
example : causeExcCodeMask = 0x1f#32 <<< 2 := by decide
