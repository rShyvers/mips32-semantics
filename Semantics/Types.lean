import Std.Data.HashMap.Basic
import Semantics.Word

/-!
# Types — core simulator datatypes

Foundation module (DESIGN.md §3): `Program` (assembler output), `State` (the processor),
instruction-word constructors, and constants. Depends only on `Word`.
-/

/-- A **virtual address**: what a program computes (`pc`, effective addresses, the addresses the
assembler uses). The Fixed Mapping MMU (`State.lean`, `translate`) turns it into a physical address
(MD00090 Vol III Rev 6.02, Appendix A.1, p.313-314). Only a name for `W32`, for readability. -/
abbrev VAddr := W32

/-- A **physical address**: an index into `State.physMem`. Only a name for `W32`. -/
abbrev PAddr := W32

/-- An assembled program image: a sparse map from word-aligned **virtual** addresses to 32-bit
words (text, data, `.ktext`, `.kdata`). This is **not** processor state: it is what the assembler
(`Asm.lean`) produces and what the loader (`Semantics/Env.lean`, `load`) writes into
`State.physMem`, each word at the physical address its virtual address translates to
(`Env.loadAddr`), before execution starts. The processor fetches instructions from
`State.physMem` only. -/
abbrev Program := Std.HashMap VAddr W32

/-- The architectural state of the modeled processor between instructions. It is
self-contained: instructions are fetched from `physMem` (`Step.lean`, `step`), so a store to the
instruction stream changes what is executed (MD00086 Vol II-A Rev 6.06, SYNCI, p.412). Anything
that belongs to the environment rather than to the processor (the loaded image, the output of the
hosted services, halting) lives in `Semantics/Env.lean`. -/
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
  /-- **Physical memory**: byte-addressable and sparse, keyed by the **physical** address. Every
  processor access (instruction fetch, loads, stores) reaches it through the Fixed Mapping MMU
  (`State.lean`, `translate`), so one physical byte can have several virtual names (kseg0 and
  kseg1 both map onto the low 512 MB). The whole 2^32-byte physical space exists: a byte that was
  never written reads as `0` and no access ends in a Bus Error — a pin of what the model's memory
  system does, which the architecture leaves to the system (MD00090 Vol III Rev 6.02 §6.2.16,
  p.97). -/
  physMem : Std.HashMap PAddr UInt8
  /-- The delay-slot marker. `some t` means **the instruction at `pc` is in a
  branch delay slot**, and control goes to `t` once it has executed; `none`
  means it is not in a delay slot.

  Every branch/jump sets this and leaves `pc` at the delay-slot instruction
  (`pc + 4`): a **taken** branch/jump records its real target, a **not-taken**
  conditional branch records the fall-through address `pc + 8`. The next
  step then (a) executes the delay-slot instruction and commits `t` to `pc`
  (`Step.lean`'s `advance`), or (b) if that instruction raises an exception,
  abandons `t` and records `EPC = pc - 4`, `Cause.BD = 1`
  (`exceptionEntry`), or (c) if that instruction is itself a control
  transfer (`Step.lean`'s `isBranchLike`), raises Reserved Instruction
  (UNPREDICTABLE / UNDEFINED in the architecture; the pin is in `execInstr`).

  Representing "not taken" as a pending fall-through target (rather than a
  separate Boolean) keeps one field for one fact: `pendingBranch.isSome` *is*
  "in a delay slot", for taken and not-taken branches alike.

  A **not-taken branch-likely** also sets this to `some (pc + 8)` (its delay-slot
  instruction is in a delay slot, `Cause.BD` rules apply) and additionally sets
  `nullified` (below): the delay-slot instruction is then nullified in its own
  instruction time. -/
  pendingBranch : Option W32 := none
  /-- The link bit (`LLbit`) set by `ll` and tested/cleared by `sc` (MD00086
  Rev 6.06, "LL"/"SC"). Cleared by `sc` (success or failure), by `eret`,
  and by every exception entry ("Exceptions between the LL and SC cause SC
  to fail"). Pinned model choice: every store-class
  instruction (`sb`, `sh`, `sw`, `swl`, `swr`, `swc1`, `sdc1`, `swxc1`, `sdxc1`) also clears
  it. MD00086 "SC": when a memory access instruction (load, store or
  prefetch) executes on the same processor between `ll` and `sc`, "the SC
  may succeed or it may fail; the success or failure is not predictable".
  Failing the `sc` after an intervening store is therefore one legal
  outcome, chosen here; it is not architecturally mandated. (After an
  intervening *load* the model lets the `sc` succeed — equally legal.)
  Defaults `false`. -/
  llBit : Bool := false
  /-- Coprocessor 0 `Status` (register 12, sel 0; MD00090 Vol III Rev 6.02 §9.32,
  Table 9.47, p.189-196). The model gives meaning to exactly these bits, and
  `mtc0` can write only these (`statusWriteMask`); all others read as zero:

  * `IE` (bit 0), `IM7..IM0` (bits 15..8) — interrupt enable and the per-request
    masks: an interrupt is taken when `IE = 1`, `EXL = ERL = 0` and some
    `Cause.IPi` with `IMi = 1` is set (`interruptTaken`, `Step.lean`).
  * `EXL` (bit 1) — set by every exception, cleared by `eret`.
  * `ERL` (bit 2) — set by the Reset exception (`resetException`, `Step.lean`);
    selects `ErrorEPC` in `eret`.
  * `UM` (bit 4) — the base operating mode: 0 Kernel, 1 User (Supervisor Mode
    is not implemented, so bit 3 (`R0`) reads 0 and `KSU` = `UM ‖ 0`). The
    processor is in User Mode iff `UM = 1`, `EXL = 0` and `ERL = 0`
    (`userMode`, `Step.lean`; Vol III §3.2-3.4, p.21-22).
  * `BEV` (bit 22) — selects the bootstrap exception vector; set by Reset.
  * `CU0` (bit 28) — coprocessor 0 usable outside Kernel Mode (`cp0Usable`).
  * `CU1` (bit 29) — coprocessor 1 usable. When it is 0 every COP1/COP1X
    instruction, `lwc1`/`swc1`/`ldc1`/`sdc1` and `movf`/`movt` raises
    Coprocessor Unusable (MD00090 Vol III Rev 6.02 §6.2.22, p.100).

  **Not modeled** (read as zero, writes ignored, as Table 9.47 requires for an
  unimplemented field): `CU2`, `CU3`, `RP`, `FR`, `RE`, `MX`, `TS`, `SR`,
  `NMI`, `ASE`, `Impl`. -/
  cp0Status : W32
  /-- Coprocessor 0 `Cause` (register 13, sel 0). Exception entry writes
  `ExcCode` (bits 6..2), `CE` (bits 29..28: the coprocessor unit number for
  Coprocessor Unusable; "loaded, but not defined" for every other exception —
  MD00090 Vol III Rev 6.02 §6.2.3, p.87 — pinned to 0) and, when `Status.EXL`
  was 0, `BD` (bit 31); it leaves every other bit alone. `mtc0` can write
  only `DC` (27), `IV` (23) and `IP1..IP0` (9..8) (`causeWriteMask`). `TI` and
  `IP7..IP2` are not stored here: they are the timer request (`cp0TimerInt`) and the
  hardware interrupt lines (`hwInt`), added when `Cause` is read (`causeValue`,
  `Step.lean`). `WP`, `PCI`, `FDCI` are never set (no watch registers, performance
  counters or EJTAG). -/
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
  when `Status.ERL = 1`. Written by `mtc0` and by the Reset exception (the
  restart PC, `resetException`). -/
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
  /-- Coprocessor 0 `Config.K0` (register 16, select 0, bits 2..0; MD00090 Vol III
  Rev 6.02 §9.45, Table 9.64, p.235: "Kseg0 cacheability and coherency attribute",
  Read/Write, Reset State "Undefined", Compliance "Required"). The model has no cache,
  so the value is stored and read back and has no other effect. Reset value `2`
  (Uncached, the "Required" encoding of Table 9.12, p.133; a pin of the undefined
  reset state). -/
  cp0ConfigK0 : BitVec 3 := 2#3
  /-- Coprocessor 0 `Config.K23` (register 16, select 0, bits 30..28): "Kseg2/Kseg3 cacheability
  and coherency attribute", Read/Write, reset "Undefined", for a Fixed Mapping MMU (MD00090 Vol III
  Rev 6.02 Table A.2, p.317: "Required"; Table 9.64, p.233: "Optional"). Stored and read back; no
  other effect (no caches). Pinned to `2` at power-on and by the Reset exception. -/
  cp0ConfigK23 : BitVec 3 := 2#3
  /-- Coprocessor 0 `Config.KU` (register 16, select 0, bits 27..25): "Kuseg cacheability and
  coherency attribute when StatusERL is zero", Read/Write, reset "Undefined" (Table A.2, p.317;
  Table 9.64, p.233). Stored and read back; no other effect. Pinned to `2` like `K23`. -/
  cp0ConfigKU : BitVec 3 := 2#3
  /-- Coprocessor 0 `Count` (register 9, select 0; MD00090 Vol III Rev 6.02 §9.27, Table 9.44,
  p.183): "acts as a timer, incrementing at a constant rate, whether or not an instruction is
  executed"; Read/Write, reset state "Undefined", "Required". The rate "is implementation-dependent";
  the model's pin is **one increment per `step`** unless `Cause.DC = 1` (`Step.lean`, `timerTick`).
  Also readable with `rdhwr` register 2 (`CC`). Pinned to `0` at power-on; the Reset exception does
  not change it (it is not in the list of §6.2.5, p.89). -/
  cp0Count : W32 := 0#32
  /-- Coprocessor 0 `Compare` (register 11, select 0; MD00090 Vol III Rev 6.02 §9.30, Table 9.46,
  p.187): "maintains a stable value and does not change on its own"; Read/Write, reset state
  "Undefined", "Required". "When the value of the Count register equals the value of the Compare
  register, an interrupt request is made" (`cp0TimerInt`); "Writing a value to the Compare register,
  as a side effect, clears the timer interrupt" (`mtc0`, `Step.lean`). Pinned to `0` at power-on;
  the Reset exception does not change it. -/
  cp0Compare : W32 := 0#32
  /-- `Cause.TI` (bit 30; MD00090 Vol III Rev 6.02 Table 9.52, p.209): "Timer Interrupt ... this bit
  denotes whether a timer interrupt is pending"; Read-only, reset "Undefined", "Required (Release 2)".
  Kept apart from `cp0Cause` because hardware, not software, drives it: set by `timerTick` when `Count`
  equals `Compare`, cleared by a write to `Compare`. Software sees it in bit 30 of `Cause` and, merged
  as the timer request, in `Cause.IP7` (bit 15) (`causeValue`, `Step.lean`). Pinned to `false` at
  power-on; the Reset exception does not change it. -/
  cp0TimerInt : Bool := false
  /-- Coprocessor 0 `HWREna` (register 7, select 0; MD00090 Vol III Rev 6.02 §9.23, Table 9.39,
  p.175): one enable bit per `rdhwr` register, "Required (Release 2)", reset state 0 (§6.2.5, p.89:
  "HWREna ← 0"). Only bits 3..0 exist (`CPUNum`, `SYNCI_Step`, `CC`, `CCRes`, the registers the model
  implements); every other bit "returns a zero and is ignored on a write" (Table 9.39), so the field
  only ever holds values under `hwrenaWriteMask`. -/
  cp0HWREna : W32 := 0#32
  /-- The six **hardware interrupt request lines** `HW5..HW0` (bit `i` = `HWi`), seen by software in
  `Cause.IP(i+2)` (MD00090 Vol III Rev 6.02 Table 9.52, p.211: "IP7..IP2 ... Indicates an interrupt
  is pending ... Hardware interrupt 5 ... Hardware interrupt 0", Read-only; Table 6.2, p.73). They
  are **inputs** to the processor: `step` reads them (`causeValue`, `interruptRequests`,
  `Step.lean`) and never writes them (`step_hwInt`, `Specs/Interrupt.lean`). Who drives them is the
  system's business: the environment of this model (`Semantics/Env.lean`) connects no device, so in
  every state it builds they are `0` (all deasserted). Pinned to `0` at power-on; the Reset
  exception does not change them. -/
  hwInt : BitVec 6 := 0#6
  /-- **Standby**: the processor has executed `wait` and its pipeline is stopped until an interrupt
  request restarts it (MD00086 Vol II-A Rev 6.06, WAIT, p.442: "The WAIT instruction is implemented
  by stalling the pipeline at the completion of the instruction and entering a lower power mode. The
  pipeline is restarted when an external event, such as an interrupt or external request occurs, and
  execution continues with the instruction following the WAIT instruction"). `pc` already holds the
  address of the instruction after the `wait`. Set only by `wait`; cleared when the processor
  restarts (`Step.lean`, `step`) and by the Reset exception ("The assertion of any reset or NMI must
  restart the pipeline", p.442). `false` at power-on. -/
  standby : Bool := false
  /-- **The instruction at `pc` is nullified**: it is the delay-slot instruction of a branch-likely
  instruction whose branch was not taken. The branch-likely's Operation (MD00086 Vol II-A Rev 6.06,
  BEQL, p.73) is "I+1: if condition then PC ← PC + target_offset else NullifyCurrentInstruction()",
  and its `I+1` statements take effect in the instruction time of the delay-slot instruction
  (§1.3, Table 1.1, p.6: "The effect of pseudocode statements for the current instruction labeled
  I+1 appears to occur “at the same time” as the effect of pseudocode statements labeled I for the
  following instruction"). NullifyCurrentInstruction (§2.2.2.5.4, p.26): "The instruction is
  aborted, inhibiting not only the functional effect of the instruction, but also inhibiting all
  exceptions detected during fetch, decode, or execution of the instruction in question. For
  branch-likely instructions, nullification kills the instruction in the delay slot of the branch
  likely instruction."

  So the nullified instruction occupies its own instruction time (`step`): `Count` advances, and an
  interrupt can be taken at it (with `pendingBranch = some _` set alongside, the usual delay-slot
  rule gives `EPC` = the branch-likely, `Cause.BD = 1`; MD00090 Vol III Rev 6.02 Table 6.11, p.87).
  Set only by a not-taken branch-likely (always together with `pc := pc + 4` and
  `pendingBranch := some (pc + 8)`); cleared by the nullifying step (`nullifiedStep`, `Step.lean`),
  by every exception entry and by the Reset exception. `false` at power-on. -/
  nullified : Bool := false

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

/-- Base address of the `.text` segment (MARS default configuration; used by the loader). -/
def textBase : W32 := 0x00400000

/-- Initial value of `$sp` (MARS default configuration). -/
def spInit : W32 := 0x7fffeffc

/-- General exception vector when `Status.BEV = 0` and `EBase` holds its
reset value (MD00090 Vol III Rev 6.02 §6.2.2 "Exception Vector Locations":
base `0x8000_0000`, offset `0x180`). -/
def exceptionVectorAddr : W32 := 0x80000180

/-- The Reset exception vector: "PC is loaded with 0xBFC0 0000" (MD00090 Vol III
Rev 6.02 §6.2.5, p.89; §6.2.2, p.84: "The Reset, Soft Reset, and NMI exceptions are
always vectored to location 0xBFC0.0000"). -/
def resetVector : W32 := 0xBFC00000

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
/-- Coprocessor Unusable: a coprocessor-1 instruction with `Status.CU1 = 0`, a
coprocessor-2 encoding, or a coprocessor-0 instruction outside Kernel Mode with
`Status.CU0 = 0` (MD00090 Vol III Rev 6.02 §6.2.22, p.100). -/
def excCodeCpU : W32 := 11
/-- Integer Overflow (`add`/`addi`/`sub`). -/
def excCodeOv : W32 := 12
/-- Trap (`teq`/`tne`/`tlt`/`tge`/`tltu`/`tgeu` and their immediate forms).
All share this one code; `Cause` does not say which condition fired. -/
def excCodeTr : W32 := 13
/-- Floating Point exception (MD00090 Vol III Rev 6.02 §6.2.23, p.100;
Table 9.53 `FPE`): an enabled IEEE exception, or FCSR `Cause.E`. -/
def excCodeFPE : W32 := 15

/-- Interrupt (MD00090 Vol III Rev 6.02 Table 9.53, p.212: ExcCode 0, "Int"). -/
def excCodeInt : W32 := 0

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
/-- `Status.CU0` (bit 28): coprocessor 0 usable outside Kernel Mode
(MD00090 Vol III Rev 6.02 Table 9.47, p.190: R/W, reset Undefined, "Required for
all implemented coprocessors (Pre-Release 6)"). -/
def statusCu0Mask : W32 := 0x10000000
/-- `Status.UM` (bit 4): base mode User when 1 (MD00090 Vol III Rev 6.02
Table 9.47, p.195: R/W, reset Undefined, Required when Supervisor Mode is not
implemented). -/
def statusUmMask : W32 := 0x10
/-- The `Status` bits `mtc0` can write: `IE`, `EXL`, `ERL`, `UM`, `IM7..IM0`,
`BEV`, `CU0`, `CU1`. Every other bit reads as zero (bit 3, `R0`, "must be
ignored on write and read as zero" when Supervisor Mode is not implemented,
Table 9.47 p.195). -/
def statusWriteMask : W32 := 0x3040ff17

/-- `Cause.BD` (bit 31): the exception was taken in a branch delay slot. -/
def causeBdMask : W32 := 0x80000000
/-- `Cause.DC` (bit 27): Disable Count; cleared by Reset (MD00090 Vol III
Rev 6.02 §6.2.5, p.90: "CauseDC ← 0"). -/
def causeDcMask : W32 := 0x08000000
/-- `Cause.ExcCode` (bits 6..2). -/
def causeExcCodeMask : W32 := 0x7c
/-- `Cause.CE` (bits 29..28): coprocessor unit number of a Coprocessor
Unusable exception. -/
def causeCeMask : W32 := 0x30000000
/-- The `Cause` bits `mtc0` can write: `DC` (27), `IV` (23) and `IP1..IP0`
(9..8). MD00090 Vol III Rev 6.02 §9.36 (p.209): "With the exception of the
IP1..0, DC, IV, and WP fields, all fields in the Cause register are
read-only"; Table 9.52 (p.210) makes `DC` R/W and Required in Release 2. `DC`
("Disable Count register") stops `Count` (`Step.lean`, `timerTick`). `WP` (22) is not writable
here: it is "Required if watch registers are implemented", and the model has none
(`Config1.WR = 0`). `TI` (30) and `IP7..IP2` (15..10) are read-only: they come from the timer
(`State.cp0TimerInt`) when `Cause` is read (`Step.lean`, `causeValue`). -/
def causeWriteMask : W32 := 0x08800300

/-- `Cause.IV` (bit 23): interrupts use the special interrupt vector (offset `0x200`) instead of
the general exception vector (MD00090 Vol III Rev 6.02 Table 9.52, p.210; §6.2.26, p.102). -/
def causeIvMask : W32 := 0x00800000

/-- `Cause.IP7..IP0` (bits 15..8): the pending interrupt requests, in the bit positions of
`Status.IM7..IM0` (MD00090 Vol III Rev 6.02 Table 9.52, p.211-212; Table 6.2, p.73). -/
def causeIpMask : W32 := 0x0000ff00

/-- Vector offset of the Interrupt exception when `Cause.IV = 1` (MD00090 Vol III Rev 6.02
Table 6.9, p.86: "Interrupt, CauseIV = 1 ... 0x200"; §6.2.3 Operation, p.88). -/
def interruptVectorOffset : W32 := 0x200

/-- The Interrupt vector when `Status.BEV = 1` and `Cause.IV = 1`: base `0xBFC0_0200` + `0x200`
(MD00090 Vol III Rev 6.02 Table 6.10, p.86: "Interrupt 1 0 1 ... 0xBFC0.0400"). -/
def interruptVectorBevAddr : W32 := 0xBFC00400

/-- `IntCtl` (CP0 register 12, select 1) as software reads it (MD00090 Vol III Rev 6.02 §9.33,
Figure 9.34 / Table 9.48, p.199-201): `IPTI` (bits 31..29) = 7 (the timer request is merged into
`IP7`, HW5; "Preset by hardware"), `IPPCI` (28..26) = 0 ("If performance counters are not
implemented (Config1PC = 0), this field returns zero on read", p.200), `IPFDC` (25..23) = 0 ("If
EJTAG FDC is not implemented, this field returns zero on read", p.200), the MCU ASE bits and the
reserved fields 0, `VS` (9..5) = 0 ("If neither EIC interrupt mode nor VI mode are implemented
(Config3VEIC = 0 and Config3VInt = 0), this field is ignored on write and reads as zero", p.201).
No field is writable, so the register is this constant. -/
def intCtlValue : W32 := 0xE0000000

/-- `SRSCtl` (CP0 register 12, select 2) as software reads it (MD00090 Vol III Rev 6.02 §9.34,
Figure 9.35 / Table 9.49, p.203-204): `HSS` = 0 ("A value of zero in this field indicates that only
the normal GPRs are implemented"), `EICSS` = 0 ("If Config3VEIC is 0, this field must be written as
zero, and returns zero on read"), `ESS` = `PSS` = `CSS` = 0 (their reset state; HSS is "the highest
value that can be written to the ESS, EICSS, PSS, and CSS fields ... The operation of the processor
is UNDEFINED if a value larger than the one in this field is written", so 0 is the only value they
can hold), reserved fields 0. -/
def srsCtlValue : W32 := 0

/-- `Cause.TI` (bit 30): a timer interrupt is pending (MD00090 Vol III Rev 6.02 Table 9.52,
p.209). -/
def causeTiMask : W32 := 0x40000000

/-- `Cause.IP7` (bit 15): "Hardware interrupt 5" (MD00090 Vol III Rev 6.02 Table 9.52, p.211), the
IP bit the timer request is merged into (`IntCtl.IPTI = 7` pin, `Step.lean`, `causeValue`). -/
def causeIp7Mask : W32 := 0x00008000

/-- The bits of `HWREna` (CP0 7,0) that exist: bit `n` enables `rdhwr` register `n` for `n` =
0 `CPUNum`, 1 `SYNCI_Step`, 2 `CC`, 3 `CCRes`. "If RDHWR register ‘n’ is not implemented, bit ‘n’ of
this field returns a zero and is ignored on a write" (MD00090 Vol III Rev 6.02 Table 9.39, p.175):
registers 4..31 are not implemented (4, 5 are Release 6; 6..28 reserved; 29 `ULR` needs the optional
UserLocal register; 30, 31 implementation-dependent, none). -/
def hwrenaWriteMask : W32 := 0x0000000F
