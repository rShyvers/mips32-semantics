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

  The branch-likely family does not use this when not taken: its delay-slot
  instruction is nullified, so the branch-likely's own step moves `pc`
  straight to `pc + 8` and leaves this `none`. -/
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

  * `IE` (bit 0), `IM7..IM0` (bits 15..8) — stored and read back only; no
    interrupt is ever raised by this model.
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
("Disable Count register") is stored and read back but has no effect: the
model has no `Count` register. `WP` (22) is not writable here: it is
"Required if watch registers are implemented", and the model has none
(`Config1.WR = 0`). -/
def causeWriteMask : W32 := 0x08800300
