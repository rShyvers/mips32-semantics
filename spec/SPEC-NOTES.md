# MIPS32 Release 6 semantics: pinned conventions, choices and divergences

**The target is the MIPS32 Release 6 architecture** (little-endian, 64-bit FPU with `Status.FR = 1`,
IEEE 754-2008 NaNs, Fixed Mapping MMU, no optional modules; see `CLAUDE.md`, "Target profile").
MD00082 Vol I-A Rev 6.01 ("Vol I"), MD00086 Vol II-A Rev 6.06 ("Vol II") and MD00090 Vol III Rev 6.02
("Vol III") are normative; **the manual wins over any emulator**. The Lean small-step semantics
specifies what programs for that processor mean. The pre-R6 Release 2 model is kept only at tag
`mips32r2-final`; nothing here describes it except where a section says so.

**Oracles.** QEMU (`qemu-system-mipsel -cpu mips32r6-generic`) and LLVM (`llvm-mc -triple=mipsel
-mcpu=mips32r6`) are the differential oracles (`tests/oracle`, `scripts/oracle.py`). **MARS 4.5 cannot
run Release 6**: it implements a pre-R6 (SPIM-derived) instruction set, a 32-bit FPU and no
CP0/exception model beyond a few registers. It is kept as a differential oracle only for the 29
`tests/corpus` programs, which were pruned to programs that mean the same thing under R6 and under
MARS (no HI/LO, branch-likely, `movz`/`movn`, `lwl`/`lwr`, `madd`, `c.cond`...; §10.2). Where MARS and the
architecture disagree the architecture wins and the divergence is recorded here; where an oracle
disagrees with the manual the deviation is declared in the test (§10.1) and recorded here.

How to read this file. Page numbers are **printed** pages. Citations are document + revision +
instruction or section + page; every one was looked up with `manuals/mipsdoc.py`. §1-§8 describe the
model's conventions, §9 is the numbered list of pins (the code cites it as "SPEC-NOTES §9 item N"), §10
the oracle deviations, §11 the independent manual spec's constants and choices (`Manual/Choices.lean`),
§12 the profile decisions D1-D13. Per-instruction semantics are in [`INSTRUCTION-REF.md`](INSTRUCTION-REF.md),
coverage in [`R6-COVERAGE.md`](R6-COVERAGE.md). MD00086's table of contents and body both have a "p.3";
`mipsdoc.py` reports both. Facts about MARS come from the MARS 4.5 source tree, which is **not
vendored** (only `vendor/mars/Mars4_5.jar` is): class names below are pointers, and line numbers cannot
be re-checked here.

## 1. Memory map

All addresses are **virtual**. `State.physMem` is physical memory; the Fixed Mapping MMU (item 27)
maps between them. The layout is the environment's convention (the loader and assembler), except for
the reset vector, the exception vectors and the segment boundaries, which are architectural.

| Region | Virtual address | Where defined | Physical address (`Env.loadAddr`, `ERL = 0`) |
|---|---|---|---|
| `.text` base, hosted entry point | `0x0040_0000` | `textBase` (`Types.lean`) | `0x4040_0000` |
| `.data` base | `0x1001_0000` | `dataBase` (`Asm/Syntax.lean`) | `0x5001_0000` |
| initial `$sp` (boot convention only) | `0x7FFF_EFFC` | `spInit` (`Types.lean`) | `0xBFFF_EFFC` |
| general exception vector (BEV = 0, `EBase` at reset), `.ktext` default | `0x8000_0180` | `exceptionVectorAddr`, `ktextBase` | `0x0000_0180` |
| `.kdata` default | `0x9000_0000` | `kdataBase` | `0x1000_0000` |
| reset vector (BEV = 1) | `0xBFC0_0000` | `resetVector` | `0x1FC0_0000` |

Not modeled: `$gp` (`0x1000_8000` in MARS; the model leaves it 0), the heap/`sbrk`, MARS's `.extern`
base. `$sp = 0x7FFF_EFFC` comes from SPIM/MARS, not classic MIPS: do not change it. MARS has no address
translation; no corpus program can tell, because it runs in Kernel Mode with `ERL = 0`, where every MARS
address is legal and the translation is injective on the segments MARS uses. The whole 2^32-byte
physical space exists and is byte-addressable; unwritten bytes read 0 (item 6).

## 2. Registers

- 32 general-purpose registers of 32 bits. `$zero` reads 0 and ignores writes. After `resetState` all
  are 0; the hosted start state (`hostedStart`, item 25) sets only `$sp`.
- **No `HI`/`LO`**: Release 6 removed the HI/LO instructions (`mult`, `div`... of earlier releases); `MUL`,
  `MUH`, `MULU`, `MUHU`, `DIV`, `MOD`, `DIVU`, `MODU` write a GPR (Vol II-A; `State` has no `hi`/`lo`).
- 32 FPRs of 64 bits (`Status.FR = 1` is read-only; "Release 6 disallows bi-modal support", Vol III §9.32,
  Table 9.47, p.190). A 32-bit write (`mtc1`, `lwc1`, `.S` results) leaves the upper half unchanged
  (item 13). `FCSR` is as Vol I Table 6.8 (p.92-96) with `NAN2008 = ABS2008 = 1` read-only; FP control
  reads and writes: item 13.
- CP0: the registers of `cp0Layout` (`Exec/Cp0.lean`): `UserLocal` (4,2), `HWREna` (7,0), `BadVAddr` (8,0),
  `BadInstr` (8,1), `BadInstrP` (8,2), `Count` (9,0), `Compare` (11,0), `Status` (12,0), `IntCtl` (12,1),
  `SRSCtl` (12,2), `Cause` (13,0), `EPC` (14,0), `PRId` (15,0), `EBase` (15,1), `Config` (16,0) ..
  `Config5` (16,0-5), `LLAddr` (17,0), `ErrorEPC` (30,0), `KScratch1..6` (31,2-7). `MFC0` of any other
  `(rd, sel)` returns 0 and `MTC0` is ignored: "Release 6: Reading a reserved register or a register that is
  not implemented for the current core configuration returns 0" (Vol II MFC0 p.266); "Release 6: Writes to a
  register that is reserved or not defined for the current core configuration are ignored" (MTC0 p.290). The
  layout is keyed by `Release`, so another release adds its own table. Values and field tables: §11, item 10.

## 3. Execution conventions

- **Delay slots and forbidden slots** (item 1). `j`, `jal`, `jalr`/`jalr.hb`, `beq`, `bne`, `blez`, `bgtz`, `bltz`,
  `bgez`, `bal`, `nal`, `bc1eqz`, `bc1nez` have one architectural delay slot, executed whether or not the
  branch is taken. The compact branches and jumps (`bc`, `balc`, `beqc`..., `jic`, `jialc`) have none; a
  **not-taken conditional** compact branch has a forbidden slot (the next instruction). No branch-likely
  instructions exist.
- **Execution starts at the `.text` base** (`0x0040_0000`), not at `main` (MARS's `StartAtMain` is false by
  default).
- Instruction fetch reads the little-endian word at `pc` from `physMem` through the MMU, the same memory
  and translation loads and stores use (items 6, 26, 27). A misaligned `pc` raises Address Error (AdEL).
- **The processor never halts** (`step : State → State`). Reserved Instruction, Address Error, Integer
  Overflow, System Call, Breakpoint, Trap, Coprocessor Unusable, Floating Point and Interrupt are state
  transitions to the vector (INSTRUCTION-REF Global rule 6).
- **The hosted run stops** (an environment convention, `Semantics/Env.lean`, item 25) on: the `exit`
  service, entry to an exception vector the loaded image does not cover (`unhandledException`), `pc` leaving
  the loaded image (`noInstruction`), or the step limit.
- `step = timerTick ∘ stepCore`: interrupt entry if `interruptTaken`, else a standby step after `WAIT`, else
  `execute` (fetch, strict decode, per-family `Exec/<Family>.lean` table); then `Count` advances (item 28).

## 4. Alignment and errors

Release 6 permits hardware to support misaligned accesses or to trap them: "it is permitted for a
processor implementation to produce the Address Error exception for all misaligned accesses" (Vol I
Appendix B.2, p.128; each load/store page repeats "Release 6 allows hardware to provide address
misalignment support in lieu of requiring natural alignment"). **The model traps every misaligned
load, store and fetch (D3)**: Address Error, AdEL (ExcCode 4) for loads and fetch, AdES (5) for stores,
`BadVAddr` = the virtual address. `LL`/`SC` always trap: "misalignment support is NOT provided for the
load-linked/store conditional instructions" (B.2, p.128; SC p.349). Hardware misaligned support was the
alternative and is not modeled. Word and halfword accesses need 4- and 2-byte alignment; `LDC1`/`SDC1`
need 8 (the 64-bit FPU); byte access has none. `LWL`/`LWR`/`SWL`/`SWR` do not exist in Release 6. The
QEMU oracle tests of misaligned accesses declare the affected fields `unpredictable` (QEMU may implement
the permitted misaligned support; §10.1).

## 5. Syscalls and the hosted environment

`syscall` is the System Call exception (ExcCode 8) for the processor (item 9). The **hosted
services** of `Env.lean` are the environment's: 1 print int, 4 print string (NUL-terminated, at most
`printStringFuel` = 65536 bytes, item 20), 10 exit, 11 print char; `$v0` = service, `$a0` = argument.
Any other `$v0` selects nothing (the processor then takes the exception); `MipsRun --bare` serves none.
MARS defines many more services (ReadInt, Sbrk, Open, Time, MIDI, dialogs...); they are not modeled.

## 6. Instruction set

The modeled set is the 203 constructors of `Instruction` (`Semantics/Instruction.lean`), one union type for
every release; a release has an instruction exactly when its decoder table (`decodeFor profile.release`,
one table per opcode) emits it. Per-family lists are in the README, the matrix in `docs/TRACE.md`, the
page-by-page classification in `R6-COVERAGE.md` (263 Vol II-A pages: 137 implemented, 77 removed in R6, 36
optional modules absent, 6 TLB instructions that raise RI, 7 assembler idioms, 0 open). Words of removed
or absent instructions do not decode and raise Reserved Instruction (Coprocessor Unusable for an
unusable coprocessor's space, item 10): "6Rm and 6R instructions signal a Reserved Instruction exception
when executed by a Release 6 implementation" (Vol II Table A.1, p.451).

Pseudo-instructions (`li`, `la`, `move`, `nop`, `blt`...) are assembler sugar following the MARS/GNU-as
expansions; they are not part of the machine semantics. Assembler notes: item 15.

## 7. Endianness and data representation

**Little-endian only** (D1). `Config5.DEC = 0` ("Only Little-Endian mode supported. Any implementation must
support Little-endian mode", Vol III §9.50, Table 9.69, p.261), `Config.BE = 0` (Table 9.64, p.234). The byte
order is one profile constant, `profile.bigEndianMem = false` (Vol I p.16, Vol II Table 1.1 p.6), which the
byte-order helpers of `Types.lean` and every memory access read, so a big-endian profile changes one
constant. A big-endian-only Release 6 core is not conformant, and dual-endian needs an unspecified
external register (p.261), so neither is chosen. Integers are two's complement; arithmetic is defined on
bit patterns with wraparound.

## 8. What is trusted, what is not

- **Spec target:** the MIPS32 Release 6 architecture as written in the three manuals. What the Lean
  development proves about `step`, and how much is independent of the implementation, is in the README and
  `docs/OVERVIEW.md`; nothing here claims the model is "proven correct" against the manuals. The
  independent correctness result is `Refine.step_eq_manual` (`step` refines the transcription in
  `Semantics/Manual/` for every state satisfying `Refine.Inv`); the per-instruction `_spec_raw` theorems
  restate what `step` computes. The manuals are read by the authors; no machine-readable form exists.
- **Empirical oracles:** QEMU `mips32r6-generic` with `llvm-mc` (`tests/oracle`; 176 programs and
  `encodings.list`), MARS 4.5 on 29 corpus programs. Agreement supports the implementation; it does not
  define the spec.
- **Not modeled** (D4, D5): TLB (`Config.MT = 3`), caches (`CACHE` is a no-op), EJTAG, Supervisor and Debug
  Mode, vectored/EIC interrupts, GPR shadow sets beyond set 0 (`SRSCtl.HSS = 0`), watch registers,
  performance counters, coprocessor 2, and the optional modules MSA, microMIPS, VZ, MT, DSP, EVA, XPA,
  MCU, CRC, GINV, VP. Exception entry, `eret`/`eretnc`, interrupts, the timer and `WAIT` are modeled.

## 9. Pins, choices and divergences

A **pin** is a choice among outcomes the manual allows (UNPREDICTABLE, UNDEFINED, implementation-
dependent); a **divergence** is a place an oracle differs from the manual. Items keep the numbers the
code cites. Retired item numbers (Release 2 only): 1b (branch-likely nullification; the model has no branch-likely), 8 and 17
(stubs below); item 21 is a pointer. Divergences from MARS are in items 3-5, 14 and §10.2.

1. **Delay slots, forbidden slots, no branch-likely.**
   - A taken branch/jump does not change `pc` to the target in the same step: it moves to `pc + 4` (the
     slot, which always executes) and schedules the target in `State.pendingBranch`; the slot's own step
     applies it (`advance`/`mkNext`, `Exec/Branch.lean`). `jal`/`bal`/`jalr` link `pc + 8`. A not-taken
     delay-slot branch also leaves `pc` at the slot and records `pc + 8`, so `pendingBranch.isSome` means
     exactly "in a delay slot" (needed for `EPC`/`Cause.BD`). Real MIPS has the slot; MARS's default
     (`DelayedBranching = false`, `Settings.java`) has none (item 5, §10.2).
   - **Forbidden slot (D6).** A not-taken conditional compact branch sets `pendingBranch := some (pc + 8)`: no
     new `State` field, the next instruction is treated as in a delay slot. A taken compact branch or jump
     sets `none` and has neither slot ("neither a delay slot nor a forbidden slot", Vol I §5.3.2.2, p.62). An
     exception in a forbidden slot reports `EPC` = the compact branch and `Cause.BD = 1`: "the hardware
     reports an Exception PC (CP0 EPC) of the branch, with a status bit set (StatusBD)" (Vol I §5.3.2.2, p.62;
     "StatusBD" is a misprint for CauseBD, Vol III Table 9.52, p.209). Vol III is silent (§6.2.3, p.87;
     BadInstrP, p.181); the Vol I text is the more specific one. `Manual.Delay.forbiddenSlot`.
   - **A control transfer instruction in a delay or forbidden slot raises Reserved Instruction**, which Release
     6 requires: "Pre-Release 6: ... UNPREDICTABLE" / "Release 6: ... Release 6 implementations are required to
     signal a Reserved Instruction exception" (Vol II BEQ p.72, JALR p.196; Vol I §5.3.2.1, p.62); likewise
     ERET (p.177), ERETNC (p.179), WAIT (p.442), BC1EQZ/BC1NEZ (p.54). The slot set is `isBranchLike`
     (branches, jumps, compact forms, `nal`, `bal`, `eret`, `eretnc`, `wait`, `pause`, `bc1eqz`, `bc1nez`).
     `branch_in_delay_slot_reserved_instruction`, `forbidden_slot_cti_reserved` (trusted statements);
     oracle tests `cti_in_delay_slot_reserved`, `forbidden_slot_cti`, `exc_forbidden_slot` (QEMU agrees).
   - `NAL` is "a not-taken branch, with a delay slot" (Vol II NAL p.306). `PAUSE`: item 16.
   - **`BadInstrP` for an exception in a forbidden slot is the compact branch word** (see item 34).
   - **Declared QEMU deviation:** an exception in the delay slot of a statically never-taken branch
     (`exc_delay_slot_never_taken_branch`, §10.1).
2. **`DIV`/`DIVU`/`MOD`/`MODU` by zero (D12; pin).** "If the divisor in GPR rt is zero, the result value is
   UNPREDICTABLE" (Vol II DIV/MOD/DIVU/MODU p.168); "No arithmetic exceptions occur. Division by zero produces
   an UNPREDICTABLE result" (p.169). The model computes as if the divisor were 1: `DIV`/`DIVU` give the
   dividend, `MOD`/`MODU` give 0 (`Oracle.divByZero`). Signed `DIV` of `INT_MIN` by -1 follows the
   Operation. A scratch probe (`div/mod/divu/modu rd, rs, $zero`) showed the model and QEMU
   `mips32r6-generic` agree. `MUL`/`MUH` and the unsigned forms have no pinned cases. There is no `HI`/`LO`.
3. **`lw`/`sw` offset sign-extension: MARS latent bug, we follow the ISA.** MARS uses the raw 16-bit I-format
   offset without sign extension for `lw`/`sw` (the defensive re-extension exists in `lb`/`lh`/`sh`/`addi`/
   `slti`). Invisible for assembler-built programs, which is all the corpus has; it would zero-extend negative
   offsets on raw binary input. The model sign-extends (`Exec/Memory.lean`), and uses 9-bit signed offsets for
   `LL`/`SC`/`PREF` (R6 encodings, `signExt9`).
4. **Endianness.** The model is little-endian (§7); MARS 4.5 headless is little-endian too (`Memory.java:90`
   `byteOrder = LITTLE_ENDIAN`, `setByteOrder` is never called), so the former byte-order divergence of the R2
   model is gone. The corpus programs `mem_byte_half` etc. were written endian-invariant when the model was
   big-endian and stay so; they are no longer needed for that reason.
5. **`jal`'s `$ra` differs from MARS whenever the delay slot is non-empty (language wins).** Real MIPS links
   `pc + 8` (the slot executes before the return); MARS's default has no slot and links `pc + 4`. With a
   real no-op in the slot the two values differ and cannot agree for any filler. The corpus program
   `jump_jal` therefore does not probe `$ra`'s value (it jumps back with `j`); `jr_jalr` only uses `$ra` as a
   return address. R6 keeps `JAL`'s delay slot and link rule (Vol II JAL).
6. **Instruction fetch reads memory (resolved).** `step` fetches with `readMemWord s s.pc`, through the same
   MMU and memory as loads and stores; a `Program` (assembler output) is only the loader's input (`load`).
   Writing the instruction stream is defined: SYNCI "is used after a new instruction stream is written to make
   the new instructions effective relative to an instruction fetch" (Vol II SYNCI p.412). The model has no
   caches (`Config1.IL = DL = 0`), so a store is visible to the next fetch and `synci` is a no-op (its
   optional AdEL for kernel addresses is "implementation dependent", p.412: not raised,
   `Impl.SynciAddressError = false`). `sw_next_instruction_is_fetched`, `store_changes_next_instruction`,
   oracle test `smc_synci`. **Memory never written reads as 0** (a pin; the architecture does not define it;
   MARS and the QEMU harness also zero-fill): an unloaded address executes as `sll $0, $0, 0`.
7. **LL/SC (`Config5.LLB = 1`).** In Release 6 "`Config5LLB` is read-only 1" (Vol III Table 9.69, p.264), so
   an `SC` fails after a store to the LL'd block ("if Config5LLB=1; else whether such a store causes the SC to
   fail is not predictable", Vol II SC p.347) and is not made to fail by a load. The model: **every store
   clears `LLbit`** (`Oracle.storeClearsLL = true`) and **no load does** (`Oracle.loadClearsLL = false`); these
   constants are right for every address, since the model does not implement a block size wider than a
   word. `ll` records its address in `State.llAddr`; `sc` compares bits 31..2 only ("An SC will fail if the
   aligned address of the SC does not match that of the preceding LL", SC p.347); it compares the **virtual**
   address ("the address is the same if the virtual address, physical address, and cacheability &
   coherency attribute are identical", SC p.348), so an `sc` through the other kseg0/kseg1 alias fails (one
   permitted outcome). `sc` clears `LLbit` (success or failure); `eret` clears it ("An ERET instruction is
   executed. (Release 5 includes ERETNC, which will not cause the SC to fail.)", SC p.347); **`eretnc` does
   not** (ERETNC p.179). **Exception entry keeps `LLbit`** (a change from the R2 model; reading: the failure SC p.350 describes,
   "Exceptions between the LL and SC cause SC to fail", is produced by the `ERET` that ends the handler, which
   clears `LLbit`, p.347, while `ERETNC` "will never cause the SC to fail", p.179, so entry itself need not clear
   it); `resetException` clears it. `pref` does not touch it. `LLAddr` (17,0): `LLB` (bit 0)
   is `LLbit`, "LLB can be cleared by software but cannot be set"; `PAddr` is not implemented and reads 0
   (Vol III Table 9.72, p.270: "an implementation may implement as many of the bits ... as it finds
   convenient"; "For the unimplemented address bits, writes are ignored and reads return zero"). `SC` without
   a preceding `LL`: with `LLB = 1` success or failure is mandated but which is open (SC p.348); the oracle
   field is `unpredictable`. See item 34 for the relation looseness.
8. Retired (Release 2: duplicate of item 4).
9. **`syscall` is always the System Call exception; the MARS-style services are the environment's.** "A system
   call exception occurs, immediately and unconditionally transferring control to the exception handler"
   (Vol II SYSCALL p.415; `SignalException(SystemCall)`). `step` does this for every `$v0`
   (`syscall_spec_raw`). The hosted run (item 25) performs services 1/4/10/11 instead of stepping when the
   instruction at `pc` is a `syscall` selecting one, as if an OS had served the exception and returned
   (`hostStep_syscall_spec`; `hostStep_eq_step` says it is `step` otherwise). MARS reports an error for unknown
   service numbers; the differential harness treats "MARS error" and "unhandled System Call exception" as the
   same verdict (`DiffHarness.lean`). The `code` field is ignored (Vol II p.415), and `SIGRIE code` is a
   Reserved Instruction exception (p.375).
10. **Operating modes; CP0 scope; reset; identification.**
    - **Modes.** Kernel Mode and User Mode (Vol III ch.3, p.21-23); Supervisor Mode and Debug Mode are not
      implemented ("Supervisor Mode is not supported with a Fixed Mapping MMU", Vol III §A.1, p.313; Vol I
      §2.4.2, p.32; `Status` bit 3 `R0`, so `KSU = UM || 0`). `kernelMode` = `UM = 0` or `EXL = 1` or
      `ERL = 1`; `userMode` = `UM = 1`, `EXL = 0`, `ERL = 0`.
    - **No `CU0`.** Release 6 `Status` has `CU3..CU1` and bit 28 is the software bit `RW` (Vol III Figure 9.33
      p.189, Table 9.47 p.190: CU3..CU0 "Required ... (Pre-Release 6)", CU3..CU1 "(Release 6)", `RW` "Required
      (Release 6)"). Vol III §3.5.3 (p.23) still lists "The CU0 bit in the Status register is 1" (pre-R6 wording);
      the model follows Table 9.47: **coprocessor 0 is usable exactly in Kernel Mode** (`cp0Usable`). When it
      is not, `mfc0`/`mtc0`/`di`/`ei`/`eret`/`eretnc`/`wait`/`rdpgpr`/`wrpgpr`/`cache`/`dvp`/`evp` and every
      undecodable COP0 or CACHE word raise Coprocessor Unusable with `Cause.CE = 0` (Vol III §6.2.22, p.100;
      for undecodable words CpU replaces RI, §6.2.21 p.99). `eret`/`wait` in a delay slot are Reserved
      Instruction in every mode (the slot check comes first; item 1).
    - **User-Mode address checks.** A kseg0..kseg3 reference from User Mode (fetch, load, store) raises Address
      Error (Vol III Table 4.2 p.30, §6.2.9 p.92-93; the MMU's `translate`, item 27).
    - **Implemented `Status` bits:** `IE` (0), `EXL` (1), `ERL` (2), `UM` (4), `IM7..0` (15..8), `BEV` (22), `RW` (28),
      `CU1` (29): write mask `0x3040_FF17` (`statusWriteMask`; `Manual.StatusWritable`), all others read 0.
      **Implemented `Cause` bits:** `BD` (31), `CE` (29..28), `ExcCode` (6..2) written by exception entry; `DC` (27),
      `IV` (23), `IP1..0` (9..8) writable by `mtc0` (mask `0x0880_0300`; Vol III §9.36, p.209-211). `WP` (22) reads
      0 and "hardware ignores a write of 1" (p.211). `TI` (30) is the timer request and `IP7..IP2` show the
      timer and the hardware lines (items 28, 29). `PCI`, `FDCI` are never set.
    - **Reset** (`resetException`, `resetState`; Vol III §6.2.5, p.89-90): `PC ← 0xBFC0_0000`, `Status.BEV ← 1`,
      `Status.ERL ← 1`, `Cause.DC ← 0`, `HWREna ← 0`, `EBase` Exception Base ← 0 (reads `0x8000_0000`),
      `Config.K0 ← 2`, `ErrorEPC` ← the restart PC (the branch when the reset hits a delay slot); standby is
      left. Registers the section does not list "only the following registers have defined state" (p.89) keep
      their value (`Oracle.resetUndefined`), except pins: `Config.K23 = Config.KU = 2` (reset "Undefined for
      processors with a Fixed Mapping MMU", Table 9.64 p.233), `LLbit ← 0`, the pending branch dropped,
      `Config5.SBRI ← 0` (Table 9.69 p.263). `UserLocal`, `BadInstr`, `BadInstrP`, `KScratch1..6` have reset
      "Undefined" and keep their values. `powerOnState` pins every undefined register to 0 for a cold start
      (GPRs, FPRs, `FCSR` whose fields reset "Undefined", Vol I Table 6.8 p.92-95, `Count`, `Compare`, memory),
      so `resetState`: `pc = 0xBFC0_0000`, `Status = 0x0040_0004`, `ErrorEPC = 0` (p.89: on power-up the restart
      PC "may or may not be predictable"). **Hosted start state** (`Env.lean`): `hostedStart = bootConvention
      textBase resetState`, i.e. reset followed by what a boot ROM would do: `Status ← 0x2000_0000` (only `CU1`;
      Kernel Mode, `BEV = ERL = 0`), `$sp ← spInit`, jump to `textBase` (`hostedStart_is_reset_then_boot`).
      `MipsRun --reset` starts at the reset vector instead. **Reset is not in the QEMU oracle**: with `-kernel`
      QEMU's `malta` boot stub sits at `0xBFC0_0000` and clears `ERL`.
    - **Identification registers** (read-only constants, §11.1): `PRId = 0x0001_0000`; `Config = 0x8000_0980` plus
      `K23`/`KU`/`K0` (R/W; all of 2 and 3 accepted, unsupported values ignored: "For Release 6, writes of
      unsupported values are ignored", Table 9.64 p.233, 235; Table 9.12 p.133: 2 Uncached and 3 Cacheable
      "Required"; no effect, there are no caches); `Config1 = 0x8000_0001`, `Config2 = 0x8000_0000`,
      `Config3 = 0x8C00_3000`, `Config4 = 0x80FC_0000`, `Config5 = 0x0000_2010` (+ `SBRI` R/W). `EBase` (15,1;
      Vol III §9.41, p.223-224): bits 29..12 writable, 31..30 fixed `10`, `CPUNum` 0; supplies the vector base
      when `BEV = 0`.
    - **Config4.IE note.** `Config4.IE = 0`. Table 9.68 p.254 says for IE "00 ... In Release 6, this field is
      reserved; i.e., TLBINV and TLBINVF must be supported in Release 6 implementations" and "10 ... Always
      Required for implementations with TLBs; i.e., ConfigMT=1 or 4 (Release 6)", which presumes a TLB; the
      instruction pages are specific to `MT = 3`: "Release 6: On processors that include a Block Address
      Translation (BAT) or Fixed Mapping (FM) MMU (ConfigMT = 2 or 3), the operation of this instruction causes a
      Reserved Instruction exception" (TLBINV p.423, TLBINVF p.426). The model follows the instruction pages and
      `IE = 0` ("not supported by hardware"); the oracle test `cp0_config45_sbri` declares the field
      `unpredictable`.
    - **Not present, by profile:** TLB registers (Index, Random, EntryLo0/1, Context, PageMask, Wired, EntryHi,
      PageGrain): "For Release 6, writes to these registers are ignored, reads return 0" and the TLB
      instructions "must cause a Reserved Instruction Exception" (Vol III §A.1.3, p.317); `TLBWR`, `TLBWI`,
      `TLBP`, `TLBR`, `TLBINV`, `TLBINVF` raise RI (D4). Watch registers, EJTAG, performance counters, shadow
      sets > 0, coprocessor 2 (below).
    - **Coprocessor 2 absent:** `Config1.C2 = 0`, `Status.CU2` reads 0, so every COP2-space word (`COP2`,
      `MFC2`, `BC2EQZ`, `LWC2`...) raises Coprocessor Unusable with `Cause.CE = 2` (Vol III §6.2.22, p.100:
      "A COP2, LWC2, SWC2, LDC2, or SDC2 instruction was executed, and the CU2 bit in the Status register was a
      zero"). QEMU raises RI instead: declared deviation `r6gap_absent_modules` (§10.1).
    - **Absent modules and removed encodings raise RI** (Kernel Mode): `DERET`/`SDBBP` (EJTAG subsetted out,
      D7), `MFHC0`/`MTHC0` (`Config5.MVH = 0`), EVA, CRC32, GINV, `DDIV`, `JALX`, MSA, microMIPS (`R6-COVERAGE.md`,
      test `r6gap_absent_modules`). `DVP`/`EVP` are NOPs with `Config5.VP = 0`, in Kernel Mode, CpU outside it
      (Vol II DVP p.172-173, EVP p.181-182; Vol III Table 9.69 p.263). `CACHE` with no caches is a no-op (D8).
11. **Strict decoding and UNPREDICTABLE encodings (pin).** A word with a nonzero reserved field, an
    UNPREDICTABLE field combination (EXT `lsb + msbd > 31`, INS `lsb > msb`, a `jalr` hint other than the two
    defined) or an unmodeled CP0 register field raises Reserved Instruction. The manual makes nonzero
    unnamed fields UNPREDICTABLE (Vol II §2.1.1, p.12) and UNPREDICTABLE "may cause arbitrary exceptions"
    (§1.2.1, p.3; pdf page 13): RI is a legal pinned outcome, not a mandate (`Oracle.unpredictableEncoding`,
    `Oracle.extOutOfRange`, `Oracle.insLsbAboveMsb`). MARS's decoder is laxer. Don't-care fields the model
    tolerates are listed in INSTRUCTION-REF Global rule 6. The manual spec has its own decoder
    (`Manual.Decode`, from the format diagrams); words outside every diagram decode as `.reserved` and
    `decode_agrees_manual` ties the model's decoder to it.
12. **Stops are the environment's.** `exit`, `unhandledException code epc badVAddr` and `noInstruction pc`
    (`HaltReason`, `Env.lean`) have no architectural counterpart: they are where the hosted run stops
    observing the processor (item 25).
13. **Floating point follows the manuals bit for bit; no host floats.** All FP arithmetic is `FpOps.lean`: the
    exact result on bit patterns, one correctly rounded pack under `FCSR.RM`, IEEE flags, FCSR
    Cause/Flags/Enables, the Floating Point exception (ExcCode 15, no destination write). Profile: 64-bit FPU,
    `FIR = 0x00F3_0000` (`S`, `D`, `W`, `L`, `F64`, `Has2008` = 1; `PS`, `3D`, `UFRP` = 0; Vol I §6.5.1 Table
    6.5 p.88-89, `FIR.FREP = 0` "Optional" p.88, Table 6.4 note 3 p.85 "requires S, D, W, and L"), IEEE
    754-2008 NaN encoding (`NAN2008 = ABS2008 = 1` read-only, Table 6.8 p.94: a quiet NaN has fraction MSB 1),
    default QNaN `0x7FC0_0000` / `0x7FF8_0000_0000_0000` (Table 6.3 p.82). L-format conversions are in scope.
    Pins and manual inconsistencies:
    - **NaN operand choice.** Vol I §6.3.1.5 (p.82-83): with `NAN2008 = 1` "the mantissa portion of the input NAN
      operand is preserved as much as possible: If the chosen input is a QNAN, the entire mantissa is passed ...
      If the chosen input is a SNAN, the only change is to set the leftmost/most-significant mantissa bit". The
      manual does not say *which* operand is chosen. The model chooses **the first signaling NaN in operand
      order, made quiet (Invalid signaled), else the first quiet NaN** (`nanResult_first`,
      `nanResult_first_snan`; trusted statements "The NaN pin"), the order QEMU `mips32r6-generic`
      implements. Operand order is the printed order of each Operation; for the fused `MADDF`/`MSUBF`
      it is `[fd, fs, ft]` (Vol II MADDF p.259-260). A conversion passes the operand's payload, a signaling NaN
      quieted, with Invalid for a signaling one (`convertNaN`; the alternative would be the new QNaN).
      `MIN`/`MAX`: item 31.
    - **`ABS.fmt`/`NEG.fmt` are not arithmetic** with `ABS2008 = 1`: the sign bit is cleared/flipped, a NaN is
      not changed otherwise and signals nothing (Vol II ABS.fmt p.32, NEG.fmt p.307: "If FIRHas2008=0 or
      FCSRABS2008=0 then this operation is arithmetic"). The former R2 pin (item 21, reading A') is gone.
    - **Upper half of an FPR after a 32-bit write is kept unchanged.** Vol I §6.6.2 (p.98) "leaves the upper
      bits of the FPR UNPREDICTABLE"; QEMU does the same (`Oracle.fprUpper`).
    - **`CFC1`/`CTC1`.** `CFC1` of `fs` 1..4 raises Reserved Instruction ("In Release 6 and later, a Reserved
      Instruction exception occurs if fs specifies a register that does not exist", Vol II CFC1 p.129;
      `fs` = 1..4 "Release 6 traps" p.129-130). **`CFC1` fs = 5 (`FRE`) raises RI (decision, Wave R6-7)**: with no
      `Config5.FRE` in the profile (`FIR.FREP = 0`, `Config5.UFR` R0, Vol III Table 9.69 p.264) the Restrictions
      give RI; the choice point `Oracle.cfc1Unpredictable` was removed (the `ConfigAR ≤ 2` glyph on p.130 is
      read as `< 2`, a misprint: read literally the Release 6 `FRE` read would be dead code). QEMU agrees
      (`fp_cfc1_ri_fs5`); QEMU signals no RI for fs 1..4 (§10.1). `CTC1` fs 1, 4, 5, 6 raise RI ("Release 6
      implementations and later are required to produce a Reserved Instruction exception" for the
      UFR/UNFR/FRE/NFRE aliases with `rt ≠ GPR[0]`, CTC1 p.149; the register-number table p.150);
      reserved bits of a value written to `FCSR`/`FCCR`/`FEXR`/`FENR` are ignored (`FCSRWrite`; `Oracle.ctc1Unpredictable`,
      p.150 "UNPREDICTABLE"); FCC bits of `FCSR` are reserved in R6 (Table 6.8 p.92) and `FCCR` reads 0. The
      `CheckFPException()` after the UNPREDICTABLE arms still runs. `FIR` is read-only (`fp_ctc1_fir_readonly`).
    - **`FCSR.FS = 1` flushes subnormal inputs and tiny results.** "As of Release 5, every input subnormal value
      is replaced with zero of the same sign" (Vol I Table 6.8 `FS`, p.93); "Flushing of subnormal input operands
      in all instructions except comparisons causes Inexact exception to be signaled" and "For floating-point
      comparisons, the Inexact exception is not signaled" (§6.7.2.4, p.102); "Flushing of tiny non-zero results
      causes Inexact and Underflow exceptions to be signaled" (p.102). **Decision (orchestrator, manual-
      explicit):** the input flush signals Inexact for every non-comparison operation; `CMP`, `MIN`, `MAX`,
      `MINA`, `MAXA`, `CLASS` flush without Inexact (Table 7.9 p.110 lists them as comparisons). 18 trusted FP
      statements were restated stronger (`WithFlushInexact`). Tests: `fp_fs_flush_input_inexact`,
      `fp_flush_to_zero_fs` (QEMU does not signal these: §10.1). Unimplemented Operation (`Cause.E`) is never
      raised.
    - **Misprints read as intended.** (a) CFC1 p.130 `if Config2AR < 2 then GPR[rt] ← temp` is read as the
      unconditional write ("Config2" has no AR field). (b) The L-format pages (CEIL.L p.127, CVT.L p.154,
      FLOOR.L p.185, ROUND.L p.341, TRUNC.L p.440) print the invalid-operation default as "-2^63-1"; read as
      Vol I Table 6.3 `0x8000_0000_0000_0000` (p.82). `CVT.W.fmt` p.160 prints "2^63-1"/"-2^63-1" for its word
      result (its range check says -2^31..2^31-1); read as the Table 6.3 word values, like CEIL.W p.128,
      FLOOR.W p.186, ROUND.W p.342, TRUNC.W p.441. (c) MADDF/MSUBF pseudocode (p.260) uses `vfr` and prints two
      `MADDF.fmt:` lines; read as `ft` and MSUBF (Description p.259 `FPR[fd] ± (FPR[fs] × FPR[ft])`).
    - **`RECIP`/`RSQRT`** accuracy and rounding-mode dependence are implementation-dependent (Vol II p.336,
      p.343): pinned to the correctly rounded `1.0 / x` (`DIV`) and `SQRT` then `DIV`. In the spec they are
      `Impl.recipS/D`, `Impl.rsqrtS/D` (§11.1); `modelImpl_recipAccurate` proves 0 ULP.
    - **UNPREDICTABLE operand register cases** (an odd register for a double) no longer exist: with `FR = 1`
      every register holds a double.
14. **MARS floating-point divergences** (the architecture wins). MARS 4.5 has no FCSR, no FP exceptions, one
    condition flag per `cc` but no flags or rounding modes, a 32-bit FPU where a double occupies an even/odd
    pair, and its `cvt.w.s` truncates (a Java `(int)` cast) where the model follows `FCSR.RM` (round to nearest
    even at reset). Corpus programs read doubles through memory (`sdc1` then `lw`, `fp_double`), use `trunc.w.s`
    or integral inputs for word conversions, and avoid NaNs and flags, so they agree under both models.
15. **Assembler notes.** `break c[, d]` follows GNU as (`c` in bits 25..16, `d` in bits 15..6 of the manual's
    20-bit `code`, Vol II BREAK p.109); MARS puts a single operand in bits 25..6. `.set noreorder`, `.set noat`,
    `.set at` are accepted; `.set reorder` is rejected (the assembler never fills delay slots). **`SSNOP` is
    rejected**: "Assemblers targeting specifically Release 6 should reject the SSNOP instruction with an error"
    (Vol II SSNOP p.387); the word `0x0000_0040` still decodes as `sll` (executes as a NOP). `EHB`, `NOP`,
    `PAUSE`, `NAL` assemble. The R6 reversed-operand idioms `bgtc`, `blec`, `bgtuc`, `bleuc` assemble to
    `bltc`/`bgec`/`bltuc`/`bgeuc` with swapped registers (B<cond>C p.83); `b`/`bal` idioms, `li`, `la` expand
    as in GNU as. `mipsdoc.py` resolves the B<cond>C and `SELNEZ.fmt` spellings.
16. **`PAUSE`, `NAL`, `SIGRIE`.** `NAL` (`REGIMM` rt = 10000, rs = 0; "NAL is considered to be a not-taken
    branch, with a delay slot", Vol II p.306) and `PAUSE` (`SPECIAL`, `sll` funct, shamt 5) are constructors of
    their own (`nal`, `pause`) in R6; a `pause`/`nal` in a delay slot raises Reserved Instruction (item 1).
    **`PAUSE` with `LLbit = 1` enters standby, `EPC ← PC + 4`** (Vol II PAUSE p.317 Operation `if LLBit ≠ 0 then EPC
    ← PC + 4; DescheduleInstructionStream()`; `DescheduleInstructionStream` is undefined; "In a single-threaded
    processor, this may be implemented as a short-term WAIT operation which resumes at the next instruction when
    the LLBit is zero or on some other external event such as an interrupt"): the model reads it as a
    WAIT-like standby that only an interrupt or reset ends, since nothing else on one hart can clear `LLbit`.
    With `LLbit = 0` it is a NOP (`r6_reencoded_forms`).
17. Retired (Release 2: `mul` left `HI`/`LO` unchanged; Release 6 has no `HI`/`LO`).
18. **`BAL`/B*ZALC with source 31, and `JALR` with `rs = rd`.** B{LE,GE,GT,LT,EQ,NE}ZALC (Vol II p.78):
    "Branch-and-link Restartability: GPR 31 must not be used for the source registers ... The result of
    executing such an instruction is UNPREDICTABLE"; the Operation writes `GPR[31] ← PC+4` before the compare
    (`Oracle.linkSourceIs31 = .proceed`: the link is written, then compared). JALR (p.196): "Register
    specifiers rs and rd must not be equal ... UNPREDICTABLE" (`Oracle.jalrRsIsRd = .proceed`): the target is
    read from `rs` before `rd` is written, so `jalr $t0, $t0` jumps to the old `$t0`.
19. **`jalr` hint (R6).** `JR` is `JALR` with `rd = 0` (no `jr` constructor). The 5-bit hint (bits 10..6):
    "In Release 1 of the architecture, the only defined hint field value is 0" and "In Release 2 ... bit 10 of
    the hint field is used to encode a hazard barrier" (Vol II JALR p.196; JALR.HB p.198). `decode` maps hint 0
    to `jalr`, hint `10000` to `jalrHb` (no hazard state, `ClearHazards()` is vacuous), every other hint to
    Reserved Instruction (an UNPREDICTABLE encoding, item 11).
20. **Hosted service 4 scans at most `printStringFuel` bytes.** `printStringFuel = 65536` (`Env.lean`) keeps the
    hosted step total; it is an environment limit, not an architectural statement (item 9).
21. **`ABS.fmt`/`NEG.fmt` of a NaN.** Retired Release 2 pin (reading A'); see item 13 (non-arithmetic, no
    exception, sign changed). QEMU agrees under `ABS2008 = 1`.
22. **NaN payload narrowing in `cvt.s.d`.** A quiet NaN keeps its sign and its most significant fraction
    bits (low bits dropped); widening (`cvt.d.s`) appends zeros; the fraction MSB is then set, so the result is
    quiet even when narrowing drops every set bit (a signaling NaN signals Invalid). Vol I §6.3.1.5, p.82:
    "Propagation of the diagnostic information requires information contained in a QNaN to be preserved through
    arithmetic operations and floating-point format conversions"; the manual does not say how a payload is
    narrowed, so the truncation rule is a pin (`Format.convertNaN`, `Oracle.cvtQNaNToD/S`; IEEE 754-2019 §6.2.3 p.49
    agrees).
23. **`WAIT` enters standby (D9).** Vol II WAIT p.442: "The WAIT instruction is implemented by stalling the
    pipeline at the completion of the instruction and entering a lower power mode. The pipeline is restarted
    when an external event, such as an interrupt or external request occurs, and execution continues with the
    instruction following the WAIT instruction". The model transcribes the **Release 6 Operation**
    (p.442-443: `interrupt_pending_and_not_masked_out()`, i.e. `Cause.IP & Status.IM`) and records the prose
    difference ("resume operation on arrival of an interrupt even if interrupts are not enabled"): `wait`
    completes (`PC ← PC + 4`) and sets `State.standby` unless a request is already pending and not masked out;
    a standby step executes nothing and only the timer advances (`step_standby_stays`); a pending unmasked
    request restarts the pipeline in one step (`step_standby_restarts`); an enabled one is taken as the
    Interrupt exception with `EPC` = the instruction after the `wait` (`step_standby_interrupt`, p.442). `Count`
    keeps counting ("In Release 6, the encoding of WAIT with bits 24:6 of the opcode set to 0 will never disable
    CP0 Count", p.442); the code field selects nothing ("unimplemented encodings must default to WAIT 0");
    there are no external requests besides interrupts here, so without one the processor stays stopped (legal).
    Reset leaves standby ("The assertion of any reset or NMI must restart the pipeline", p.442). `WAIT` in a
    delay slot is RI (item 1). QEMU agrees on timer-wakes-`wait` (`irq_wait_timer`).
24. **`Cause.CE` is 0 for every exception except Coprocessor Unusable.** Vol III Cause §9.36, p.209: CE is loaded
    by hardware on every exception, but is UNPREDICTABLE except for Coprocessor Unusable; §6.2.3 p.87 "loaded,
    but not defined" (`Oracle.causeCE`, `exceptionEntry_ce`; `ce = 1` for COP1, `2` for COP2). **`BadInstr` /
    `BadInstrP`** (8,1)/(8,2), "Release 6 - Required" (Vol III §9.25 p.179, §9.26 p.181): written by exception
    entry for the exceptions the pages list, not by Interrupts; `BadInstr` with no instruction word (a fetch
    exception) and `BadInstrP` outside a delay slot are UNPREDICTABLE there and pinned to 0
    (`Oracle.badInstrNoWord`, `Oracle.badInstrP`); for a forbidden slot see items 1 and 34. `Config3.BP`/`BI` are
    1 ("Release 6: BadInstrP is always implemented", p.246).
25. **The environment layer is outside the architecture.** `Semantics/Env.lean` holds every convention of the
    model rather than the processor, so `step` reads against the manual without exceptions:
    - **Start state and loader.** The machine starts at the architectural reset state (`resetState`, item 10);
      the hosted environment then applies its **boot convention** (`bootConvention`); `load p` writes the
      assembled image (text, data, `.ktext`, `.kdata`) into `hostedStart` memory at `loadAddr`.
      `MipsRun --reset` loads into `resetState` (`loadAtReset`) and runs from `0xBFC0_0000`: the program supplies
      the boot code (`.ktext 0xBFC00000`). `Specs/Loader.lean`, `Specs/Reset.lean`.
    - **Hosted services** (item 9) and their output buffer (`Hosted.out`).
    - **Stopping conventions.** The hosted run stops before a step when `pc` is word-aligned and outside the
      loaded image: `unhandledException (Cause.ExcCode) EPC BadVAddr` when the machine has just entered the
      general or interrupt vector (`Status.EXL = 1`) with no handler loaded there, `noInstruction pc` otherwise.
      A misaligned `pc` is not a stop (AdEL).
    - `MipsRun --bare` runs with services off; the stopping conventions still apply.
    `hostStep_eq_step`, `runHosted_agrees_with_run` (`Specs/Hosted.lean`).
26. **Memory access has one implementation point.** Every processor access (fetch, load, store) goes through the
    six `readMem*`/`writeMem*` functions of `State.lean`; each takes a virtual address, checks alignment,
    translates it with `translate` (item 27) and indexes `physMem`. The loader and observers (`readCString`,
    `MipsRun`'s JSON) are not the processor.
27. **The MMU is the Fixed Mapping MMU (`Config.MT = 3`, D4).** Vol III Appendix A.1, p.313-317 (still permitted in
    Release 6, Vol I §2.4.2 p.32). `State.lean`:
    - `fixedMappingPA erl va` is Table A.1 (p.313-314): useg/kuseg `VA + 0x4000_0000` with `ERL = 0`, `VA` with
      `ERL = 1` (§4.7 p.31); kseg0 and kseg1 both `VA[28..0]` ("they both map to the low 512MB", A.1.1); kseg2/kseg3
      identity (`kseg1_store_visible_through_kseg0`). Physical `0x2000_0000`-`0x3FFF_FFFF` is reachable only
      through kuseg with `ERL = 1` ("inaccessible when the ERL bit is off", p.314).
    - `translate` is the manual's `AddressTranslation` (Vol II §2.2.2.2.2, Figure 2.17, p.19) with the address-error
      check first ("address error checking is still done before the translation process", A.1.1 p.313): in User
      Mode only useg is legal (Table 4.2 p.30), else AdEL/AdES with `BadVAddr` = the virtual address (§6.2.9
      p.92-93).
    - **No TLB exception can occur** (no TLB; §6.2.10-6.2.14, p.93-96) and **no Bus Error** (pin: every physical
      byte exists; Bus Error is a property of the system, §6.2.16 p.97).
    - `Config1.MMU Size - 1 = 0` (pin: p.237 is silent for `MT = 3`). `K23`/`KU` are R/W (Table 9.64 p.233
      "Optional", Table A.2 p.317 "Required"); both are accepted, no effect.
    - **Fetch from kuseg with `ERL = 1`** is UNDEFINED ("The operation of the processor is UNDEFINED if the ERL
      bit is set while the processor is executing instructions from kuseg", A.1.2 p.316). Pin: translated like
      data (identity); it neither halts nor hangs (Vol II §1.2.2, p.4).
    - **Manual inconsistency:** Figure A.2 (p.316) draws kseg1's arrow to the unmapped block
      `0x8000_0000`-`0xBFFF_FFFF`, while Table A.1 (p.313) and the A.1.1 text map kseg1 to the low 512 MB for
      either `ERL`. The model follows the table and the text.
    - `PREF`/`PREFX` never take address exceptions (PREF p.321). QEMU's 24Kf/R6 has a TLB, so the kuseg
      `+ 0x4000_0000` offset is not observable there; kseg0/kseg1 aliasing, the `ERL = 1` kuseg identity and the
      User-Mode Address Errors are, and agree (`tests/oracle/mmu_*`).
28. **Timer and hardware registers.** `step s = timerTick (stepCore s)` (`Step.lean`).
    - **Count rate (pin).** "The Count register acts as a timer, incrementing at a constant rate, whether or not
      an instruction is executed ... The rate at which the counter increments is implementation-dependent"
      (Vol III §9.27, p.183). `Count` += 1 on **every `step`**, modulo 2^32 (`step_count_advances`); one step is
      the model's cycle, so `CCRes` (`rdhwr` 3, Vol II RDHWR p.332) reads 1. QEMU's Count follows virtual time
      and its `CCRes` is 2: not comparable (oracle tests freeze `Count` with `DC = 1` or compare only flags).
    - **`Cause.DC = 1`** ("Disable counting of Count register", Table 9.52 p.210): `Count` stops
      (`step_count_stopped`); the match test is still made.
    - **Order within a step (pin).** The instruction reads the `Count` the step started with; the timer then
      advances it. `mtc0 $9` with `v` leaves `Count = v + 1` (or `v` with `DC = 1`) (`mtc0_count_spec`).
    - **Timer interrupt request.** "When the value of the Count register equals the value of the Compare
      register, an interrupt request is made ... visible to software via the CauseTI bit" (§9.30, p.187): after
      every step `Count = Compare` implies `Cause.TI = 1` (`step_timer_match_sets_ti`); a write of `Compare`
      clears it ("as a side effect, clears the timer interrupt", p.187; `mtc0_compare_clears_ti`). `TI` is its own
      field (`State.cp0TimerInt`), read-only for `mtc0 $13`.
    - **IP7 (pin of `IntCtl.IPTI = 7`).** `IntCtl.IPTI` "specifies the IP number to which the Timer Interrupt
      request is merged" (§9.33, Table 9.48, p.199); the model merges it into `IP7` (`causeValue`). QEMU 24Kf/R6
      reads `IntCtl` the same (`irq_timer`).
    - **The hosted services do not advance the timer** (item 25).
    - **Reset values:** `Count`, `Compare`, `Cause.TI` "Undefined" (Tables 9.44 p.183, 9.46 p.187, 9.52 p.209) and
      not in the Reset Operation: kept by Reset, 0 at power-on. `HWREna ← 0` (§6.2.5, p.89).
    - **`HWREna`** (7,0; §9.23, Table 9.39, p.175): bits 0, 1, 2, 3, 5, 29 are R/W (`hwrenaWriteMask = 0x2000_002F`),
      all others "return a zero and are ignored on a write" (`hwrena_write_masked`).
    - **`RDHWR`** (Vol II p.332-334): 0 `CPUNum` = 0, 1 `SYNCI_Step` = 0 ("zero if no caches need be
      synchronized"), 2 `CC` = `Count`, 3 `CCRes` = 1, **5 `XNP` = `Config5.XNP` = 1** ("Required (Release 6)",
      Vol III Table 9.40 p.176; D13), **29 `ULR` = `UserLocal`** ("In Release 6, the UserLocal register is
      required"). Access "is enabled if Coprocessor 0 is enabled, or if the corresponding bit is set in HWREna.
      If access is not allowed or the register is not implemented, a Reserved Instruction Exception is signaled"
      (p.333): Kernel Mode or the `HWREna` bit, else RI (never CpU). Register 4 (`PerfCnt`, "Required if any
      PerfCnt register is implemented"), 6..28, 30, 31: RI. **`sel`** (Release 6): "when the 3-bit sel is
      undefined for use with a specific register number, then a Reserved Instruction Exception is signaled"
      (p.333): only `sel = 0` is defined here (`rdhwr_reserved_unimplemented`, `rdhwr_reserved_sel`). QEMU
      ignores `sel` (`r6_reencoded_forms`, §10.1).
29. **Interrupts, `IntCtl`, shadow set 0.**
    - **Mode.** Interrupt compatibility mode only (Vol III §6.1.1 p.72); `Config3.VInt = VEIC = 0`.
    - **When.** Request `i` = `Cause.IPi AND Status.IMi` (Table 6.2 p.73); taken when `IE = 1`, `EXL = ERL = 0`
      (§6.1 p.72; no EJTAG `DM`). `interruptTaken_iff`.
    - **Priority / place.** Checked at the start of `step`, before the fetch: Interrupt is above every
      instruction exception (Table 6.6 p.83-84; asynchronous exceptions are "the highest priority relative to
      the next instruction", Table 6.7 p.84). The instruction at `pc` is not executed (`step_interrupt`).
    - **Entry.** General exception processing (§6.2.3, p.86-88), `ExcCode = Int` (0, Table 9.53 p.212): `EPC` = the
      instruction not executed, or the branch with `Cause.BD = 1` in a delay or forbidden slot (Table 6.11 p.87;
      §9.38 p.217); the pending branch is abandoned, so `eret` re-executes the branch
      (`takeInterrupt_in_delay_slot`, `takeInterrupt_not_in_delay_slot`). `Cause.IP` is not latched (§6.2.26
      p.102).
    - **Vector.** `Cause.IV = 0`: offset `0x180`; `IV = 1`: `0x200` (§6.2.3 Operation p.88; Table 6.10 p.86);
      conforming text, not a pin (Table 6.1 p.72, §6.1.1.1 p.73).
    - **Sources.** Software `IP1..IP0` (`mtc0_cause_requests_software_interrupt`), the timer (item 28) and the six
      hardware lines `HW5..HW0` (`State.hwInt`, `IP7..IP2`), which are inputs `step` reads and never writes
      (`step_hwInt`, `hwInt_requests_interrupt`). The environment connects no device: `hwInt = 0` always. (QEMU's
      Malta raises HW0 by itself; the oracle tests keep `IM2 = 0` and mask `IP7..IP2`.)
    - **Hazards (pin).** `EHB` after a `Status`/`Cause` change "makes the change to the interrupt state visible
      no later than the instruction following the EHB" (§6.1.2.1, Table 6.5 p.82); the model makes it visible
      at once. QEMU takes the interrupt at the same place (`irq_software`).
    - **`IntCtl`** (12,1) = `0xE000_0000` (Table 9.48 p.199-201): `IPTI = 7`, `IPPCI = 0`, `IPFDC = 0`, `VS = 0`
      ("ignored on write and reads as zero" without VI/EIC, p.201); read-only.
    - **`SRSCtl`** (12,2) = 0 (Table 9.49 p.203-204): `HSS = 0` ("only the normal GPRs are implemented"); `mtc0`
      is ignored (pin: `ESS`/`PSS` can only hold 0, since UNDEFINED above `HSS`). `SRSMap` is not implemented
      (required only with additional shadow sets, §9.35 p.207); `mfc0` of it reads 0 and `mtc0` is ignored (layout table, §2).
    - **`RDPGPR`/`WRPGPR`** (Vol II p.335, p.444): shadow set 0 = the normal GPRs ("The normal GPRs are logically
      considered shadow set zero", Vol III ch.7 p.103), `PSS = 0`, so both are `$rd ← $rt` (`rdpgpr_wrpgpr`).
    - **Theorem statements.** Every per-instruction theorem `step s = timerTick (...)` assumes
      `hexec : executesInstr s = true` (no interrupt is taken, not in standby); the global theorems do not.
30. **Signs of exact zero results (a pin where the manuals are silent).** The manuals do not give the sign of an
    exactly zero sum, difference, product or quotient, nor of `CVT.S.W`/`CVT.D.W` of 0. Vol I §6.2 (p.77,
    footnote 1) names IEEE 754-1985, whose text is not available here; the model and the reference
    (`FpOpsSpec.lean`: `AddSpec`, `MulSpec`, `DivSpec`, `FromIntSpec`) follow the rules verified against the
    owner's local copy of **IEEE Std 754-2019** (`manuals/LOCAL-SOURCES.md`; `mipsdoc.py section ieee 6.3`),
    §6.3 p.50: the sign of a product or quotient is the exclusive OR of the operand signs; an exact zero sum
    (or difference) of opposite effective signs is `+0` except `-0` under `roundTowardNegative`
    (`FCSR.RM = 3`), and `x + x`, `x - (-x)` keep the sign of `x`; `squareRoot(-0) = -0` (also Vol II SQRT.fmt p.382:
    "If the value in FPR fs corresponds to - 0, the result is - 0"); §5.4.1 p.33: "Integer zeros without signs are
    converted to +0". Only "verified against 2019": no claim that the rules are unchanged since 1985. The same
    rule covers `MADDF`/`MSUBF` (an exact zero fused result) and `RINT` (the zero's sign is kept, 754 §5.9).
    Proved for every operand: `Trusted.f32Add_spec` ... `Trusted.w32ToF32_spec`.

    **Verification against IEEE Std 754-2019** (printed pages; each row looked up with `mipsdoc.py section ieee X`;
    "agrees" = the proved spec in `FpOpsSpec.lean` and the model behave as the clause says):

    | Pin / definition | 754-2019 clause, page | Result |
    |---|---|---|
    | exact-zero sum/difference sign | §6.3, p.50 | agrees (`AddSpec`) |
    | zero product / quotient sign = XOR | §6.3, p.50; §7.3 p.53 | agrees (`MulSpec`, `DivSpec`) |
    | `SQRT(-0) = -0`, other roots positive | §6.3, p.50 | agrees (`SqrtSpec`; Vol II p.382) |
    | integer 0 to `+0` | §5.4.1, p.33 | agrees (`FromIntSpec`) |
    | correct rounding RN/RZ/RP/RM, ties to even | §4.3 p.27-28 | agrees (`CorrectlyRounded`) |
    | overflow default results and flags | §7.4, p.53 | agrees (`overflowResult`) |
    | underflow: tiny non-zero result, flag only if inexact (untrapped) | §7.5, p.53 | agrees; with the Underflow enable MIPS signals on tininess alone (the trap case) |
    | tininess detected after rounding (Vol I §6.7.2.3 p.101) | §7.5 a), p.53 | agrees (`RoundSpec.tiny`); `FS = 1` flushing detects it before rounding (§6.7.2.4 p.102), a MIPS non-IEEE mode |
    | Inexact when the rounded result differs from the unbounded one | §7.6, p.54 | agrees |
    | Invalid: SNaN operand, 0 x inf, inf - inf, 0/0, inf/inf, sqrt of a negative | §7.2, p.52 | agrees |
    | Division by zero: finite non-zero / 0 to signed inf | §7.3, p.53 | agrees (`DivSpec`) |
    | float to integer: Invalid for NaN, inf, out of range; Inexact if rounded | §5.8 p.39-40, §7.2 j) p.52 | agrees (`ToWordSpec`); the value `0x7FFF_FFFF` is the MIPS rule |
    | comparisons: unordered, `+0 = -0`, SNaN signals Invalid | §5.11 p.43; §7.2 i) k) p.52 | agrees (`CompareSpec`) |
    | NaN: Invalid result is quiet; quiet inputs signal nothing; payload kept | §6.2 p.48; §6.2.3 p.49 | agrees (`NaNResult`); which input supplies the payload is unspecified by both (item 13) |
    | conversion keeps the sign of `+-0`, `+-inf`; payload narrowing | §6.3 p.50; §6.2.3 p.49 | agrees (`ConvertSpec`; item 22) |
    | `ABS`/`NEG` quiet for NaN | §5.5.1, p.35 | agrees under `ABS2008 = 1` (R6); the legacy arithmetic form is not in the profile |
    | NaN encoding: quiet = fraction MSB 1 | §6.2.1 p.48 | agrees (`NAN2008 = 1` is the 754-2008 preferred encoding) |
    | fused multiply-add: single rounding | §5.4.1 fusedMultiplyAdd, §6.3 p.50, §7.2 c) p.52 | applies to `MADDF`/`MSUBF` (`FmaSpec`; MADDF "0 x inf + QNaN fd" is Invalid with fd's QNaN, p.100, 754 §7.2 c) p.52) |
31. **Release 6 FPU instruction pins.**
    - `CMP.condn.fmt`: `condn` 0-15, 17-19, 25-27 are defined, every other value is Reserved Instruction (Vol II
      p.136: "All encodings of the condn field that are not specified ... are reserved in Release 6 and produce a
      Reserved Instruction exception"; Table A.17 p.457). The result is all-ones/all-zeros; flushing without
      Inexact (item 13).
    - `MIN`/`MAX`/`MINA`/`MAXA` funct codes `0x1c`-`0x1f` come from the instruction diagrams (p.262: MIN 011100, MINA
      011101, MAX 011110, MAXA 011111), not from Table A.15 (p.456, which lists MIN, MAX, MINA, MAXA at 4-7); LLVM
      and QEMU agree with the diagrams. A NaN operand: "if one input is a NaN, but not both, the value of the
      numeric input is returned. If both are NaNs, the NaN in fs is returned" (p.263); an SNaN is "treated as if
      the SNaN were a QNaN (do not quieten the result)" (Table 4.1 p.265) and still signals Invalid. QEMU follows
      IEEE minNum/maxNum instead (`fp_r6_max_min_snan`, §10.1).
    - `MADDF`/`MSUBF`: fused, single rounding, NaN order `[fd, fs, ft]`; pseudocode erratum (item 13). `RINT`
      keeps the zero's sign. `CLASS` and `SEL`/`SELEQZ`/`SELNEZ` leave `FCSR` untouched (Vol II p.132, 368, 371).
      `.S` operations leave the upper half of the register as it was (`fprUpper`).
    - `BC1EQZ`/`BC1NEZ` offset: "A 18-bit signed offset (the 16-bit offset field shifted left 2 bits)" (p.54);
      the Operation `sign_extend(offset << 2)` (p.55) is read as 18-bit, as for BOVC/BNVC (item 32).
32. **Compact branch and jump pins.**
    - **`target_offset` (D11).** The Operation of B<cond>C on p.84 writes `PC+4+sign_extend(offset)` where the
      surrounding text and the encoding define `target_offset` (p.83: "An 18/23-bit signed offset (the 16/21-bit
      offset field shifted left 2 bits)"; B*ZALC p.78 `PC+4+sign_extend(target_offset)`); the model uses
      `target_offset`.
    - **`BOVC`/`BNVC`** `sign_extend(offset << 2)` is read as 18-bit (p.107-108). The special case `rs = rt = 0`
      "is allowed. BOVC never branches, while BNVC always branches" and neither links (p.107; Table A.26 p.464:
      POP10/POP30 with `0rs 0rt`); **QEMU links `$31`**: declared deviation `bovc_zero_zero`.
    - B*ZALC with `rt = 31`: item 18. Taken compact branches have no slot; not-taken conditional ones have the
      forbidden slot (item 1).
33. **Privileged and absent-module pins (Wave R6-2, R6-7).** `CACHE` with no caches: "UNDEFINED for any
    operation/cache combination that is not implemented. In Release 6, the instruction in this case should
    perform no operation" (Vol II CACHE p.119; D8). `TLB*` instructions: RI under the Fixed Mapping MMU (Vol III
    §A.1.3 p.317; TLBINV p.423). `DERET`, `SDBBP`: EJTAG not implemented, "the EJTAG instructions (SDBBP and
    DERET) can be subsetted out" (Vol I §2.4.1, p.31); the words are undecodable, so RI (D7; with EJTAG,
    `SDBBP` page p.361 would signal RI when `Config5.SBRI = 1`, which is stored and read back here with no other
    effect, Vol III Table 9.69 p.263). **`DVP`/`EVP`** are NOPs in Kernel Mode (`Config5.VP = 0`; item 10).
    **`Config5.CRCP`/`GI`** are absent from the Vol III table (`mipsdoc.py search CRCP` finds no match), so
    the model reports 0 (D10); `LLWP`/`SCWP` are absent and `Config5.XNP = 1` ("LLX/SCX instruction family not
    supported", p.261; LLWP p.228, SCWP p.355: "only present if Config5XNP=0"; D13). `Config3` has `BP`, `BI`,
    `ULRI`, `RXI` set (p.245-248; `RXI = 1` although `PageGrain` is absent, a pin, p.248); `Config4.KScrExist = 0xFC`
    ("For Release 6, bits 2-7 are always 1 because KScratch1-6 must be implemented", p.255).
34. **Where the spec relation is looser or stricter than the manual (reported, not changed).**
    - **Looser: `storeClearsLL` / `loadClearsLL`.** With `Config5.LLB = 1` a store to the LL'd block MUST make
      `SC` fail and a load must not (Vol II SC p.347-348; Vol III Table 9.69 p.264). `modelOracle` has the
      constants `true`/`false`, correct for every address. But the oracle fields take no address argument, so
      `Manual.Step` also admits oracles an R6 core may not: `storeClearsLL = false` for a same-block store, or
      `loadClearsLL = true` for a same-block load. The model is unaffected. Tightening needs the
      implementation-dependent block size in `Impl`.
    - **Stricter: `BadInstrP` in a forbidden slot.** For a slot of a compact branch, Vol III §9.26 (p.181) speaks
      only of "a branch delay slot" ("not in a branch delay slot ... UNPREDICTABLE" otherwise), and Vol I
      §5.3.2.2 (p.62) treats the forbidden slot like a delay slot for EPC/BD. `Manual.GeneralExceptionProcessing`
      fixes `BadInstrP` = the compact branch word (D6 extension) instead of consulting `Oracle.badInstrP`; the
      value is a permitted one, but the spec is stricter than the manual there.
    - **Stricter: UNPREDICTABLE limits.** An UNPREDICTABLE or UNDEFINED outcome leaves the hardware interrupt
      inputs `HW` unchanged (`Manual.UnpredictableLimits`; the inputs are read through read-only
      `Cause.IP7..IP2`, Vol III §6.1.1.1 Table 6.2 p.73, §9.36 p.209, so no instruction writes them).
35. **`SYNC`, `PREF`, trap codes (pins and readings).** `PREF` "does not cause
    addressing-related exceptions ... the exception condition is ignored" and "Any action, including doing
    nothing, is permitted" (Vol II PREF p.321): a no-op; the Release 6 reserved hints 24..31 raise Reserved
    Instruction. `SYNC` "has the same effect as a NOP" on a strongly ordered system (SYNC p.410). The trap `code`
    field is "available for use as software parameters" and ignored (TEQ p.416; BREAK p.109).

## 10. Oracle deviations (the manual wins)

### 10.1 QEMU (`qemu-system-mipsel -cpu mips32r6-generic`)

Every `# oracle: expect-deviation` line in `tests/oracle/*.asm` (119 lines in 20 programs at 63e01a2; no
`known-model-bug`) is a place where QEMU differs from the manual and the model follows the manual. The
oracle fails on an undeclared mismatch and on a declared deviation that no longer occurs. Citations are those
in the directives (documents as in §9); each page was re-checked with `mipsdoc.py`.

| Test | Where QEMU differs | Manual |
|---|---|---|
| `bovc_zero_zero` | links `$31` for `bovc $0,$0` (model: no link) | Vol II BOVC/BNVC p.107; Table A.26 p.464 |
| `cp0_lladdr` | the software-visible `LLAddr.LLB` bit (3 fields) | Vol III Table 9.72 p.270; Table 9.69 p.264; Vol II SC p.347 |
| `exc_sc_misaligned` | a misaligned `sc` does not take Address Error (6 fields) | Vol II SC p.349: "If either of the 2 least-significant bits of the address is non-zero, an Address Error exception occurs"; "Providing misaligned support for Release 6 is not a requirement for this instruction" |
| `exc_delay_slot_never_taken_branch` | exception (`break`, `teq`, misaligned `sh`) in the delay slot of a never-taken `bne r,r`, `bgtz $zero`...: QEMU reports `BD = 0`, EPC = the slot (8 fields); dynamically not-taken controls agree | Vol III §9.36 p.209 (BD), §9.38 p.217 (EPC); Vol I App. B.2 p.128 |
| `fp_cfc1_ri_fs1`..`fs4` | no Reserved Instruction for `cfc1` with fs 1-4 | Vol II CFC1 p.129-130 ("Release 6 traps") |
| `fp_ctc1_ri_fs1`, `fs4` | no RI for `ctc1` fs 1, 4 | Vol II CTC1 p.149 ("Release 6 traps") |
| `fp_ctc1_ri_fs5`, `fs6` | no RI for `ctc1` fs 5, 6 (rt ≠ 0) | Vol II CTC1 p.149 ("Release 6 implementations and later are required to produce a Reserved Instruction exception") |
| `fp_flush_to_zero_fs` | with `FCSR.FS = 1` a flushed tiny result leaves Underflow/Inexact clear (10 fields) | Vol I §6.7.2.4 p.102; Table 6.8 `FS` p.93 |
| `fp_fs_flush_input_inexact` | no Inexact for an input subnormal flush (7 fields) | Vol I §6.7.2.4 p.102; Table 6.8 p.93; MADDF p.260 |
| `fp_r6_max_min_snan` | MAX/MIN/MAXA/MINA with an SNaN: QEMU follows IEEE minNum/maxNum (quieted NaN) (46 fields) | Vol II MAX/MIN p.263, Table 4.1 p.265 |
| `fp_trap_enabled_handler` | with the Overflow enable set QEMU also sets `Cause.I` | Vol I §6.7.2.6 p.102 ("without an overflow trap"; the more specific clause); §6.7.2 p.99 |
| `fp_underflow_enabled_exact` | with `Enables.U`, an exact tiny product does not trap in QEMU (6 fields) | Vol I §6.7.2.3 p.101 |
| `r6_reencoded_forms` | `rdhwr $2` with `sel = 1`: QEMU ignores `sel` and returns `Count` (4 fields) | Vol II RDHWR p.333 |
| `r6gap_absent_modules` | COP2-space words raise RI in QEMU, Coprocessor Unusable `CE = 2` in the model (5 fields) | Vol III §6.2.22 p.100 |
| `rdhwr_kernel` | `rdhwr 4` (`PerfCnt`) returns a value (2 fields) | Vol II RDHWR p.333; Vol III Table 9.40 p.176 |

**Declared `unpredictable` fields (not deviations; 91 lines in 22 programs):** misaligned `LH`, `LW`, `SH`, `SW`,
`LWC1`, `SWC1`, `LDC1`, `SDC1` (46 lines; "Release 6 allows hardware to provide address misalignment support in lieu of
requiring natural alignment" on each page, Vol II LDC1 p.215, LH p.219, LW p.235, LWC1 p.236, SDC1 p.362, SH
p.373, SW p.392, SWC1 p.393; Vol I App. B.2 p.128); the TLB-register reads and TLB instructions (MMU type is an
implementation choice, Vol I §2.4.2 p.32; Vol III §A.1.3 p.317); `SC` without `LL` (p.348); Config/PRId/FIR/K0
reset values (Vol III Tables 9.57 p.221, 9.64 p.233-235, 9.65 p.237-240; Vol I Table 6.5 p.88-89; `Config1.MSAP`,
`Config3.ISA`, `Config4.IE`); which NaN is returned for two NaN operands (Vol I §6.3.1.5 p.82: "When possible,
this QNaN result is one of the operand QNaN values"); `RECIP`/`RSQRT` accuracy (Vol II RECIP.fmt p.336, RSQRT.fmt
p.343); `rdhwr` `SYNCI_Step`, `CCRes`, `PerfCnt` (QEMU 32, 2; model 0, 1; Vol III Table 9.40 p.176); `Cause.IP` lines in
`timer_count_compare` (the Malta board raises HW0); `HI`/`LO` no longer exist. The directive `cti_in_delay_slot_reserved`
formerly declared six `unpredictable` fields on a pre-R6 reading; Release 6 mandates RI (Vol II BEQ p.72, JALR
p.196; Vol I §5.3.2.1 p.62), so they were removed and every field is now compared (QEMU agrees).

**Probe findings (scratch runs outside the tree, Wave R6-7).** (1) `div/mod/divu/modu rd, rs, $zero`: model and QEMU
agree (item 2). (2) `cfc1 $s0, $5` (`FRE`): the model, now, and QEMU both signal Reserved Instruction (QEMU Cause
`0x28`, `$s0` left as it was); before the change the model read 0. QEMU reported EPC 0x400000, 0x400004, 0x400008 for
three consecutive such words, i.e. its EPC for this RI looked wrong too; not investigated. (3) Citation fixes
(16 directive/choice citations re-audited, e.g. SC "Config5LLB" wording, CFC1/CTC1 page numbers, RECIP/RSQRT flag
wording) are in `git log` for Wave R6-7.

**Possible future work.** Emulator-compatibility toggles (a mode that reproduces QEMU's or MARS's behaviour for
these cases) could be added later; none exist, and the default is always the manual.

### 10.2 MARS 4.5 (corpus programs only)

MARS cannot run Release 6 and is only a differential oracle for the 29 `tests/corpus/*.asm` programs (gate
step 5: the pass count must equal the number of programs). The programs use only instructions that mean the same
in both (`li`, `move`, ALU, shifts, `lw`/`sw`/`lb`/`lh`, `ll`/`sc` at offset 0, `clz`/`clo`, traps, branches with a
filled slot, `syscall` 1/4/10/11, single/double FP through `mtc1`/`sdc1`/`lw`); they avoid every instruction
removed in R6 (HI/LO, branch-likely, `movz`/`movn`, `lwl`/`lwr`, `madd`, `c.cond`; `lui` is `AUI` with `rs = 0`). The
divergences that still apply:

| Aspect | MARS | Model | Effect on the corpus |
|---|---|---|---|
| delay slots | none by default (`DelayedBranching = false`) | one, always executed (item 1) | every branch/jump is followed by a real `nop` (`sll $0,$0,0`), harmless in both |
| `jal` `$ra` | `pc + 4` | `pc + 8` (item 5) | `$ra` is never probed by value |
| `lw`/`sw` offset | raw 16 bits (bug) | sign-extended (item 3) | assembler-built programs agree |
| byte order | little-endian | little-endian (§7) | none; tests stay endian-invariant |
| FP | 32-bit FPU, no FCSR, `cvt.w.s` truncates | 64-bit FPU, FCSR, RM (items 13, 14) | doubles read through memory; integral inputs or `trunc.w.s` |
| unknown/failing runs | prints `Error in ...` | System Call or other unhandled exception | harness treats both as the same verdict (item 9) |
| decoder | lax on reserved fields | strict, RI (item 11) | corpus uses defined encodings only |
| `break` operand | single operand in bits 25..6 | GNU as: `c` in 25..16, `d` in 15..6 (item 15) | `break` without operands |

## 11. The manual spec's implementation constants and choices (`Manual.modelImpl`, `Manual.modelOracle`)

The independent spec (`Semantics/Manual/`, `docs/MANUAL-SPEC.md`) takes the implementation's constants (`Impl`)
and one resolution of every manual choice (`Oracle`) as arguments; `Manual.Step` quantifies over all
oracles. The model's values (`Semantics/Manual/Choices.lean`) are the spec-side statement of the pins above.

### 11.1 `Impl` constants (`modelImpl`)

| Field | Model's value | Manual text and page | Pin |
|---|---|---|---|
| `Exception` names | the `SignalException` argument | Vol II §2.2.2.5.1 p.26; Vol III §6.2.9 p.92-93, §6.2.22 p.100 | |
| `CountIncrement` | 1 per instruction time | "The rate at which the counter increments is implementation-dependent" (Vol III §9.27 p.183) | item 28 |
| `PRId` | `0x0001_0000` | Vol III §9.40 Table 9.57 p.221 (all fields "Preset by hardware") | implementation constant |
| `ConfigFixed` | `0x8000_0980` (`M` = 1, `BE` = 0, `AT` = 0, `AR` = 2, `MT` = 3) | Table 9.64 p.233-235: BE "0 Little endian" p.234, AR "2 Release 6" p.234, MT "3 Fixed Mapping" p.235 | D1, D4 |
| `Config1` | `0x8000_0001` (`M` = 1, `FP` = 1; no TLB, caches, PC, WR, CA, EP) | Table 9.65 p.237-240; M: "If the Config2 register is implemented, this bit should read as a 1" p.237 | |
| `Config2` | `0x8000_0000` | Table 9.66 p.241-243; M p.241; TU/SU "read as zero and be ignored on write" p.241-242; SL/TL "No cache present" p.242-243 | Config2 present because `Config5.L2C = 0` (Table 9.69 p.261) |
| `Config3` | `0x8C00_3000` (`M`, `BP`, `BI`, `ULRI`, `RXI`) | §9.48 p.245-248: "Release 6: BadInstrP is always implemented." / "Release 6: BadInstr is always implemented." p.246; ULRI, RXI p.248; "All fields in the Config3 register are read-only" p.245 | RXI without `PageGrain` (p.248) |
| `Config4` | `0x80FC_0000` (`M` = 1, `KScrExist` = 0xFC, `IE` = 0) | Table 9.68 p.253-258; KScrExist p.255 | item 10 (IE note) |
| `Config5Fixed` | `0x0000_2010` (`XNP` = 1, `LLB` = 1, `DEC` = 0, `L2C` = 0, `M` = 0; `SBRI` R/W) | Table 9.69 p.259-264: XNP p.261, DEC p.261, L2C p.261, M p.260, LLB p.264, SBRI p.263 | D1, D13 |
| `CCASupported` | `{2, 3}` | "For Release 6, writes of unsupported values are ignored" (Table 9.64 p.233, 235); Table 9.12 p.133 | item 10 |
| `IntCtl` | `0xE000_0000` (`IPTI` = 7, `VS` = 0) | Vol III §9.33 Table 9.48 p.199-201 | item 29 |
| `SRSCtl` | 0 (`HSS` = `PSS` = 0) | Table 9.49 p.203-204; "The normal GPRs are logically considered shadow set zero" (ch.7 p.103) | item 29 |
| `CCRes`, `SYNCIStep` | 1, 0 | Vol II RDHWR Table 5.4 p.332 ("or zero if no caches need be synchronized"); Vol III Table 9.40 p.176 | item 28 |
| `SynciAddressError` | false | "It is implementation dependent whether such an exception does occur" (Vol II SYNCI p.412) | item 6 |
| `FIR` | `0x00F3_0000` | Vol I §6.5.1 p.87, Table 6.5 p.88-90: Has2008 "1 (Release 6)" p.88; F64 "In Release 6, StatusFR is read-only 1" p.89; UFRP/3D/PS "R0 (Release 6)" p.88-89; FREP "Optional" p.88 | item 13 |
| `recipS/D` | correctly rounded `1.0 / fs` | Vol II RECIP.fmt p.336 (accuracy implementation-dependent, 1 ULP) | item 13; `modelImpl_recipAccurate` |
| `rsqrtS/D` | `SQRT` then `DIV` (flags ORed) | Vol II RSQRT.fmt p.343 ("no more than two units"; rounding-mode effect implementation dependent) | item 13 |
| `WF` | `modelImpl_WF` | `SRSCtl.HSS = PSS = 0`; `IntCtl.VS = 0` without VI/EIC (Table 9.48 p.201) | no shadow sets, no vectored interrupts |

The RECIP/RSQRT Invalid/Division-by-Zero conditions are constrained by operand class (`Impl.RecipFlags`; Vol I
§6.3.1.5 p.82, §6.3.1.4 p.81, §6.7.2.2 p.100, §6.7.2.1 p.100), a flushed subnormal input (FS = 1) excepted
(§6.7.2.4 p.102: `RecipFlagsOK` clause 4, Wave R6-7: divZero = true, invalid = false); Overflow, Underflow,
Inexact are left free (`modelImpl_valid`).

### 11.2 `Oracle` choice points (`modelOracle`)

| Field | Model's value | Manual text and page |
|---|---|---|
| `storeClearsLL` | true | Vol II SC p.347-348; Vol III Table 9.69 p.264 (item 7, 34) |
| `loadClearsLL` | false | Vol II SC p.347 ("will not cause the SC to fail (if Config5LLB=1 ...)") |
| `causeCE` | 0 | "The CE field is loaded, but not defined, for any exception type other than a coprocessor unusable exception" (Vol III §6.2.3 p.87) |
| `resetUndefined` | keep; `K23 = KU = 2`; `LLbit = 0` | Vol III §6.2.5 p.89; Table 9.64 p.233 (item 10) |
| `jalrRsIsRd` | `.proceed` | Vol II JALR p.196 (item 18) |
| `linkSourceIs31` | `.proceed` (link written, then compared) | Vol II B*ZALC p.78 (item 18) |
| `fprUpper` | upper half unchanged | Vol I §6.6.2 p.98 (item 13) |
| `ctc1Unpredictable` | fs 5/6 RI; reserved FCSR/FCCR/FEXR/FENR bits ignored | Vol II CTC1 p.149-150 (item 13) |
| (removed) `cfc1Unpredictable` | fs 5 is RI, no choice point | Vol II CFC1 p.129-130 (item 13) |
| `extOutOfRange` | Reserved Instruction | "The operation is UNPREDICTABLE if lsb+msbd > 31" (Vol II EXT p.183, image page) |
| `insLsbAboveMsb` | Reserved Instruction | "The operation is UNPREDICTABLE if lsb > msb" (INS p.193) |
| `unpredictableEncoding` | Reserved Instruction (after the coprocessor-usability check of the word's space) | Vol II §2.1.1 p.12; EXT p.183; INS p.193; only two `jalr` hints are defined (JALR p.196, JALR.HB p.198) |
| `ebaseWriteBEV0` | `.proceed` | "The operation of the processor is UNDEFINED if the Exception Base field is written with a different value when StatusBEV is 0" (Vol III §9.41 p.223) |
| `cvtQNaNToD/S` | the core's widening/narrowing of the payload | Vol I §6.3.1.5 p.82 (item 22) |
| `badInstrNoWord` | 0 | Vol III §9.25 p.179 |
| `badInstrP` | 0 outside a delay slot | Vol III §9.26 p.181 |
| `divByZero` | `DIV`/`DIVU` dividend; `MOD`/`MODU` 0 | Vol II p.168-169 (item 2) |

The oracle fields removed in the Release 6 retarget (HI/LO, the PAUSE special case for a CTI in a slot, odd-FPR reads and writes,
the ABS/NEG QNaN reading, the HI/LO multiply result, the unfused multiply-add) are not needed: those cases no longer exist.

### 11.3 Readings of the manual text (misprints and gaps; no model change)

| Reading | Where | Citation and note |
|---|---|---|
| ALIGN `tmp_rt_lo` read as `tmp_rs_lo` | `Manual/Ops/BitOps` | Vol II ALIGN p.39 (image page, read in the PDF): the Operation defines `tmp_rt_hi`, `tmp_rs_lo`, then `tmp ← tmp_rt_hi or tmp_rt_lo`; the Description `GPR[rs] >> (GPRLEN-8*bp)` agrees |
| CFC1 `if Config2AR < 2 then GPR[rt] ← temp` read as unconditional; `ConfigAR ≤ 2` read as `< 2` | `Manual/Ops/FpuControl` | Vol II CFC1 p.129-130 (item 13) |
| `signed_word`/`unsigned_word` undefined | `Manual/Pseudocode` | read as `toInt`/`toNat` (p.168-169) |
| L conversions "-2^63-1"; `CVT.W` "2^63-1" | `Manual/Ops/FpuConvert` | item 13 |
| MADDF/MSUBF `vfr`, two `MADDF.fmt:` lines | `Manual/Ops/FpuR6` | Vol II MADDF p.259-260 (item 13) |
| B<cond>C `target_offset`; BOVC/BNVC 18-bit; BC1EQZ 18-bit | `Manual/Ops/CompactBranch` | p.83-84, p.107-108, p.54-55 (items 31, 32) |
| MIN/MAX funct from the diagrams | decode | p.262 vs Table A.15 p.456 (item 31) |
| CMP `condn` reserved values RI | decode | Vol II p.136; Table A.17 p.457 |
| WSBH: the printed Operation reads `GPR[rs]` | `Manual/Ops/BitOps` | Vol II WSBH p.445: the Description ("Within each halfword of GPR rt") and the diagram (field 25..21 is 0) make the source `GPR[rt]` |
| ROTR/ROTRV test `ArchitectureRevision() < 2` | `Manual/Ops/Shift` | Vol II ROTR p.339 (the `<` glyph is lost by text extraction); with `ArchitectureRevision() = 6` the UNPREDICTABLE branch is never taken |
| EXT/INS `pos`/`size` mapping | encode/`Manual.enc` | Vol II EXT p.183, INS p.192-193: `lsb = pos`, `msbd = size - 1`, `msb = pos + size - 1`, each mod 32; model and spec read the same fields |
| `SLL`/`SRL`/`SRA`/`ROTR` | model fix | `s ← sa` is the 5-bit field; the model shifts by `sa mod 32` (SLL p.376, SRL p.385, SRA p.383, ROTR p.339) |
| `div`, `mod` rounding | `Manual/Ops/MulDiv` | Vol II Table 1.1 p.5 ("2's complement integer division") names no rounding rule; the spec truncates toward zero, remainder with the dividend's sign (`BitVec.sdiv`/`srem`) |
| `SC` and the address | `Manual/Ops/Atomic` | the Operation tests `LLbit` only; the prose (SC p.347) adds the aligned-address check, modeled as `atomic_update = LLbit ∧ vAddr31..2 = LLAddr31..2`; the `SC` itself is not a store "between the execution of LL and SC", so `storeClearsLL` does not apply to it |
| `SYNC`, `PREF`, `SYNCI` | `Manual/Ops/Memory` | item 35 |
| Reset `Status` masked | `Manual/Reset` | the oracle's `Status` is masked with `StatusWritable` before the Operation's assignments (Vol III §6.2.5 p.89-90, Table 9.47 p.189-196) |
| MTC0 of `EBase` with `BEV = 0` | `Manual/Ops/Cp0` | UNDEFINED (Vol III §9.41 p.223): the write takes effect |
| `SWXC1`/`LWXC1`... | removed in R6 | COP1X does not exist; no reading needed |
| Timer placement, `Delay.forbiddenSlot` | `Manual.TimerTick`, `Manual/Ops/CompactBranch` | the timer advances after the instruction of the instruction time (implementation-dependent placement); item 1 |
| `PC` / `NAL` / `PAUSE` | `Manual/Ops/System` | items 1, 16 |

### 11.4 Pins recorded in Wave R6-7 without a spec change

| Pin | Where | Citation |
|---|---|---|
| LL/SC with `Config5.LLB = 1`: same-block store clears `LLbit`, load does not | `Manual/Choices.lean` `storeClearsLL`, `loadClearsLL` | Vol II SC p.347-348; Vol III Table 9.69 p.264. Spec looser than the manual for oracles that do not see the address (item 34) |
| `BadInstrP` for an exception in a compact-branch forbidden slot is the branch word | `Manual/Exceptions.lean` `GeneralExceptionProcessing`; model the same | Vol III §9.26 p.181; Vol I §5.3.2.2 p.62 (D6). Spec stricter (item 34) |
| `SSNOP` rejected by the assembler | `Semantics/Asm` | Vol II SSNOP p.387; the word still decodes as `sll` |
| `DVP`/`EVP` are NOPs with `Config5.VP = 0` (CpU outside Kernel Mode) | `Exec/Cp0.lean`, `Manual/Ops/VP.lean` | Vol II DVP p.172-173, EVP p.181-182; Vol III Table 9.69 p.263. Closed a gap (previously RI) |
| COP2 words: Coprocessor Unusable `CE = 2` | `Step.lean` decode-none path | Vol III §6.2.22 p.100; QEMU raises RI (declared in `r6gap_absent_modules`) |
| Exception entry keeps `LLbit`; `eretnc` does not clear it | `Manual/Exceptions.lean`, `Exec/System.lean` | Vol II SC p.347, p.350; ERETNC p.179 |

## 12. Profile decisions D1-D13 (owner/orchestrator, 2026-11-16)

Each is a choice the manual permits, recorded here as a pin; code comments cite them as "DECISIONS Dn".

| # | Decision | Manual basis |
|---|---|---|
| D1 | **Little-endian only.** `Config5.DEC = 0`, `Config.BE = 0`; one profile constant keeps the byte order switchable. Oracles `qemu-system-mipsel`, `llvm-mc -triple=mipsel` | Vol III Table 9.69 p.261; Vol I p.16 |
| D2 | **FPU present, 64-bit**, `Status.FR = 1` read-only; `FIR.F64 = L = W = D = S = Has2008 = 1`, `PS = 3D = UFRP = 0`; `FCSR.NAN2008 = ABS2008 = 1` read-only; L-format conversions in scope | Vol I §6.5.1 p.88-89, p.92-96 |
| D3 | **Misaligned load/store = Address Error**; LL/SC always. Hardware support was the alternative | Vol I App. B.2 p.128 |
| D4 | **Fixed Mapping MMU**; TLB registers read 0, writes ignored; `TLBWR/WI/P/R` RI; `TLBINV/F` RI with `Config4.IE = 0` | Vol I §2.4.2 p.32; Vol III §A.1.3 p.317; Vol II TLBINV p.423 |
| D5 | **No optional modules** (MSA, microMIPS, VZ, MT, DSP, EVA, XPA, MCU, CRC, GINV, VP, EJTAG); their config bits 0 | Vol III Tables 9.65-9.69 |
| D6 | **Exception in a forbidden slot:** `EPC` = the compact branch, `BD = 1`; the Vol I text is more specific than Vol III's silence | Vol I §5.3.2.2 p.62; Vol III §6.2.3 p.87, BadInstrP p.181 |
| D7 | **`SDBBP` without EJTAG:** subsetted out, the word is undecodable (RI) | Vol I §2.4.1 p.31; Vol II SDBBP p.361; Vol III p.263 |
| D8 | **`CACHE` with no caches:** no operation | Vol II CACHE p.119 |
| D9 | **`WAIT` wake-up:** the Release 6 pseudocode (p.442-443) transcribed; the prose difference is noted (item 23) | Vol II WAIT p.442-443 |
| D10 | **`Config5.CRCP`/`GI`** absent from the Vol III table: report 0 (modules absent) | Vol III Table 9.69 (no match for CRCP) |
| D11 | **B<cond>C pseudocode erratum:** use `target_offset` as the text and encoding define | Vol II p.83-84, p.78 |
| D12 | **Choice points** (NaN propagation under NAN2008, upper FPR bits, DIV/MOD by zero...): oracle choices with pins in `Choices.lean`; `ChoiceFree` is exact (`choiceFree_exact`) | items 2, 13 |
| D13 | **`XNP` (`RDHWR 5`):** `Config5.XNP = 1`; `LLWP`/`SCWP` absent | Vol III Table 9.69 p.261; Vol II LLWP p.228, SCWP p.355 |

Owner decision 2026-11-16: MIPS32 Release 6 replaces the Release 2 model in place; earlier releases will be added
later, backwards (R5, R3, R2, R1), as profiles (`Release`/`Profile` with one arm, one decoder table per
release, one CP0 layout table per release).
