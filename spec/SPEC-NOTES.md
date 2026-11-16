# MIPS semantics — pinned conventions and divergences

**The target is the MIPS architecture**, pre-Release-6 MIPS32 with the Release 2
feature set (MD00086 Vol II-A Rev 6.06, MD00090 Vol III Rev 6.02, MD00082 Vol I-A
Rev 6.01 are normative; the manual wins over any emulator). The Lean small-step
semantics specifies what programs for that processor mean. **MARS 4.5 and QEMU are
differential oracles**: executables we run programs in and compare against.

Where an oracle matches the architecture it supports our semantics; where it
deviates, **the manual wins** and the deviation is listed in §9 (MARS) or §10
(QEMU, with the manual citation). Facts in §1-§7 about MARS come from the MARS 4.5
source tree, which is **not vendored** here (only `vendor/mars/Mars4_5.jar` is);
the class and file names below (`Memory.java`, `Settings.java`, ...) are pointers
into that source, and the line numbers cannot be re-checked in this repository.
Per-instruction semantics live in [`INSTRUCTION-REF.md`](INSTRUCTION-REF.md).
Page numbers are printed pages. MD00086's table of contents and its body both have a
"p.3" (the body one is pdf page 13, where §1.2 is); `mipsdoc.py` reports both.

## 1. Memory map

MARS's default (SPIM-based) configuration, from `mars/mips/hardware/MemoryConfigurations.java`
(MARS 4.5 source, not vendored; lines 79–96), and what this model implements of it:

| Region | MARS address | In this model |
|---|---|---|
| `.text` base (first instruction) | `0x00400000` | `textBase` (`Types.lean`); the loader's start state `hostedStart` (`Env.lean`) starts there |
| data segment base / `.extern` base | `0x10000000` | not modeled |
| global pointer `$gp` | `0x10008000` | **not modeled**: `initialState` leaves `$gp` = 0 |
| `.data` base | `0x10010000` | `dataBase` (`Asm.lean`) |
| heap base (sbrk) | `0x10040000` | **not modeled** (no `sbrk` service) |
| stack pointer `$sp` initial value | `0x7fffeffc` | `spInit` (`Types.lean`); `$sp` is the only non-zero initial GPR |
| stack base / highest user address | `0x7ffffffc` / `0x7fffffff` | the end of useg/kuseg (MD00090 Vol III Rev 6.02 Table 4.1, p.28); no stack limit is modeled |
| kernel space starts at | `0x80000000` | enforced by the MMU: from User Mode every address `≥ 0x8000_0000` is an Address Error (item 27); the exception vector `0x80000180` is `exceptionVectorAddr`, `.ktext` defaults to it, `.kdata` to `0x90000000` |

All these are **virtual** addresses. The model has the Fixed Mapping MMU (`Config.MT = 3`, item 27):
`State.physMem` is physical memory, and the loader places each image word at the physical address
its virtual address has with `Status.ERL = 0` (`Env.loadAddr`): text `0x0040_0000` → physical
`0x4040_0000`, data `0x1001_0000` → `0x5001_0000`, stack `0x7FFF_EFFC` → `0xBFFF_EFFC`, `.ktext
0x8000_0180` → `0x0000_0180`, `.kdata 0x9000_0000` → `0x1000_0000`, boot code `0xBFC0_0000` →
`0x1FC0_0000`. MARS has no address translation (its addresses are used directly); no corpus program
can tell the difference, since it runs in Kernel Mode with `ERL = 0`, where every MARS address is
legal and the translation is injective on the segments MARS uses. The whole 2^32-byte physical
space exists and memory is byte-addressable. Note: `$sp = 0x7fffeffc` comes from SPIM, not classic
MIPS — do not "fix" it to `0x1000ffff`.

## 2. Registers

Source: `mars/mips/hardware/RegisterFile.java` (MARS 4.5 source, not vendored).

- 32 general-purpose registers, 32-bit bit patterns.
- `$zero` is hardwired: reads return 0, writes are silently ignored
  (`RegisterFile.java`, "you can not change the value of the zero register").
- `$sp` (register 29) initialized to `Memory.stackPointer` = `0x7fffeffc`.
- All other registers start at 0.
- `mult`/`div` use a separate `hi`/`lo` pair (`Instruction.java` in the MARS source; here two 32-bit registers).

## 3. Execution conventions

Source: `mars/simulator/Simulator.java`, `mars/Settings.java` (MARS 4.5 source, not vendored).

- **Branch delay slots: our semantics implements real MIPS32, not MARS's
  default.** `DelayedBranching` setting defaults to `false` in MARS
  (`Settings.java`, index 8 of `defaultBooleanSettingsValues`): with that
  default, MARS updates PC to a taken branch/jump's target immediately, with
  no delay-slot instruction executed. Real MIPS32 hardware always executes
  exactly one delay-slot instruction (the one physically following the
  branch/jump) before the transfer takes effect; our semantics models that
  real-architecture behavior (see §9 item 1), not MARS's no-delay-slot
  configuration. (MARS *can* model delay slots if the user enables the
  setting, which would then match our spec — but that is a MARS
  configuration detail, not why we implement it this way.)
- **Execution starts at the `.text` base** (`0x400000`), not at `main`:
  `StartAtMain` defaults to `false`.
- PC fetches must be word-aligned (else Address Error, AdEL); instruction
  fetch reads the big-endian word at `pc` from physical memory `State.physMem` through the MMU,
  the same memory and translation loads and stores use (§9 items 6, 27).
- **The processor never halts** (`step : State → State`). Reserved
  Instruction, Address Error, Integer Overflow, System Call, Breakpoint,
  Trap, Coprocessor Unusable and Floating Point are architectural exceptions
  (state transitions to the vector) — INSTRUCTION-REF Global rule 6; a
  control transfer in a delay slot raises Reserved Instruction (§9 item 1).
- **The hosted run stops** (an environment convention, `Semantics/Env.lean`,
  §9 item 25) on: the `exit` service, entry to an exception vector the
  loaded image does not cover (`unhandledException`), `pc` leaving the
  loaded image (`noInstruction`), or the step limit.

## 4. Alignment and errors

Source: `mars/mips/hardware/Memory.java` (MARS 4.5 source, not vendored).

- Word access (`lw`, `sw`, fetch): address must be a multiple of 4, else
  `AddressErrorException` ("not aligned on word boundary").
- Halfword access (`lh`, `lhu`, `sh`): multiple of 2.
- Byte access: no alignment requirement.
- In our semantics these raise the architectural Address Error exception
  (AdEL, ExcCode 4, for loads/fetch; AdES, ExcCode 5, for stores) with
  `BadVAddr` set — INSTRUCTION-REF Global rules 5 and 6.

## 5. Syscalls

Source: `Syscall.properties`, `help/SyscallHelp.html`, and the classes in
`mars/mips/instructions/syscalls/` (MARS 4.5 source, not vendored).

Full MARS table (number → name): 1 PrintInt, 2 PrintFloat, 3 PrintDouble,
4 PrintString, 5 ReadInt, 6 ReadFloat, 7 ReadDouble, 8 ReadString, 9 Sbrk,
10 Exit, 11 PrintChar, 12 ReadChar, 13 Open, 14 Read, 15 Write, 16 Close,
17 Exit2, 30 Time, 31 MidiOut, 32 Sleep, 33 MidiOutSync, 34 PrintIntHex,
35 PrintIntBinary, 36 PrintIntUnsigned, 40 RandSeed, 41 RandInt,
42 RandIntRange, 43 RandFloat, 44 RandDouble, 50–59 dialogs.

**Hosted services: 1 (print int), 4 (print string, null-terminated from
memory; scans at most `printStringFuel` = 65536 bytes, see §9 item 20), 10 (exit),
11 (print char).** Argument convention: `$v0` = syscall
number, `$a0` (+ `$a1`, …) = arguments. These four services belong to the
**hosted environment** (`Semantics/Env.lean`, §9 items 9 and 25), not to the
processor: the hosted run performs one instead of stepping when the
instruction at `pc` is a `syscall` selecting it. For the processor (`step`)
`syscall` is always the System Call exception (ExcCode 8), which is also what
the hosted run does for any other `$v0` and what `MipsRun --bare` does for
every `syscall`.

## 6. Instruction set

The modeled instruction set is the 179 constructors of `Instruction`
(`Semantics/Instruction.lean`); the per-family list is in the root `README.md`, the
instruction-by-instruction matrix in `docs/TRACE.md`, and the semantics in
[`INSTRUCTION-REF.md`](INSTRUCTION-REF.md). What is not modeled is listed in §9 item 10
and in [`MIPS-COVERAGE-GAPS.md`](MIPS-COVERAGE-GAPS.md).

Pseudo-instructions (`li`, `la`, `move`, `nop`, `blt`, ...) are assembler sugar; the Lean
assembler expands them following the MARS/GNU-as expansions (MARS's `PseudoOps.txt`, in
the MARS 4.5 source, not vendored). They are not part of the machine-level semantics.

## 7. Endianness and data representation

Our language (the spec target) follows the classic MIPS big-endian
convention. **MARS itself defaults to little-endian** — see §9 item 4 for
the correction to an earlier (incorrect) "big-endian throughout" claim here;
that was a misreading of `Memory.java`. Integers are two's complement;
arithmetic instructions operate on bit patterns with defined wraparound
(`addu`, `subu`) or the MARS-documented behavior for signed variants —
per-instruction details are pinned in Lean spec S against `Instruction.java`.

## 8. What is trusted / not

- **Spec target:** the MIPS32 Release 2 architecture as written in the three manuals above.
  What the Lean development proves about `step`, and how much of it is independent of the
  implementation, is stated in the README ("What is proved, what is tested, what is trusted")
  and `docs/PROOF-NOTES.md`; nothing here claims the semantics is "proven correct" against
  the manuals. The manuals are read by the authors; no machine-readable form of them exists here.
- **Empirical oracles:** MARS 4.5 (`tests/corpus`) and QEMU `qemu-system-mips -cpu 24Kf` with
  `llvm-mc` as the encoding oracle (`tests/oracle`, `scripts/oracle.py`). Agreement supports the
  implementation; it does not define the spec (§9 for MARS, §10 for QEMU).
- **Not modeled:** macros, User-Mode address checks (§9 item 10; Kernel/User Mode and CP0 access
  control are modeled), interrupts (the timer `Count`/`Compare`/`Cause.TI` is modeled, §9 item 28,
  but no Interrupt exception is taken), TLB,
  caches, watch registers, EJTAG, shadow register sets, coprocessor 2, the L format and
  paired-single. Exception *entry* and `eret` are modeled (a handler can be placed at the
  vector); see INSTRUCTION-REF "Coprocessor 0". Branch delay slots **are** in scope — §9 item 1.

## 9. Divergence list (language vs MARS)

Places where MARS's behavior differs from the plain MIPS architecture, and
the decision for our semantics:

1. **Branch delay slots: we implement real MIPS32, overriding MARS's
   default.** Real MIPS32 hardware (the actual architecture, not a MARS
   peculiarity) mandates exactly one delay slot for every branch
   (`beq`/`bne`/`blez`/`bgtz`) and jump (`j`/`jal`): the single instruction
   immediately following the branch/jump in program order **always**
   executes — whether or not the branch is taken — *before* control
   transfers to the target. MARS's default configuration
   (`DelayedBranching=false`, same as SPIM) instead jumps to the target
   immediately with no delay-slot instruction executed; MARS was only ever
   meant to serve this project as a differential-testing oracle, not as the
   spec source, and on this point we deliberately diverge from MARS's
   default to match the real architecture. Concretely (see
   `Semantics/Step.lean`, `Semantics/Types.lean`):
   - A taken branch/jump does not update `pc` to the target in the same
     step. It falls through to `pc + 4` (the delay-slot instruction, which
     always executes next, taken or not) and *schedules* the real target in
     a new `State.pendingBranch : Option W32` field; the delay-slot
     instruction's own step is what actually applies the scheduled target
     to `pc` (`Step.lean`'s `advance`/`mkNext`).
   - `jal`'s `$ra` link value is `pc + 8` (the address *after* the delay
     slot), not `pc + 4` — because the delay-slot instruction still executes
     before control can return to `$ra`.
   - A *not-taken* branch also leaves `pc` at the delay slot and records
     the fall-through address `pc + 8` in `pendingBranch`, so
     `pendingBranch.isSome` means exactly "in a delay slot" (needed for
     `EPC`/`Cause.BD` on an exception there).
   - A control transfer in a delay slot (after a taken or not-taken
     branch) — any of the 28 instructions of `isBranchLike`: branches,
     jumps, branch-likelies, `bc1*`, `eret`, `wait` — **raises Reserved
     Instruction** (a pin; INSTRUCTION-REF Global rule 3), taken in the delay
     slot (`EPC` = the branch, `Cause.BD = 1`). The manual is not uniform
     about this case: for branches and jumps "Pre-Release 6: Processor
     operation is UNPREDICTABLE if a control transfer instruction (CTI) is
     placed in the delay slot of a branch or jump" (MD00086 Vol II-A Rev 6.06,
     BEQ, p.72; MD00082 Vol I-A Rev 6.01 §5.3.2.1, p.62: "the operation of
     both instructions is UNPREDICTABLE"), while for ERET (p.177) and WAIT
     (p.442) "The operation of the processor is UNDEFINED". The same pin
     serves both: "UNPREDICTABLE operations may cause arbitrary exceptions"
     and "must not halt or hang the processor" (MD00086 §1.2.1, p.3-4);
     UNDEFINED operations "may vary from nothing to creating an environment
     in which execution can no longer continue" but "must not cause the
     processor to hang" (§1.2.2, p.4). Reserved Instruction is also exactly
     what Release 6 requires here (MD00082 §5.3.2.1, p.62; ERET p.177, WAIT
     p.442). The former pin, a model halt `branchInDelaySlot`, was not
     permitted (the processor must not halt). `branch_in_delay_slot_reserved_instruction`
     (`Specs/DelaySlot.lean`) states it; oracle test
     `cti_in_delay_slot_reserved` (QEMU 24Kf was observed to do the same; its
     fields are still declared `unpredictable`).
   - **1b. Branch-likely nullification is its own instruction time (Wave 7
     Task 0, owner decision).** The branch-likely Operation is "I: target_offset ←
     sign_extend(offset || 0^2); condition ← (GPR[rs] = GPR[rt])  I+1: if condition
     then PC ← PC + target_offset else NullifyCurrentInstruction() endif" (MD00086
     Vol II-A Rev 6.06, BEQL, p.73; the same shape on BNEL p.104, BLEZL p.95, BGTZL
     p.89, BLTZL p.101, BGEZL p.86, BLTZALL p.99, BGEZALL p.80, BC1FL p.58, BC1TL
     p.62). Statements labeled I+1 "appear to occur “at the same time” as the effect
     of pseudocode statements labeled I for the following instruction" (§1.3, Table
     1.1, p.6), and NullifyCurrentInstruction "nullifies the current instruction ...
     The instruction is aborted, inhibiting not only the functional effect of the
     instruction, but also inhibiting all exceptions detected during fetch, decode,
     or execution of the instruction in question. For branch-likely instructions,
     nullification kills the instruction in the delay slot of the branch likely
     instruction" (§2.2.2.5.4, p.26). So the nullified delay-slot instruction is a
     separate instruction time. The model: a not-taken branch-likely moves `pc` to
     the delay slot, sets `pendingBranch := some (pc + 8)` (it is a delay slot) and
     the new field `State.nullified := true`; the next `step` (`stepCore`, after the
     interrupt and standby checks) is `nullifiedStep`: no fetch, no effect, no
     exception, `pc ← pc + 4`, `pendingBranch := none`, `nullified := false`, and
     the timer ticks (`Count` advances once for the branch and once for the
     nullified slot). Before this change the branch's own step went straight to
     `pc + 8`: one instruction time for two, and no interrupt could be taken at
     the slot.
     **Ambiguity (both readings recorded).** The manual does not say whether an
     asynchronous interrupt can be taken at a nullified slot. Reading (A, chosen):
     the nullified instruction occupies an instruction time like any other, so an
     interrupt is recognised there; the instruction at `PC` is in a branch delay
     slot, so the general exception processing stores "Address of the branch or jump
     instruction (PC-4)" in `EPC` and sets `Cause.BD = 1` (MD00090 Vol III Rev 6.02
     §6.2.3, Table 6.11, p.87), the nullification is abandoned with the pending
     branch, and `eret` re-executes the branch-likely (which re-evaluates its
     condition; it has no side effect except the `$31` link of
     `bltzall`/`bgezall`, which writes the same value again). Reading (B): the
     interrupt is held off until after the nullified slot (a nullified instruction
     "inhibits all exceptions detected during fetch, decode, or execution"). An
     interrupt is not detected during fetch, decode or execution of an instruction
     (it is asynchronous, "the highest priority relative to the next instruction",
     Table 6.7, p.84), so (B) is not forced by that sentence; (A) is the reading that
     needs no extra rule. Statements: `beql_spec_raw` … `bgezall_spec_raw`,
     `bc1fl_spec_raw`, `bc1tl_spec_raw`, `beql_not_taken_squashes_delay_slot`
     (restated: two steps, two ticks), `step_nullified`; `#guard`s in
     `Tests/StepControlTests.lean` (Count delta 2 across a not-taken `beql` and its
     slot; an interrupt at the slot gives `EPC` = the `beql`, `BD = 1`). The Count
     delta is checked only in the model: QEMU's `Count` follows virtual time, so an
     oracle test of it would not be robust (`tests/oracle/timer_count_compare.asm`
     header).
2. **`div`/`divu` by zero: hi/lo unchanged, no trap (a pin).** MD00086
   Rev 6.06 "DIV" (p. 165): the result is UNPREDICTABLE and "No arithmetic
   exception occurs under any circumstances"; leaving `HI`/`LO` unchanged
   is the model's pinned choice of that UNPREDICTABLE result. MARS reads the
   specification the same way (explicit source comment: "no arithmetic
   exception under any circumstances"); COD3 textbooks say "divide with
   overflow". We follow the no-trap reading.
3. **`lw`/`sw` offset sign-extension: MARS latent bug, we follow the ISA.**
   MARS uses the raw 16-bit I-format offset without sign extension for
   `lw`/`sw` (defensive re-extension exists in `lb`/`lh`/`sh`/`addi`/`slti`
   but not there). Invisible for assembler-built programs; would zero-extend
   negative offsets on raw binary input. Our semantics sign-extends per the
   ISA. Differential corpus is assembler-built, so MARS still matches;
   this deviation is documented as a found defect in the test environment.
4. **Endianness: MARS 4.5 headless defaults to LITTLE-ENDIAN memory
   storage; we follow the classic MIPS big-endian convention (ISA truth).**
   `mars/mips/hardware/Memory.java:90` (MARS 4.5 source, not vendored):
   `private static boolean byteOrder = LITTLE_ENDIAN;`. `setByteOrder`
   (line 328) exists but is never called anywhere in this source tree, so
   there is no CLI/GUI override available in headless MARS — every run
   observes little-endian memory. An earlier version of §7 above claimed
   MARS was "big-endian throughout"; that was a misreading of this file and
   has been corrected. Consequence for differential testing: byte-order-
   sensitive probes (e.g. `lb` at offset 0 of a `.word`-declared value) will
   diverge between MARS and our big-endian spec *by design*, not due to a
   bug in either. The differential corpus must stick to endian-invariant
   access patterns — `lw`/`sw` round-trips (store and reload a word through
   the same-width access), and sequential `.byte`/`.asciiz` data accessed
   byte-by-byte — which produce identical observable results under either
   byte order.
5. **`jal`'s `$ra` value: diverges from MARS whenever the delay slot is
   non-empty, as a direct consequence of item 1 — language wins.** Per item
   1, real MIPS32 sets `jal`'s `$ra` to `pc + 8` (the address *after* the
   delay slot), since the delay-slot instruction always executes before
   control returns to `$ra`. MARS's default `DelayedBranching=false` has no
   delay slot at all, so it always sets `$ra = pc + 4` — the address of
   whatever instruction textually follows `jal`, regardless of whether that
   instruction is ever executed. Before real delay slots were implemented,
   `jal` was typically followed immediately by its logical continuation (no
   gap), so `pc + 4 == pc + 8` and the two engines agreed by coincidence.
   Once a real delay-slot instruction (even a pure no-op, inserted solely to
   give `jal` a harmless instruction to execute as required by item 1) sits
   between `jal` and its continuation, `pc + 4` and `pc + 8` are two
   different addresses, and the two engines' `$ra` values necessarily
   disagree — this is not fixable by any choice of delay-slot filler
   instruction, since it follows purely from the fixed 4-byte gap between
   the two conventions. Affects `tests/corpus/jump_jal.asm`: its former
   `andi $a0, $ra, 0xff` / syscall probe of `$ra`'s raw low byte was removed
   for this reason (the program hardcodes `j AfterCall` instead of returning
   through `$ra`, so the probe only showed that `$ra` held *something*).
6. **Instruction fetch reads memory (resolved; formerly a divergence).** `step` fetches the
   big-endian word at `pc` with `readMemWord s s.pc`, from the same (physical) memory, through the
   same MMU (item 27), that loads and stores use; a `Program` (assembler output) is only the loader's input (`load`, `Env.lean`).
   Writing the instruction stream is defined behaviour (MD00086 Vol II-A Rev 6.06, SYNCI, p.412:
   SYNCI "is used after a new instruction stream is written to make the new instructions
   effective relative to an instruction fetch"); the model has no caches (`Config1.IL = DL = 0`),
   so a store is visible to the very next fetch and `synci` has nothing to synchronize — a no-op
   that is correct for a cacheless implementation (its Operation is `SynchronizeCacheLines`,
   p.413; its optional AdEL for kernel addresses is "implementation dependent", p.412, and not
   raised). `sw_next_instruction_is_fetched` / `store_changes_next_instruction`
   (`Specs/SelfModifying.lean`), oracle test `smc_synci`. **Memory that was never written reads
   as 0** (`State.lean`): a pin of what the model's memory system holds where nothing was loaded
   (the architecture does not define memory contents; MARS and the QEMU harness also zero-fill).
   For fetch this means an unloaded address executes as `sll $0, $0, 0`; the processor does not
   stop there — only the hosted run does (item 25).
7. **Stores clear `LLbit`: a legal choice of an unpredictable outcome,
   not an architectural mandate.** MD00086 Rev 6.06 "SC": whether a
   same-processor store between `ll` and `sc` makes the `sc` fail "is not
   predictable" unless `Config5.LLB = 1` (Release 5; Rev 2.50: "the SC may
   succeed or it may fail; the success or failure is not predictable"). The
   model pins "fails after any store (`sb sh sw swl swr swc1 sdc1 swxc1 sdxc1`),
   succeeds after loads" — every store-class instruction of `Step.lean` clears it (the
   docstring of `State.llBit` in `Types.lean` omits `swxc1`/`sdxc1`). `eret` and every exception entry clearing
   `LLbit` *are* architectural ("ERET"; "SC" p. 350: "Exceptions between
   the LL and SC cause SC to fail"). `sc` itself clearing `LLbit` is a pin
   (Rev 2.50 pseudocode has no clear; Rev 6.06 clears only if
   `Config5.LLB = 1`). An `sc` whose address differs from the preceding
   `ll`'s fails ("An SC will fail if the aligned address of the SC does not
   match that of the preceding LL", MD00086 Vol II-A Rev 6.06, SC, p.347):
   `ll` records its address in `State.llAddr`, and `sc` compares bits 31..2 only (the aligned
   word; Wave 7D model fix: the whole addresses were compared before, which made an `sc` to
   `0x8000_1000` after a link address `0x8000_1001` fail; no state `ll` can produce has
   `llAddr` bits 1..0 nonzero, so reachable behaviour is unchanged; regression `#guard` in
   `Specs/Atomic.lean`). `pref`/`prefx` do not touch
   `LLbit` (after a prefetch the `sc` "may fail", p.348; the model lets it
   succeed).
8. **Endianness** — see item 4: MARS is little-endian by default, this
   model is big-endian (INSTRUCTION-REF Global rule 4 formerly said the
   opposite about MARS; corrected).
9. **`syscall` is always the System Call exception; the MARS-style services are the
   environment's.** MD00086 Vol II-A Rev 6.06, SYSCALL, p.415: "A system call exception
   occurs, immediately and unconditionally transferring control to the exception handler";
   Operation `SignalException(SystemCall)`. `step` does exactly that, for every `$v0`
   (`syscall_spec_raw`). The hosted run (`Env.lean`, item 25) performs services 1/4/10/11
   *instead of* stepping when the instruction at `pc` is a `syscall` selecting one, as if an OS
   had served the exception and returned (`hostStep_syscall_spec`, `hosted_print_int`,
   `hosted_exit`; `hostStep_eq_step` says the hosted run is `step` otherwise). MARS reports an
   error for unknown service numbers; the differential harness treats "MARS error" and "our
   unhandled System Call exception" as the same verdict.
10. **Operating modes; CP0 scope.** Kernel Mode and User Mode are modeled
    (MD00090 Vol III Rev 6.02 ch.3, p.21-23); Supervisor Mode and Debug Mode are
    not implemented (optional: "Supervisor Mode is optional. If Supervisor Mode is not
    implemented, bit 3 of the Status register must be ignored on write and read as zero",
    MD00082 Vol I-A Rev 6.01 §2.4.2, p.32; `R0`, Table 9.47 p.195; so `KSU = UM ‖ 0`). `kernelMode s` = `UM = 0` or `EXL = 1`
    or `ERL = 1` (§3.2, p.21); `userMode s` = `UM = 1`, `EXL = 0`, `ERL = 0` (§3.4,
    p.22); `cp0Usable s` = Kernel Mode or `CU0 = 1` (§3.5.3, p.23). When coprocessor 0
    is not usable, `mfc0`/`mtc0`/`di`/`ei`/`eret`/`wait`/`rdpgpr`/`wrpgpr` and every undecodable COP0
    or CACHE word raise Coprocessor Unusable with `Cause.CE = 0` (§6.2.22, p.100; for
    the undecodable words CpU takes the place of Reserved Instruction, §6.2.21 p.99 and
    Table 6.6 p.83). Pin: `eret`/`wait` in a delay slot are Reserved Instruction in
    every mode (the delay-slot check comes first; the case is UNDEFINED, ERET p.177,
    WAIT p.442). Exception entry sets `EXL`, so a handler always runs in Kernel Mode,
    and leaves `UM` alone, so `eret` returns to the mode the exception came from.
    **User-Mode address checks** (wave 4, COMPLIANCE F10): a kseg0/kseg1/kseg2/kseg3
    reference from User Mode — load, store or instruction fetch — raises Address Error
    (AdEL/AdES, `BadVAddr` = the virtual address; Vol III Table 4.2 p.30, §6.2.9 p.92-93).
    They are the MMU's (`translate`, item 27), inserted in the six memory functions (item 26).
    **Implemented `Status` bits:** `IE` (0), `EXL` (1), `ERL` (2), `UM` (4),
    `IM7..0` (15..8), `BEV` (22), `CU0` (28), `CU1` (29) — mask `0x3040FF17`; every
    other bit reads 0. `IE`/`IM`/`EXL`/`ERL` gate interrupts (item 29).
    **Implemented `Cause` bits:** `BD` (31), `CE` (29..28), `ExcCode` (6..2)
    written by exception entry; `DC` (27), `IV` (23), `IP1..0` (9..8)
    writable by `mtc0` (mask `0x08800300`; MD00090 Vol III Rev 6.02 §9.36,
    p.209-210). `DC` stops `Count` (item 28). `WP` (22) reads 0 and ignores writes (no
    watch registers). `TI` (30) is the timer request (item 28) and `IP7` (15) shows it
    (`IntCtl.IPTI = 7` pin); `IP7..IP2` also show the hardware interrupt lines `State.hwInt`
    (inputs; the environment holds them deasserted, item 29); `PCI` is never set (no performance
    counters).
    **Reset** (`resetException`, `resetState`; MD00090 Vol III Rev 6.02 §6.2.5,
    p.89-90): `PC ← 0xBFC0_0000`, `Status.BEV ← 1`, `Status.ERL ← 1`, `Cause.DC ← 0`,
    `HWREna ← 0`, `EBase` Exception Base ← 0 (reads `0x8000_0000`), `Config.K0 ← 2`, `ErrorEPC ←`
    the restart PC (the branch when the reset hits a delay slot). `Status.RP/TS/SR/NMI
    ← 0` hold trivially (not implemented, read 0), and so do `IntCtlVS ← 0` and `SRSCtlHSS ←
    HighestImplementedShadowSet`, `SRSCtlESS/PSS/CSS ← 0` (p.90: both registers are constants, item 29).
    The processor leaves standby (item 23). The other registers the Operation
    names (Random, PageMask, PageGrain, Wired, EntryHi, SRSMap,
    WatchLo, PerfCnt) do not exist in the model; `Config1/2/3 ← ConfigurationState` hold trivially
    (constants, item 28). **Pins:** every register
    the section does not give a reset state keeps its value in `resetException s`
    ("only the following registers have defined state", p.89); `powerOnState` gives
    all of them the value 0 for a cold power-on (GPRs including `$sp`, `HI`/`LO`, FPRs,
    `FCSR` — every FCSR field's reset state is "Undefined", MD00082 Vol I-A Rev 6.01
    Table 6.8 p.92-95 — `Status` UM/EXL/IE/IM/CU0/CU1, `Cause`, `EPC`, `BadVAddr`,
    `Count`, `Compare`, `Cause.TI`, memory), and `pc = 0` there, so `resetState.ErrorEPC = 0` (p.89: on power-up the
    restart PC "may or may not be predictable"); the pending branch is dropped and
    `LLbit` is cleared (the reset "aborts state machines", p.89; no reset state is
    given for `LLbit`). So `resetState`: `pc = 0xBFC0_0000`, `Status = 0x0040_0004`.
    **Environment convention for the hosted start state** (`Env.lean`): `hostedStart =
    bootConvention textBase resetState`, i.e. reset followed by what a boot ROM would
    do: `Status ← 0x2000_0000` (only `CU1`: Kernel Mode, `BEV = ERL = 0`, FPU usable),
    `$sp ← spInit`, jump to `textBase`. It equals the old `initialState textBase`
    (`hostedStart_is_reset_then_boot`), so hosted programs see exactly the start state
    they always did. `MipsRun --reset` starts at the reset vector instead.
    **Reset is not in the QEMU oracle.** The harness loads tests with `-kernel`; QEMU's
    `malta` board then places its own boot stub at `0xBFC0_0000` (first instruction executed
    after reset: `j 0xbfc00580`) and clears `Status.ERL` for a `-kernel` boot (`-d cpu` shows
    `Status = 0x0040_0000` at `pc = 0xbfc00000`), so test code never runs at the reset vector.
    With a raw `-bios` ROM instead (no harness), QEMU 24Kf's state at `0xBFC0_0000` is
    `Status = 0x0040_0004` and `Config = 0x8000_8482`: the model's reset `Status`; its
    `Config` differs (model `0xA400_8582`: `MT = 3` Fixed Mapping where QEMU's 24Kf has `MT = 1`
    TLB, and the model's pinned `K23 = KU = 2`; the MMU type is implementation-defined and
    declared `unpredictable` in `tests/oracle/cp0_config_k0_rw.asm`). Comparing more needs a ROM-resident dump harness.
    **Identification registers** (read-only constants): `PRId` (15,0) =
    `0x0001_0000` (Company ID 1, Processor ID 0 — names no real product;
    §9.40, p.221); `Config` (16,0) = `0x8000_8580` plus `K23`/`KU`/`K0` (`M`, `BE` = 1,
    `AT` = 0, `AR` = 1 = Release 2, `MT` = 3 Fixed Mapping MMU; §9.45, p.233-235; reset value
    `0xA400_8582`) with `K23` (30..28) and `KU` (27..25) Read/Write for the Fixed Mapping MMU
    (Table A.2 p.317, item 27) and
    `K0` (bits 2..0) Read/Write ("Kseg0 cacheability and coherency attribute",
    Reset State "Undefined", Required; Table 9.64, p.235): `State.cp0ConfigK0`,
    reset 2 (Uncached; the reset pseudocode's "ConfigK0 <- 2 # Suggested",
    §6.2.5 p.90), `mtc0` stores bits 2..0 and `mfc0` reads them back. Table
    9.12 (p.133) lists the encodings: 2 Uncached and 3 Cacheable "Required", 0, 1
    and 4..7 "Available for implementation-dependent use", "Optional". Pins: all
    eight values are accepted and read back (pre-Release 6 the manual does not
    say what a write of an unsupported attribute does; only "For Release 6,
    writes of unsupported values are ignored", p.235), and `K0` has **no effect**:
    the model has no cache (`Config1.IL = DL = 0`), so there is nothing for a
    cacheability attribute to select. `K23`/`KU` are treated the same way (reset
    pinned to 2, all values accepted, no effect). The rest of `Config` is read-only;
    `Config1` (16,1) = `0x8000_0001` (`M` = 1, Config2 present, item 28; `FP`:
    `MMU Size - 1` = 0 (item 27), no caches, no coprocessor 2, no watch/perf-counter/EJTAG/MIPS16e;
    §9.46). `EBase` (15,1; §9.41, p.223-224) has no write gate: bits 29..12
    writable, 31..30 fixed `10`, `CPUNum` 0; it supplies the vector base when
    `BEV = 0` (§6.2.3, p.88). Writing a different Exception Base while
    `BEV = 0` is UNDEFINED in the architecture; the model just takes the new
    value.
    **Required on a Release 2 processor but NOT MODELED** (an `mfc0`/`mtc0`
    naming one of these registers, or one of these instructions, does not
    decode and raises Reserved Instruction — item 11 — or, for a COP0 or CACHE
    word executed when coprocessor 0 is not usable, Coprocessor Unusable):
    - (since wave 6 the interrupt system, `IntCtl`, `SRSCtl`, `RDPGPR`/`WRPGPR` are modeled: item 29;
      `SRSMap` (12,3) does not decode, a pin of its UNPREDICTABLE access with `SRSCtl.HSS = 0`);
    - the TLB and its instructions (`TLBP` p.427, `TLBWI` p.430 …; TLB
      exceptions §6.2.10, p.93) — the MMU is the Fixed Mapping MMU, `Config.MT = 3`
      (item 27), and with it "The TLBWR, TLBWI, TLBP, and TLBR instructions are no longer
      required and must cause a Reserved Instruction Exception" (Vol III §A.1.3, p.317);
    - `CACHE` (p.114-121) — `Config1` reports no caches;
    - watch registers (`WatchLo`/`WatchHi`, §9.55-9.56, p.279-281; Watch
      exception §6.2.25, p.101) — optional, `Config1.WR = 0`;
    - EJTAG (`DERET` p.163, `SDBBP` p.361) — `Config1.EP = 0`;
    - coprocessor 2: `Config1.C2 = 0` and `Status.CU2` reads 0, so every
      COP2-space word (opcodes `0x12`, `0x32`, `0x36`, `0x3a`, `0x3e`) raises
      Coprocessor Unusable with `Cause.CE = 2` (§6.2.22, p.100) rather than
      Reserved Instruction.
11. **Strict decoding and UNPREDICTABLE encodings (a pin).** A word with a
    nonzero reserved field, an UNPREDICTABLE field combination (`clz`/`clo`
    with `rt ≠ rd`, bad `ext`/`ins` ranges), or an unmodeled CP0 register /
    `sel` raises Reserved Instruction. The manual makes nonzero
    must-be-zero fields UNPREDICTABLE (MD00086 Rev 6.06 §2.1.1, p. 12), and
    UNPREDICTABLE "may cause arbitrary exceptions" (p. 3, §1.2.1; pdf page 13): Reserved
    Instruction is a legal pinned outcome, not a mandate. Other pinned
    UNPREDICTABLE/UNDEFINED cases: `jalr` with `rs = rd` (p. 196);
    `bltzal`/`bgezal`(+likely) with `rs = 31` (BLTZAL p. 98, BGEZAL p. 76, BLTZALL p. 99,
    BGEZALL p. 80; the content of these pins is in item 18); a branch, jump,
    `eret` or `wait` in a delay slot (Reserved Instruction, item 1; pp. 72,
    177, 442). MARS's decoder is laxer.
    Deliberately tolerated don't-care fields are listed in INSTRUCTION-REF
    Global rule 6.
12. **Stops are the environment's, not the processor's.** `exit`, `unhandledException code
    epc badVAddr` and `noInstruction pc` (`HaltReason`, `Env.lean`) have no architectural
    counterpart: they are where the hosted run stops observing the processor (item 25). The
    former `branchInDelaySlot` halt is gone (item 1).
13. **Floating point follows the manuals, bit for bit; no host floats.**
    All FP arithmetic is `Semantics/FpOps.lean`: the exact result on bit
    patterns, one correctly-rounded pack under FCSR.RM, IEEE flags, FCSR
    Cause/Flags/Enables and the Floating Point exception (ExcCode 15, no
    destination write). Target: 32-bit FPU, `Status.FR = 0`, legacy NaN
    encoding (`FIR.Has2008 = 0`). Pins and manual inconsistencies:
    - **NaN operand order.** MD00082 Vol I-A Rev 6.01 §6.3.1.5 (p.82): a QNaN
      operand makes the result a QNaN and "when possible, this QNaN result is
      one of the operand QNaN values"; a new QNaN (Table 6.3: `0x7FBFFFFF`,
      `0x7FF7FFFF_FFFFFFFF`) is created "when no input operand QNaN value can
      be copied". The manual does not say *which* operand when two are quiet:
      the model returns the first in operand order (`fs` before `ft`). A
      signaling-NaN operand next to a quiet one therefore gives the quiet one
      (with Invalid). The operand order is the printed order of each Operation
      (7R): MADD `(vfs × vft) + vfr` and MSUB `(vfs × vft) − vfr` put the
      product first, NMADD `−(vfr + (vfs × vft))` puts `fr` first (NMADD.fmt
      p.308, read from the PDF: the text extraction loses the operators),
      NMSUB `−((vfs × vft) − vfr)` the product first (p.310). The spec states
      this as an implementation choice inside the trusted IEEE core
      (`Manual/FPU.lean` header).
    - **`FIR.L`.** The manual contradicts itself, and the model takes the
      minimal consistent reading. For: MD00086 Vol II-A Rev 6.06 §3.1, p.30,
      the allowed FPU subset with D, "Config1.FP=1, Status.FR=(see below),
      FIR.S=FIR.L=FIR.D=FIR.L=1, FIR.PS=0" ("pre-MIPSr5 permits this 64-bit
      configuration, and allows both FPU register modes. Status.FR=0 support
      is required but Status.FR=1 support is optional"; the 32-bit-only
      subset without D "is permitted by Release 6, but prohibited by
      pre-Release 6 releases"), and MD00082 Vol I-A Rev 6.01 Table 6.4, p.85,
      Release 2, 32-bit FPU: "64-bit data formats D/L use even/odd pairs:
      FIRD=1 and FIRL=1 required". Against: every L-format instruction page,
      "The result of this instruction is UNPREDICTABLE if the processor is
      executing in the FR=0 32-bit FPU register model; it is predictable if
      executing on a 64-bit FPU in the FR=1 mode, but not with FR=0, and not
      on a 32-bit FPU" (CVT.L.fmt, p.154). Every pre-Release-6 subset that
      has D also has L, so the model reports `FIR = 0x0033_0000` (`S`, `D`,
      `W`, `L` = 1; `F64` = 0, `PS` = 0, `Has2008` = 0), and keeps the
      L-format instructions (`CVT.L.fmt`, `CVT.S.L`/`CVT.D.L`,
      `ROUND/TRUNC/CEIL/FLOOR.L.fmt`) and `LUXC1`/`SUXC1` undecoded: they
      raise Reserved Instruction, a pin of their UNPREDICTABLE result with
      `FR` = 0 (UNPREDICTABLE operations may raise arbitrary exceptions, Vol II
      1.2.1 p.3). `FIR.L = 0` would match no allowed pre-Release-6 subset.
    - **`CVT.W.fmt` typo.** MD00086 Vol II-A Rev 6.06 p.160 gives the
      `NAN2008 = 0` default result as "2^63–1"; ROUND.W.fmt (p.342) and
      MD00082 Table 6.3 (p.82) say 2^31−1 = `0x7FFFFFFF`, which is what the
      model returns.
    - **Multiply-add family: separate operations, FCSR per instruction (7R; Wave 12a
      model fix, audit B1/B2).** MADD.fmt (MD00086 Vol II-A Rev 6.06, p.256): "The
      results and flags are as if separate floating-point multiply and add
      instructions were executed ... The Cause bits are ORed into the Flag bits if
      no exception is taken" (MSUB p.287 "multiply and subtract", NMADD p.308 /
      NMSUB p.310 "... and negate"; each page has the same last sentence). MD00082
      Vol I-A Rev 6.01, Table 6.8 `Cause` (p.94): "A bit is set to 1 if the
      corresponding exception condition arises during the execution of an
      instruction and is set to 0 otherwise"; §6.7.1 (p.99): "instructions that
      trap do not update the Flag bits". The model (`Step.lean`, `fpStep` +
      `fpFinishS/D`, `Mips.Fp.accFlags`/`setCause`) and the spec
      (`Manual.Ops.MADD_S` …, `FPCheck` then `FPResult`) execute the operations one
      after the other, each rounded with the result and exception conditions of
      the separate instruction; after each, FCSR.Cause holds the **union** of the
      conditions of the operations so far and CheckFPException is made; Flags |=
      the union only when the whole instruction completes; a trapping instruction
      writes no FPR and leaves Flags unchanged. Reference: `Mips.Fp.MaddSpec`
      (`OpAcc`). **Reading of a trapping multiply:** the multiply that traps ends
      the instruction with the multiply's Cause (the add/negate are not executed).
      Both quotes support it: "as if separate ... instructions were executed" — a
      separate MUL that traps is not followed by the ADD — and Table 6.8's
      per-instruction Cause holds the conditions that arose during the execution,
      which stops at the trap ("a trap occurs before the instruction that causes the
      trap ... can complete", §6.7.1 p.98-99). Before Wave 12a the model wrote Cause
      per operation (an untrapped instruction left the last operation's Cause) and
      ORed each operation's exceptions into Flags as it completed, so a trap in the
      add left the multiply's conditions in Flags (audit reproducers
      `b_madd_trap_flags`, model `0x00010804` vs the manual's Flags 0, and
      `b_madd_cause`, model `0x00000004` vs `0x00001004`). QEMU now agrees on the
      untrapped Cause (the former §10 deviations of `fp_madd_msub_nmadd_nmsub`,
      `fp_rand_{s,d}_madd_{0,1}` and the Cause part of `fp_madd_separate_ops` are
      matches); it still differs on a trapping multiply (QEMU runs the add too,
      §10 `fp_madd_mul_trap`). The negation is `NEG.fmt` (arithmetic with
      `Has2008 = 0`, item 21).
    - **`RECIP`/`RSQRT`** accuracy and rounding-mode dependence are
      implementation-dependent (p.336, p.343): pinned to `1.0 / x` (`DIV`) and
      `1.0 / sqrt(x)` (`SQRT` then `DIV`). In the spec these are `Impl.recipS/D`,
      `Impl.rsqrtS/D` (§11).
    - **UNPREDICTABLE cases pinned:** an odd register number for a double
      (the pair `(N, N+1 mod 32)` is used); `cfc1` of a nonexistent control
      register reads 0 and `ctc1` to one writes nothing, but the
      `CheckFPException()` that follows the UNPREDICTABLE arm still runs (CTC1
      p.150; changed in 7C S4b, before it was a no-op without the check);
      reserved bits in a value
      written by `ctc1` are ignored; FCSR bits 22..18 read 0.
    - **Not raised:** Unimplemented Operation (`Cause.E`) — only `ctc1` can
      set it. With `FCSR.FS = 1` results are flushed (§6.7.2.4, p.101-102);
      subnormal *operands* are not (implementation-dependent before
      Release 5).
    - **Not modeled (UNPREDICTABLE with `FR = 0`, so no decode → Reserved
      Instruction, or Coprocessor Unusable when `CU1 = 0`):** the L format
      (`cvt.l.fmt` p.154, `round.l`/`trunc.l`/`ceil.l`/`floor.l`,
      `cvt.s.l`/`cvt.d.l`), `luxc1` (p.234) / `suxc1` (p.391), and
      paired-single (`*.ps`, `cvt.s.pl` p.157, `alnv.ps` …).
14. **Known oracle deviations (the manual wins).**
    - **MARS 4.5** has no FCSR, no FP exceptions, a single condition flag
      per `cc` but no flags/rounding modes, and its `cvt.w.s` truncates (a
      Java `(int)` cast) where the model follows FCSR.RM (round to nearest
      even at start). Corpus programs use `trunc.w.s`, or integral inputs,
      where truncation is meant.
    - **QEMU**: `abs.fmt/`neg.fmt` of a NaN do not signal Invalid
      there; with `Has2008 = 0` the manual makes them arithmetic ("any NaN
      operand signals invalid operation", MD00086 Vol II-A Rev 6.06, ABS.fmt
      p.32, NEG.fmt p.307). A signaling NaN next to a quiet NaN gives the
      default QNaN in QEMU's softfloat; the model copies the quiet operand
      (item 13).
15. **Assembler notes.** `break c[, d]` follows GNU as operand syntax (`c` in
    bits 25..16, `d` in bits 15..6 of the manual's 20-bit `code` field,
    MD00086 Vol II-A Rev 6.06 BREAK p.109); MARS puts a single operand in
    bits 25..6. `.set noreorder`/`.set noat`/`.set at` are accepted;
    `.set reorder` is rejected (the assembler never fills delay slots).
16. **`pause` and `nal` decode as other instructions; both assemble.** Availability: PAUSE's
    Format line reads "MIPS32 Release 2/MT Module" (MD00086 Vol II-A Rev 6.06, PAUSE, p.317);
    NAL's reads "Assembly Idiom MIPS32 pre-Release 6, MIPS32 Release 6" and "The NAL instruction
    encoding, however, works on all implementations, both pre-Release 6 ... and Release 6" (NAL,
    p.306), so both are available on a pre-Release-6 Release 2 CPU. `pause` assembles to
    `sll $0,$0,5` (0x00000140) and `nal` to `bltzal $0,0` (0x04100000; the offset is ignored,
    written 0). PAUSE is modeled as the NOP its encoding is: "The PAUSE instruction is
    implementation-dependent, but it usually involves descheduling the instruction stream until the
    LLBit is zero" and "can therefore be placed into existing lock sequences and treated as a NOP by
    the processor, even if the processor does not implement the PAUSE instruction" (p.317), so the
    deschedule-until-LLbit-clear of the Operation is a permitted no-op in the single-threaded,
    interrupt-free-wait model (pin). PAUSE has no constructor, like `ssnop`/`ehb` (`sll` hint
    encodings); a constructor would make `decode (encode (.sll 0 0 5))` return a different
    instruction and change the `decode_encode` statement's domain for no behavioural gain.
    Earlier text of this item (before the mnemonics existed):
    `PAUSE` is encoded `SPECIAL`, `sll` funct, `shamt = 5` (MD00086 Vol II-A Rev 6.06,
    PAUSE, p.317) and `NAL` is `REGIMM` `rt = 10000`, `rs = 0` (NAL, p.306: "NAL was
    originally an alias for pre-Release 6 instruction BLTZAL"). `decode` returns `.sll 0 0 5`
    and `.bltzal 0 imm`; both execute with the semantics of those instructions (a no-op;
    link `$ra ← pc + 8`, never taken). Consequence: a `pause` in a branch delay slot
    executes as a no-op, where the manual lists `PAUSE` and `NAL` among the control
    transfer instructions that are UNPREDICTABLE in a delay slot (JALR, p.196, Restrictions;
    PAUSE p.317); a `nal` in a delay slot raises Reserved Instruction like any `bltzal` (item 1).
    (The assembler now accepts `pause` and `nal`, no operands.) `ssnop` and `ehb` are accepted and assemble to `sll $0,$0,1` /
    `sll $0,$0,3` (SSNOP p.387).
17. **`mul` leaves `HI` and `LO` unchanged (a pin of an UNPREDICTABLE result).** MD00086 Vol II-A
    Rev 6.06, MUL, p.299: "The contents of HI and LO are UNPREDICTABLE after the operation"
    (Operation: `HI ← UNPREDICTABLE`, `LO ← UNPREDICTABLE`). The model's `.mul` arm
    (`Step.lean`) writes only `rd`. The QEMU oracle test `mul_hilo_unpredictable` declares
    `hi`/`lo` as not compared.
18. **Branch-and-link with `rs = 31`, and `jalr` with `rs = rd`.** BLTZAL (p.98), BGEZAL (p.76),
    BLTZALL (p.99) and BGEZALL (p.80): "GPR 31 must not be used for the source register rs ...
    The result of executing such an instruction is UNPREDICTABLE." The model links `$ra` and
    tests the condition on the value `rs` had **before** the link (it reads `rs` from the
    original state). JALR (p.196): "Register specifiers rs and rd must not be equal ... The
    result of executing such an instruction is UNPREDICTABLE." The model reads the jump target
    from `rs` before writing `rd`, so `jalr $t0, $t0` jumps to the old `$t0` and links
    `pc + 8` into it.
19. **`jr`/`jalr` hint field: only 0 and `10000` decode (7R; formerly tolerated).** The 5-bit `hint`
    (bits 10..6): MD00086 Vol II-A Rev 6.06, JR p.207 / JALR p.196: "In release 1 of the architecture, the
    only defined hint field value is 0" and "In Release 2 ... bit 10 of the hint field is used to encode
    a hazard barrier". `decode` maps hint 0 to `jr`/`jalr`, hint `10000` to `jrHb`/`jalrHb` (the model has
    no hazard state, so `ClearHazards()` is vacuous) and every other hint to Reserved Instruction (an
    UNPREDICTABLE encoding pinned to RI, item 11); `encode` emits hint 0 / `10000` accordingly. Before 7R
    the hint was ignored, which made `DecoderSound decode` false.
20. **Hosted service 4 scans at most `printStringFuel` bytes.** `printStringFuel = 65536`
    (`Env.lean`) bounds the scan for the terminating NUL so that the hosted step stays total.
    This is an environment limitation, not an architectural statement (item 9). A string without a NUL in its first 65536 bytes prints
    those 65536 bytes.
21. **`ABS.fmt`/`NEG.fmt` (and so the negate step of `NMADD`/`NMSUB`) of a NaN: reading A′ (7R model
    fix; formerly reading A).** Legacy encoding (`FIR.Has2008 = 0`): the fraction MSB b1 is 1 for a
    signaling and 0 for a quiet NaN (MD00082 Vol I-A Rev 6.01 Table 6.2, p.80), so `0x7fa00000` is a QNaN.
    The pages say both "If FIRHas2008=0 or FCSRABS2008=0 then this operation is arithmetic. For this case,
    any NaN operand signals invalid operation" (ABS.fmt, MD00086 Vol II-A Rev 6.06 p.32; NEG.fmt p.307) and,
    for NEG, "The value is negated by changing the sign bit value" (p.307); Vol I-A §6.3.1.5 (p.82) says
    "QNaN operands do not cause arithmetic operations to signal an exception" and "When possible, this QNaN
    result is one of the operand QNaN values". Three readings (`Manual.AbsNegNaN`, `Oracle.absNegNaN`):
    *A*: Invalid, the QNaN operand returned unchanged (the model before 7R); *A′*: Invalid, and the untrapped
    result is the operand with the sign bit cleared (ABS) or flipped (NEG) — both sentences of the pages
    hold; *B*: no exception, the sign changed (QEMU). **The model takes A′** (`f32Abs`/`f32Neg`/`f64Abs`/
    `f64Neg` in `FpOps.lean`; `modelOracle.absNegNaN = .A'`). A signaling NaN, in every reading, signals
    Invalid and untrapped gives the default QNaN `0x7FBFFFFF` / `0x7FF7FFFF_FFFFFFFF` ("An SNaN is never
    produced as a result value", §6.3.1.4 p.81; Table 6.3 p.82): a sign-changed SNaN would be an SNaN.
    The negate step of NMADD.fmt (p.308) / NMSUB.fmt (p.310) ("as if separate floating-point multiply and
    add and negate instructions were executed") is this `NEG.fmt`: a NaN sum signals Invalid and its sign
    is flipped. QEMU returns the sign-changed value without Invalid (§10, `fp_abs_neg_nan`).
    **Wave 12a re-examination (audit B3): NMADD/NMSUB with a QNaN operand.** Two readings, both quoted:
    (i) the general rule, "QNaN operands do not cause arithmetic operations to signal an exception"
    (MD00082 Vol I-A Rev 6.01 §6.3.1.5, p.82), would make an NMADD whose only NaN is a quiet operand
    signal nothing; (ii) the instruction pages say "The results and flags are as if separate
    floating-point multiply and add and negate instructions were executed" (NMADD.fmt, MD00086 Vol II-A
    Rev 6.06 p.308; NMSUB.fmt p.310: "... multiply and subtract and negate ...") and the separate
    negate is `NEG.fmt` with `Has2008 = 0`: "this operation is arithmetic. For this case, any NaN operand
    signals invalid operation" (p.307), so the negate of the QNaN sum signals Invalid. The instruction
    pages are specific to these instructions and name the flags explicitly; the §6.3.1.5 sentence is
    the general rule that `NEG.fmt` itself already overrides for a QNaN operand. **The model keeps (ii)**
    (unchanged pin, `Oracle.absNegNaN = .A'`, `f32Neg`/`f64Neg`); the text is contested, and QEMU follows
    (i) (§10, `fp_madd_separate_ops`). COMPLIANCE E12d records the same.
22. **NaN payload narrowing in `cvt.s.d`.** A quiet NaN keeps its sign and its most significant
    fraction bits (the low bits are dropped); widening (`cvt.d.s`) appends zeros. If narrowing
    leaves a zero fraction (the pattern would be an infinity) the destination's default QNaN is
    supplied. MD00082 Vol I-A Rev 6.01 §6.3.1.5, p.82: "Propagation of the diagnostic
    information requires information contained in a QNaN to be preserved through arithmetic
    operations and floating-point format conversions"; the manual does not say how a payload
    is narrowed, so the truncation and the zero-fraction rule are pins (`Format.convertNaN`).
23. **`wait` enters standby (wave 6; formerly an immediate restart).** MD00086 Vol II-A Rev 6.06,
    WAIT, p.442: "The WAIT instruction is implemented by stalling the pipeline at the completion of the
    instruction and entering a lower power mode. The pipeline is restarted when an external event, such
    as an interrupt or external request occurs, and execution continues with the instruction following
    the WAIT instruction"; pre-Release-6 Operation "I: Enter implementation dependent lower power mode /
    I+1: Potential interrupt taken here". The model: `wait` completes (`PC ← PC + 4`) and sets
    `State.standby`; a standby step executes nothing and only the timer advances (`step_standby_stays`).
    An enabled interrupt ends standby through the Interrupt exception with `EPC` = the instruction after
    the `wait` ("EPC for the interrupt points at the instruction following the WAIT instruction", p.442;
    `step_standby_interrupt`). **Pins:** (a) a pending, unmasked request (`Cause.IP & Status.IM ≠ 0`) that
    is not enabled (`IE = 0`, `EXL = 1` or `ERL = 1`) restarts the pipeline — "It is
    implementation-dependent whether the pipeline restarts when a non-enabled interrupt is requested"
    (p.442); the model takes the Release 6 rule (`interrupt_pending_and_not_masked_out`, p.443) — and
    the restart takes one step (`step_standby_restarts`); (b) `Count` keeps counting in standby ("Prior to
    Release 6, whether Count is disabled was implementation-dependent", p.442); (c) the code field
    selects nothing ("unimplemented encodings must default to WAIT 0", p.442); (d) there are no
    "external requests" besides interrupt requests in this system, so without one `wait` stops the
    processor for good (only `Count` moves): legal, since nothing obliges a restart. Reset leaves standby
    ("The assertion of any reset or NMI must restart the pipeline", p.442). `wait` in a delay slot
    raises Reserved Instruction (item 1; the manual: UNDEFINED, p.442). QEMU 24Kf agrees on the
    timer-wakes-`wait` case (`tests/oracle/irq_wait_timer.asm`, PASS).
24. **`Cause.CE` is written as 0 by every exception other than Coprocessor Unusable.** MD00090
    Vol III Rev 6.02, Cause (§9.36, p.209): CE "is loaded by hardware on every exception, but
    is UNPREDICTABLE for all exceptions except for Coprocessor Unusable". `exceptionEntry`
    (`Step.lean`) clears bits 29..28 and ORs in `ce << 28`, with `ce = 0` unless the exception is
    Coprocessor Unusable (`ce = 1` for COP1, `2` for COP2). `exceptionEntry_ce` states this.

25. **The environment layer is outside the architecture.** `Semantics/Env.lean` holds
    everything that is a convention of this model rather than of the processor, so that `step`
    can be read against the manual without exceptions:
    - **Start state and loader.** The machine starts at the architectural reset state
      (`resetState`, item 10). The hosted environment then applies its **boot convention**
      (`bootConvention`: `Status ← CU1`, `$sp ← spInit`, `pc ← 0x0040_0000`) — what boot code
      at the reset vector would do; it is outside the architecture. `load p` writes the
      assembled image (text, data, `.ktext`, `.kdata`) into the memory of `hostedStart =
      bootConvention textBase resetState`, which equals `initialState textBase`
      (`hostedStart_is_reset_then_boot`, `Specs/Reset.lean`). `MipsRun --reset` loads the
      image into `resetState` instead (`loadAtReset`) and runs from `0xBFC0_0000`: the program
      provides the boot code (`.ktext 0xBFC00000`).
    - **Hosted services** (item 9) and their output buffer (`Hosted.out`; `State` has no output
      field any more).
    - **Stopping conventions.** The hosted run stops before a step when `pc` is word-aligned and
      outside the loaded image: `unhandledException (Cause.ExcCode) EPC BadVAddr` when the
      machine has just entered the general exception vector (`Status.EXL = 1`) and no handler was
      loaded there, `noInstruction pc` otherwise. A misaligned `pc` is not a stop (the processor
      raises AdEL).
    - `MipsRun --bare` runs with services off (every `syscall` is the exception); the stopping
      conventions still apply, since they are how the observer decides a run is over.
    `hostStep_eq_step` / `runHosted_agrees_with_run` (`Specs/Hosted.lean`) state that the hosted
    run is the bare `run` whenever it neither stops nor performs a service.
26. **Memory access has one implementation point.** Every processor memory access (fetch, every
    load and store, `lwl`/`lwr`/`swl`/`swr` byte by byte) goes through the six `readMem*` /
    `writeMem*` functions of `State.lean`; each takes a **virtual** address, checks alignment,
    translates it with `translate` (item 27) and indexes the **physical** memory `State.physMem`.
    The loader (`Env.lean`) and observers (`readCString` reads through `readMemByte`; `MipsRun`'s
    JSON) are not the processor.
27. **The MMU is the Fixed Mapping MMU (`Config.MT = 3`).** MD00090 Vol III Rev 6.02 Appendix
    A.1, p.313-317 (COMPLIANCE B11/B12: `MT = 0` "None" has no defined translation; Fixed
    Mapping is the minimal fully specified organization). `State.lean`:
    - `fixedMappingPA erl va` is Table A.1 (p.313-314): useg/kuseg `VA + 0x4000_0000` when
      `Status.ERL = 0`, `VA` when `ERL = 1` (§4.7, p.31); kseg0 and kseg1 both `VA[28..0]`, the
      low 512 MB (§4.6/Table 4.3, p.30-31; A.1.1: "they both map to the low 512MB"); kseg2
      (sseg/ksseg) and kseg3 identity. So kseg0 and kseg1 alias (`kseg1_store_visible_through_kseg0`),
      and physical `0x2000_0000`-`0x3FFF_FFFF` is reachable only through kuseg with `ERL = 1`
      ("inaccessible when the ERL bit is off", p.314).
    - `translate` is the manual's `AddressTranslation(vAddr, IorD, LorS)` (MD00086 Vol II-A Rev
      6.06 §2.2.2.2.2, Figure 2.17, p.19: "If the virtual address is in one of the mapped address
      spaces then the TLB or fixed mapping MMU determines the physical address"). It does not
      depend on `IorD`/`LorS` (Table 4.2 does not distinguish them); the caller picks AdEL/AdES.
    - `translate s va`: the address-error check first ("address error checking is still done
      before the translation process", A.1.1 p.313): in User Mode only useg is legal (Table 4.2,
      p.30), every other segment is an Address Error (AdEL for fetch/load, AdES for store,
      `BadVAddr` = the virtual address, §6.2.9 p.92-93). Kernel Mode references everything.
      Supervisor Mode does not exist ("Supervisor Mode is not supported with a Fixed Mapping
      MMU", p.313), so `0xC000_0000`-`0xDFFF_FFFF` is just kseg2 to the kernel.
    - **No TLB exception can occur**: there is no TLB (Refill/Invalid/Modified/XI/RI are TLB-match
      conditions, §6.2.10-6.2.14, p.93-96), and the Fixed Mapping MMU has "no memory protection
      beyond what is provided by the address error checks" (A.1, p.313).
    - **No Bus Error** (pin): every physical byte exists; a never-written byte reads 0 (item 6).
      Bus Error "occurs when ... [a bus] request is terminated in an error" (§6.2.16, p.97): a
      property of the system, which this model's system never produces.
    - **Cacheability** (`Config.K0`, `K23`, `KU`; Table A.2 p.317) selects nothing: no caches.
      `K23`/`KU` reset "Undefined" (p.233), pinned to 2 like `K0`. The manual is inconsistent on
      their compliance level: Table 9.64 (p.233) "Optional", Table A.2 (p.317) "Required"; both are
      R/W here, which satisfies either.
    - `Config1.MMU Size - 1` = 0 (pin): p.237 defines the field as "Number of entries in the TLB
      minus one" and says only that "The value zero is implied by ConfigMT having a value of
      ‘none’"; it is silent for `MT = 3`, which has no TLB.
    - **Fetch from kuseg with `ERL = 1`** is UNDEFINED ("The operation of the processor is
      UNDEFINED if the ERL bit is set while the processor is executing instructions from kuseg",
      A.1.2 p.316). Pin: the fetch is translated like data (identity); it neither halts nor hangs
      (MD00086 Vol II-A Rev 6.06 §1.2.2, p.4).
    - **Manual inconsistency**: Figure A.2 (p.316, "Memory Mapping when ERL = 1") draws kseg1's
      arrow to the "Unmapped" physical block `0x8000_0000`-`0xBFFF_FFFF`, while Table A.1
      (p.313, one cell for both ERL columns: kseg1 → `0x0000_0000`-`0x1FFF_FFFF`) and the A.1.1
      text ("Kseg0 and Kseg1 addresses ... both map to the low 512MB") map kseg1 to the low 512 MB
      regardless of ERL. The model follows the table and the text.
    - `SYNCI`'s optional AdEL for kernel addresses stays unraised ("It is implementation dependent
      whether such an exception does occur", SYNCI p.412): from User Mode a `synci` of a kernel
      address is a no-op (pin). `PREF`/`PREFX` never take address exceptions (PREF p.321).
    - `LL`/`SC` compare the **virtual** address (`llAddr`): the RMW sequence "must use the same
      address in the LL and SC. The address is the same if the virtual address, physical address,
      and cacheability & coherency attribute are identical" (SC p.348), so an `sc` through the
      other kseg0/kseg1 alias of the `ll`'s address fails — one permitted outcome.
    - **Loader and environment** (item 25): images are placed at `Env.loadAddr va =
      fixedMappingPA false va`; `Specs/Loader.lean` proves a fetch or load of an image address then
      returns the image word (`load_readMemWord`, `load_step_fetches_image`,
      `loadAtReset_readMemWord_kseg`). A reset-time program (`MipsRun --reset`) must clear `ERL`
      before it uses kuseg: its kuseg words are placed for `ERL = 0`.
    - **QEMU** (`tests/oracle/mmu_*`): QEMU's 24Kf has a TLB, so its kuseg is TLB-mapped and the
      `+ 0x4000_0000` kuseg offset is not observable there; kseg0/kseg1 aliasing, the `ERL = 1`
      kuseg identity map and the User-Mode Address Errors are, and agree.

28. **Timer and hardware registers (wave 5: `Count`, `Compare`, `Cause.TI`/`DC`/`IP7`, `HWREna`,
    `RDHWR`).** `step s = timerTick (stepCore s)` (`Step.lean`): the instruction (or, since wave 6, an
    interrupt entry or a standby step: item 29), then the timer.
    - **Count rate (pin).** "The Count register acts as a timer, incrementing at a constant rate,
      whether or not an instruction is executed ... The rate at which the counter increments is
      implementation-dependent" (MD00090 Vol III Rev 6.02 §9.27, p.183). The model increments
      `Count` by one on **every `step`** — an ordinary instruction, a branch, a step that takes an
      exception — modulo 2^32 (`step_count_advances`). One step is the model's cycle, so `CCRes`
      (`rdhwr` 3, "the number of cycles between update of the register", MD00086 Vol II-A Rev 6.06,
      RDHWR, p.332) reads 1. QEMU's Count follows virtual time and its `CCRes` is 2: not comparable
      (the oracle tests freeze `Count` with `DC = 1` or compare only flags).
    - **`Cause.DC = 1`** "Disable counting of Count register" (Table 9.52, p.210; reset 0, §6.2.5
      p.90): `Count` does not move while `DC = 1` (`step_count_stopped`); it is written and read
      normally. The match test (next point) is still made on every step.
    - **Order within a step (pin).** The instruction reads the `Count` the step started with
      (`mfc0 $9`, `rdhwr 2`); the timer then advances the `Count` the instruction left. So `mtc0 $9`
      with `v` leaves `Count = v + 1` (or `v` with `DC = 1`), and `mtc0 $13` that sets or clears
      `DC` takes effect in the same step (`mtc0_count_spec`).
    - **Timer interrupt request.** "When the value of the Count register equals the value of the
      Compare register, an interrupt request is made ... visible to software via the CauseTI bit"
      (§9.30, p.187): after every step, `Count = Compare` implies `Cause.TI = 1`
      (`step_timer_match_sets_ti`); `TI` then stays set until software writes `Compare` ("Writing
      a value to the Compare register, as a side effect, clears the timer interrupt", p.187;
      `mtc0_compare_clears_ti`). A write of `Compare` equal to the new `Count` is matched by the
      same step's tick. Writing `Count` does not by itself clear `TI`. `TI` is held in its own
      field (`State.cp0TimerInt`); `mtc0 $13` cannot write it (read-only, Table 9.52, p.209).
    - **IP7 (pin of `IntCtl.IPTI = 7`).** "In Release 2 ... combined in an implementation-dependent
      way with a hardware or software interrupt" (§9.30, p.187); `IntCtl.IPTI` "specifies the IP
      number to which the Timer Interrupt request is merged" (§9.33, Table 9.48, p.199); Table 6.2
      (§6.1.1.1, p.73) lists "Timer Interrupt" under HW5, "CauseIP7 and StatusIM7". The model merges
      the request into `IP7`: `mfc0 $13` reads `Cause | hw<<10 | TI<<30 | TI<<15` (`causeValue`).
      `IntCtl` (wave 6) reads `0xE000_0000`, `IPTI = 7`; QEMU 24Kf's reads the same
      (`tests/oracle/irq_timer.asm`, PASS).
    - **The hosted services do not advance the timer.** A `syscall` that `Env.hostStep` serves (item 25)
      is an environment action replacing a processor step, not a step: `Count` is unchanged by it.
    - **Interrupt delivery** (wave 6, item 29): with `Status.IM7 = 1`, `IE = 1`, `EXL = ERL = 0` the
      request is taken as the Interrupt exception at the start of the next step
      (`timer_requests_interrupt`, `step_interrupt`; `tests/oracle/irq_timer.asm`).
    - **Reset values (pins).** `Count`, `Compare`, `Cause.TI`: reset state "Undefined" (Tables 9.44
      p.183, 9.46 p.187, 9.52 p.209) and not in the Reset Operation (§6.2.5, p.89-90): the Reset
      exception keeps them; `powerOnState` pins them to 0/0/false (hosted start the same).
      `HWREna ← 0` (§6.2.5, p.89).
    - **`HWREna`** (CP0 7,0; §9.23, Table 9.39, p.175): bits 3..0 (the implemented `rdhwr` registers)
      read/write; "If RDHWR register ‘n’ is not implemented, bit ‘n’ of this field returns a zero and
      is ignored on a write", so all other bits read 0 (`hwrena_write_masked`). QEMU 24Kf agrees
      (`rdhwr_kernel`).
    - **`RDHWR`** (MD00086 Vol II-A Rev 6.06, p.332-334): registers 0 `CPUNum` = `EBase.CPUNum` = 0,
      1 `SYNCI_Step` = 0 ("zero if no caches need be synchronized": no caches, `Config1.IL = DL = 0`),
      2 `CC` = `Count`, 3 `CCRes` = 1. Access "is enabled if Coprocessor 0 is enabled, or if the
      corresponding bit is set in the HWREna register. If access is not allowed or the register is not
      implemented, a Reserved Instruction Exception is signaled" (p.333): Kernel Mode or `CU0 = 1`, or
      the `HWREna` bit; otherwise Reserved Instruction (never Coprocessor Unusable). Registers 4, 5
      (Release 6), 6..28 (reserved), 30, 31 (implementation-dependent, none here): Reserved
      Instruction. A nonzero bits 10..6 (the Release 6 `sel`) does not decode (item 11).
    - **UserLocal / `rdhwr 29` absent; Config2 and Config3 present (F17, wave 12).**
      UserLocal is "Pre-Release 6: Recommended" (§9.11, p.143), not required, and "Prior to Release 6,
      this register only exists if the Config3ULRI register field is set" (p.143). Config3 is
      "Required if any optional feature described by this register is implemented: Release 2 of the
      Architecture, the SmartMIPS™ ASE, or trace logic" (§9.48, p.245): the model is Release 2, so it
      has Config3 (16,3) = 0, read-only ("All fields in the Config3 register are read-only", p.245);
      `ULRI` = 0, hence `rdhwr 29` → Reserved Instruction in every mode. Config2 is "Required if a
      level 2 or level 3 cache is implemented, or if the Config3 register is required" (§9.47, p.241):
      (16,2) = `0x8000_0000` (`M` = 1 "If the Config3 register is implemented", Table 9.66 p.241; no
      L2/L3 cache; `TU`/`SU` not implemented, "read as zero and be ignored on write", p.241-242), and
      `Config1.M` = 1 ("If the Config2 register is implemented, this bit should read as a 1", Table
      9.65, p.237). `Config3.M` = 0: no Config4 ("If the Config4 register is not implemented, this bit
      should read as a 0", p.245; the Release 2 manual: "With the current architectural definition, this
      bit should always read as a 0", MD00090 Vol III Rev 2.50 §8.29 p.110), although Config4's own
      compliance line repeats "Release 2 of the Architecture" (§9.49, p.253): every Config4 field
      describes a feature the model does not have (COMPLIANCE.md header note 1, A9.49). Before wave
      12 the chain stopped at `Config1.M = 0` and (16,2)/(16,3) raised Reserved Instruction.

29. **Interrupts, `IntCtl`, GPR shadow sets (wave 6, COMPLIANCE F13/F16).**
    - **Mode.** Interrupt compatibility mode only: "A compatible implementation of Release 2 of the
      Architecture must implement interrupt compatibility mode, and may optionally implement one or both
      vectored interrupt modes" (MD00090 Vol III Rev 6.02 §6.1.1, p.72); VI and EIC are announced by
      `Config3.VInt`/`VEIC` (p.72), and the model's Config3 reads 0 (`VInt` = `VEIC` = 0, item 28).
    - **When.** Request `i` = `Cause.IPi AND Status.IMi` (Table 6.2, p.73; `interruptRequests`); "An
      interrupt is only taken when ... A specific request for interrupt service is made ... The IE bit in
      the Status register is a one ... The DM bit in the Debug register is a zero (for processors
      implementing EJTAG) ... The EXL and ERL bits in the Status register are both zero" (§6.1, p.72; no
      EJTAG here). `interruptTaken`, `interruptTaken_iff`, `no_interrupt_ie0/exl/erl/masked`.
    - **Priority / place.** Checked at the start of `step` (`stepCore`), before the fetch: Interrupt is
      above every fetch, instruction-validity, execution and data exception in Table 6.6 (p.83-84), and
      an asynchronous exception is "the highest priority relative to the next instruction" (Table 6.7,
      p.84). The instruction at `pc` is not executed (`step_interrupt`). Reset, NMI, Machine Check and
      the debug exceptions above it are not raised by `step`.
    - **Entry.** The general exception processing (§6.2.3, p.86-88) with `ExcCode = Int` (0, Table 9.53,
      p.212): `EPC` = the instruction not executed, or the branch with `Cause.BD = 1` when it is in a
      delay slot (Table 6.11, p.87; MD00090 §9.38 p.217: "For asynchronous (imprecise) exceptions, EPC
      contains the address of the instruction at which to resume execution"); the pending branch is
      abandoned, so `eret` re-executes the branch (`takeInterrupt_not_in_delay_slot`,
      `takeInterrupt_in_delay_slot`). `Cause.IP` is not latched: it shows the current requests
      ("Additional State Saved: CauseIP indicates the interrupts that are pending", §6.2.26, p.102; "The
      current interrupt requests are visible via the IP field in the Cause register on any read of the
      register", §6.1.1.1, p.73).
    - **Vector.** `Cause.IV = 0`: general vector, offset `0x180`; `IV = 1`: offset `0x200` (§6.2.26,
      p.102; §6.2.3 Operation p.88: "if (StatusBEV = 1) or (IntCtlVS = 0) then vectorOffset ← 0x200");
      `0x8000_0200` (BEV = 0, EBase at reset) or `0xBFC0_0400` (BEV = 1) (Table 6.10, p.86;
      `interruptVector_*`). This is conforming text, not a pin: Table 6.1 (p.72) has the row "x x =0 x x
      Compatibility" (`IntCtlVS = 0`), its "Not Allowed" row (p.73) is for `IntCtlVS ≠ 0` with
      `VInt = VEIC = 0`, and §6.1.1.1 (p.73) dispatches compatibility mode through `0x200` when
      `CauseIV = 1` (COMPLIANCE C.2). (An earlier version of this note read the p.73 row as `IntCtlVS = 0`
      and claimed a manual self-contradiction: that was a text-extraction artefact, the "≠" glyph is lost
      by `pdftotext`; checked against the PDF page image.) QEMU 24Kf agrees (`tests/oracle/irq_cause_iv_vector.asm`, PASS).
    - **Sources.** Software `IP1..IP0` (`mtc0 $13`; `mtc0_cause_requests_software_interrupt`), the timer
      (`TI` into `IP7`, item 28; `timer_requests_interrupt`) and the six hardware lines `HW5..HW0`
      (`State.hwInt`, in `IP7..IP2`; `hwInt_requests_interrupt`). **Decision on the hardware lines:**
      they are modeled as a State field that `step` reads and never writes (`step_hwInt`), so the
      processor's interrupt logic is the manual's complete Table 6.2, and who drives the lines is the
      environment's business (`Env.lean`). **Environment property:** this environment connects no
      device: every state it builds has `hwInt = 0` and nothing changes it. (QEMU's Malta raises HW0 on
      its own; the oracle tests keep `IM2 = 0` and the harness masks `IP7..IP2` in the comparison.)
    - **Hazards (pin).** `mtc0` to `Status` (IM, ERL, EXL, IE) or `Cause` (IP1..0), `ei`, `di` change the
      interrupt state; "An EHB, executed after one of these fields is modified by the listed instruction,
      makes the change to the interrupt state visible no later than the instruction following the EHB"
      (§6.1.2.1, Table 6.5, p.82). The model makes it visible at once: the next step's check sees it
      (`ehb` is `sll $0, $0, 3`, a no-op). QEMU 24Kf takes the interrupt at the same place in
      `tests/oracle/irq_software.asm` (PASS).
    - **`di`/`ei`/`eret`** are unchanged: they write `Status.IE`/`EXL`/`ERL`, which the next step's
      check reads. The general exception sequence sets `EXL`, so a handler runs with interrupts disabled
      until it clears `EXL` or executes `eret`.
    - **`IntCtl` (12,1)** = `0xE000_0000` (`intCtlValue`, Table 9.48 p.199-201): `IPTI = 7` (pin, item 28),
      `IPPCI = 0` (`Config1.PC = 0`, p.200), `IPFDC = 0` (no EJTAG FDC, p.200), `VS = 0` ("ignored on write
      and reads as zero" without VI/EIC, p.201). No field is writable: `mtc0` is ignored.
    - **`SRSCtl` (12,2)** = 0 (`srsCtlValue`, Table 9.49 p.203-204): `HSS = 0` ("only the normal GPRs are
      implemented"), `EICSS = 0`, `ESS = PSS = CSS = 0`. **Pin:** `mtc0` to it is ignored: `ESS`/`PSS` are
      R/W but "The operation of the processor is UNDEFINED if a value larger than the one in this field is
      written", so 0 is the only value they can hold. Exception entry and `eret` never change it (their
      shadow-set steps require `SRSCtlHSS ≠ 0`, §6.2.3 p.88, ERET p.177; and with every field 0 they would
      change nothing). QEMU 24Kf reads 0 too (`irq_timer`, `rdpgpr_wrpgpr`).
    - **`SRSMap` (12,3)** is not implemented: required only "if Additional Shadow Sets and Vectored
      Interrupt Mode are Implemented" (§9.35, p.207), and "If SRSCtlHSS is zero, the results of a software
      read or write of this register are UNPREDICTABLE" (p.207). **Pin:** the access does not decode and
      raises Reserved Instruction ("UNPREDICTABLE operations may cause arbitrary exceptions", MD00086 Vol
      II-A Rev 6.06 §1.2.1, p.3); not in the QEMU oracle.
    - **`RDPGPR`/`WRPGPR`** (MD00086 Vol II-A Rev 6.06 p.335, p.444; "MIPS32 Release 2"; "In
      implementations prior to Release 2 of the Architecture, this instruction resulted in a Reserved
      Instruction exception"): implemented on shadow set 0 = the normal GPRs ("The normal GPRs are
      logically considered shadow set zero", MD00090 Vol III §7, p.103), `PSS = 0`, so both are `$rd ← $rt`.
      QEMU 24Kf agrees (`tests/oracle/rdpgpr_wrpgpr.asm`, PASS).
    - **Theorem statements.** Every per-instruction theorem `step s = timerTick (…)` now assumes
      `hexec : executesInstr s = true` (no interrupt is taken and the processor is not in standby): with
      interrupts the equation is false in the other states. This hypothesis was added to 68 trusted
      statements (a weakening forced by the model change; `store_changes_next_instruction`, a two-step
      statement, also assumes `executesInstr (step s) = true`; the global theorems — `$zero`,
      register-file sizes, `Count` advance, `TI` — hold for every state and did not get it).

30. **Signs of exact zero results (wave 11, a pin where the manuals are silent).** The MIPS manuals
    do not give the sign of an exactly zero sum, difference, product or quotient, nor of `CVT.S.W` /
    `CVT.D.W` of 0. MD00082 Vol I-A Rev 6.01 §6.2 (p.77, footnote 1) names IEEE Standard 754-1985 as
    "the IEEE standard" of the chapter; the model and the reference (`Semantics/FpOpsSpec.lean`,
    `Format.AddSpec`, `MulSpec`, `DivSpec`, `FromIntSpec`) follow it. The published standard is
    not vendored (sold by IEEE). The rules are verified against the published **IEEE Std 754-2019** (the owner's
    licensed copy, local-only, `manuals/LOCAL-SOURCES.md`; `mipsdoc.py section ieee 6.3`), §6.3 "The sign
    bit", printed p.50: "the sign of a product or quotient is the exclusive OR of the operands' signs" and "These
    rules shall apply even when operands or results are zero or infinite."; "the sign of that sum (or difference)
    shall be +0 under all rounding-direction attributes except roundTowardNegative; under that attribute, the sign
    of an exact zero sum (or difference) shall be −0. However, under all rounding-direction attributes, when x is
    zero, x + x and x − (−x) have the sign of x."; "Except that squareRoot(−0) shall be −0, every numeric
    squareRoot result shall have a positive sign."; and for the integer conversion §5.4.1 (p.33,
    formatOf-convertFromInt): "Integer zeros without signs are converted to +0." The model agrees with every one
    of these (verification table below). Only "verified against 2019": the MIPS manual names the 1985 standard, whose
    text is not available here, so no claim is made that these rules are unchanged since 1985. The earlier check
    against the public P754 Draft 1.2.5 §8.3 p.44 (`p754`) said the same. The rule: a sum of operands of opposite (effective)
    signs, or a difference of operands of like signs, that is exactly zero is `+0`, except `−0` when
    rounding toward −∞ (`FCSR.RM = 3`); `x + x` and `x − (−x)` keep the sign of `x` (also for `x = ±0`);
    the sign of a zero product or quotient is the exclusive or of the operands' signs; an integer 0
    converts to `+0`. `SQRT(−0) = −0` is the manual's own rule (MD00086 Vol II-A Rev 6.06, SQRT.fmt,
    p.382: "If the value in FPR fs corresponds to – 0, the result is – 0"). Proved for every operand:
    `Trusted.f32Add_spec` … `Trusted.w32ToF32_spec` (docs/PROOF-NOTES.md, "Wave 11").

    **Verification against IEEE Std 754-2019** (local copy; all page numbers are printed pages; every row looked
    up with `mipsdoc.py section ieee X`). "Agrees" = the proved spec in `Semantics/FpOpsSpec.lean` and the model
    behave as the clause says.

    | Pin / definition | 754-2019 clause, page | Result |
    |---|---|---|
    | exact-zero sum/difference sign (`+0`, `−0` in RM; `x+x`, `x−(−x)` keep sign of x) | §6.3, p.50 | agrees (`AddSpec`, `Exact.add`) |
    | zero product / quotient sign = XOR | §6.3, p.50 (and §7.3 p.53 for ±∞) | agrees (`MulSpec`, `DivSpec`) |
    | `SQRT(−0) = −0`, other numeric roots positive | §6.3, p.50 | agrees (`SqrtSpec`; also MD00086 SQRT.fmt p.382) |
    | integer 0 → `+0` | §5.4.1 convertFromInt, p.33 | agrees (`FromIntSpec`) |
    | conversion keeps the operand's sign (`±0`, `±∞`) | §6.3, p.50; §6.1 p.48 | agrees (`ConvertSpec`) |
    | correct rounding to RN / RZ / RP / RM, ties to even | §4.3 p.27, §4.3.1-4.3.2 p.27, §4.3.3 p.28 (RN is the default) | agrees (`CorrectlyRounded`); roundTiesToAway is not required for binary |
    | overflow default results (RN/RZ/RP/RM, sign of the intermediate result), flags Overflow + Inexact | §7.4, p.53 | agrees (`overflowResult`, `Signaled`) |
    | underflow: tiny non-zero result, flag only if inexact (default handling) | §7.5, p.53 | agrees (`Signaled`; with the Underflow enable MIPS signals on tininess alone: the trap case, §7.5 "shall be signaled when a tiny non-zero result is detected") |
    | tininess "after rounding" (MIPS MD00082 §6.7.2.3 p.101 pins it) | §7.5 a), p.53: "The implementer shall choose how tininess is detected, but shall detect tininess in the same way for all operations in radix two" | agrees: both options (a) after / (b) before rounding are allowed; the model uses (a) uniformly (`RoundSpec.tiny`). FCSR.FS = 1 flushing detects tininess before rounding (MD00082 §6.7.2.4 p.102): a MIPS non-IEEE mode, outside 754's "default handling ... shall always deliver a rounded result" (§7.5 p.53) |
    | Inexact when the rounded result differs from the unbounded one | §7.6, p.54 | agrees (`RoundSpec.inexact`) |
    | Invalid: SNaN operand, 0×∞, ∞−∞, 0/0, ∞/∞, sqrt of a negative number | §7.2 a) b) d) e) g), p.52 | agrees (`MulSpec`, `AddSpec`, `DivSpec`, `SqrtSpec`; `SQRT(−∞)` is Invalid) |
    | Division by zero: finite non-zero / 0 → ∞ with sign XOR | §7.3, p.53 | agrees (`DivSpec`) |
    | float → integer: Invalid for NaN, ∞, out-of-range after rounding; Inexact for rounded results | §5.8, p.39-40 ("convertToIntegerExact..." signal inexact) and §7.2 j), p.52 | agrees (`ToWordSpec`; CVT.W/ROUND.W/... are the *Exact* family). The delivered value `0x7FFFFFFF` is not specified by 754 ("cannot otherwise be indicated"): it is the MIPS rule |
    | comparisons: unordered with a NaN; `+0 = −0`; SNaN signals Invalid; quiet vs signaling predicates (cond3) | §5.11, p.43; §7.2 i) k), p.52 | agrees (`CompareSpec`) |
    | infinities exact, no exception | §6.1, p.48 | agrees |
    | NaN: Invalid result is a quiet NaN; quiet-NaN inputs signal nothing; payload of an input NaN "should" be kept | §6.2, p.48; §6.2.3, p.49 | agrees (`NaNResult`); which operand supplies the payload is unspecified by 754 ("This standard does not specify which of the input NaNs will provide the payload", §6.2.3 p.49) and by MIPS (item 13) |
    | `cvt.s.d` / `cvt.d.s` of a QNaN keeps the leading payload bits; widen-then-narrow keeps the payload | §6.2.3, p.49 (quoted: "should not change the quiet NaN payload in any way except to make it canonical") | agrees (item 22); all binary encodings are canonical (§3.4, p.19) |
    | `ABS.fmt`/`NEG.fmt` of a NaN signal Invalid (`FIR.Has2008 = 0`), reading A′ (item 21) | §5.5.1, p.35: "signal no exception" and "treat floating-point numbers and NaNs alike" | **differs by design, MIPS-specified**: 754-2019 makes abs/negate quiet; the MIPS pages (ABS.fmt p.32, NEG.fmt p.307) say "If FIRHas2008=0 or FCSRABS2008=0 then this operation is arithmetic", so the model follows MIPS. Not a model error (the manual is explicit), but it is a place where legacy MIPS is not 754-2019 |
    | legacy NaN encoding (`Has2008 = 0`: fraction MSB 1 = signaling) | §3.4 a), p.19: d1 "shall exclusively distinguish between qNaN and sNaN"; §6.2.1, p.48: a quiet NaN "should be encoded with the first bit (d1) ... being 1" | the legacy MIPS polarity is the opposite of the 754-2019 preferred encoding; it satisfies the "shall" (d1 distinguishes) and departs only from a "should" (MD00082 Table 6.2 p.80; item 13) |
    | `MADD`/`MSUB`/`NMADD`/`NMSUB` as separate multiply and add (two roundings), not fusedMultiplyAdd | §5.4.1 fusedMultiplyAdd (single rounding), §6.3 p.50 and §7.2 c) p.52 describe the fused operation | not the 754 fused operation by the MIPS manual's own words ("as if separate ... instructions were executed", MADD.fmt p.256), so the FMA clauses do not apply to them |

## 10. Known oracle deviations (the manual wins)

Every `# oracle: expect-deviation` in `tests/oracle/*.asm`, plus the one declared for
`tests/asm/fp_legacy_nan` in `ASM_DIRECTIVES` of `scripts/oracle.py`, is a place where the QEMU
24Kf (`qemu-system-mips -M malta -cpu 24Kf`) differs from the manual and the model follows the
manual. The oracle fails on an undeclared mismatch and on a declared deviation that no longer
occurs. Citations are those in the directives; each page was re-checked with `mipsdoc.py`.

| Test | Where QEMU differs | Manual |
|---|---|---|
| `exc_sc_misaligned` | a misaligned `sc` fails silently (rt ← 0) instead of taking Address Error | MD00086 Vol II-A Rev 6.06, SC, p.349 (Exceptions: Address Error) |
| `exc_lwxc1_misaligned` | the access is performed without an exception | LWXC1 p.254: "An Address Error exception occurs if EffectiveAddress1..0 ≠ 0" |
| `exc_ldxc1_misaligned` | same | LDXC1 p.218 (EffectiveAddress2..0 ≠ 0) |
| `exc_swxc1_misaligned` | same | SWXC1 p.406 (EffectiveAddress1..0 ≠ 0) |
| `exc_sdxc1_misaligned` | same | SDXC1 p.364 (EffectiveAddress2..0 ≠ 0) |
| `fp_flush_to_zero_fs` | with `FCSR.FS = 1` a flushed tiny result leaves Underflow/Inexact clear | MD00082 Vol I-A Rev 6.01, §6.7.2.4, p.102: flushing of tiny non-zero results causes Inexact and Underflow |
| `fp_abs_neg_nan` | `abs.s` of the QNaN `0xffa00000` and `neg.s` of the QNaN `0x7fa00000` (MD00082 Vol I-A Rev 6.01 Table 6.2, p.80): QEMU and the model return the same sign-changed values (`0x7fa00000`, `0xffa00000`); QEMU leaves FCSR at 0, the manual says Invalid is signaled (model `0x00010040`) | MD00086 Vol II-A Rev 6.06, ABS.fmt p.32 / NEG.fmt p.307 (item 21, reading A′) |
| `fp_madd_separate_ops` | QEMU returns the default QNaN for any NaN operand of the multiply-add family (the model an operand QNaN: `0xff800001` for NMADD, `0x7f800002` for MADD); QEMU's NMADD negate of the QNaN sum signals nothing (the model: Invalid, reading A′ of item 21). The Cause of the untrapped instruction (`0x15054`: the union of the multiply's O\|I and the add's V) matches since Wave 12a | MD00086 Vol II-A Rev 6.06, NMADD.fmt p.308, NEG.fmt p.307; MD00082 Vol I-A Rev 6.01 §6.3.1.5, p.82 (items 13, 21) |
| `fp_madd_mul_trap` | with `Enables.O`, the multiply step overflows: QEMU traps with Cause `V\|O\|I` (it also ran the add), the model with the multiply's Cause `O` (FCSR `0x4200`): the trapping multiply ends the instruction (re-evaluated in Wave 12a: item 13, "Multiply-add family", reading of a trapping multiply) | MADD.fmt p.256 ("as if separate ... instructions were executed"); MD00082 Vol I-A Rev 6.01 Table 6.8 `Cause`, p.94, and §6.7.1, p.98-99 (item 13) |
| `fp_trap_enabled_handler` | with the Overflow enable set, QEMU also sets `Cause.I` | MD00082 Vol I-A Rev 6.01, §6.7.2.6, p.102: Inexact is signaled on overflow only "without an overflow trap" |
| `fp_nan_propagation_quiet` | `add/sub/mul/div.s` with exactly one QNaN operand (`0x7fa00003`) and a number: QEMU returns the default QNaN `0x7fbfffff`, the model the operand QNaN (8 result slots); the slots with two NaN operands stay `unpredictable` | MD00082 Vol I-A Rev 6.01, §6.3.1.5, p.82: "When possible, this QNaN result is one of the operand QNaN values" (possible here: a single QNaN operand) |
| `fp_underflow_enabled_exact` | with `Enables.U` set, an exact tiny product (`mul.s` 0.5 × 2^-126, `mul.d` 0.5 × 2^-1022) does not trap in QEMU (it writes the denormal, FCSR unchanged); the model traps (FPE, `Cause.U`, FCSR `0x2100` at the trap, destination not written); the inexact tiny control traps on both | MD00082 Vol I-A Rev 6.01, §6.7.2.3, p.101: "When an underflow trap is enabled (through the FCSR Enable field bit), underflow is signaled when tininess is detected regardless of loss of accuracy" |
| `fp_abs_neg_clear_cause` | `abs.s`/`abs.d`/`neg.s`/`neg.d` of a non-NaN operand after an inexact `mul.s`: QEMU keeps `Cause.I` (FCSR `0x1004`), the model clears Cause (`0x0004`); the `mov.s` control (non-arithmetic, MOV.fmt p.275) keeps it on both | MD00086 Vol II-A Rev 6.06, ABS.fmt p.32 / NEG.fmt p.307 ("If FIRHas2008=0 or FCSRABS2008=0 then this operation is arithmetic"); MD00082 Vol I-A Rev 6.01 §6.7.1, p.99 ("The Cause bits are written during each floating point arithmetic operation ... otherwise it is set to 0") |
| `exc_delay_slot_never_taken_branch` | an exception (`break`, `teq`, misaligned `sh`) in the delay slot of a statically never-taken branch (`bne r,r`, `bgtz $zero`, `bltz $zero`, `bne $zero,$zero`): QEMU reports `Cause.BD = 0` and EPC = the slot (it translates the branch as a NOP); the model `BD = 1`, EPC = the branch; dynamically not-taken controls (`beq`, `blez`) agree | MD00090 Vol III Rev 6.02, §9.36 Cause, p.209 (BD: "Indicates whether the last exception taken occurred in a branch delay slot"), §9.38 EPC, p.217 ("the virtual address of the immediately preceding branch or jump instruction, when the exception causing instruction is in a branch delay slot"); MD00082 Vol I-A Rev 6.01 §5.3.2, p.61 ("Typical delayed branches execute the delay-slot instruction, whether or not the branch was taken"); MD00086 Vol II-A Rev 6.06 BNE p.103, BGTZ p.88, BLTZ p.97 |
| `rdhwr_kernel` | `rdhwr $t9, $29` in Kernel Mode returns a value (no exception) although QEMU's 24Kf reads `Config3 = 0` (`ULRI = 0`, UserLocal not implemented) | MD00086 Vol II-A Rev 6.06, RDHWR, p.333 ("If access is not allowed or the register is not implemented, a Reserved Instruction Exception is signaled"); MD00090 Vol III Rev 6.02 §9.11, p.143 ("Prior to Release 6, this register only exists if the Config3ULRI register field is set") |
| `tests/asm/fp_legacy_nan` (via `ASM_DIRECTIVES`) | `abs.s` of a NaN is not arithmetic in QEMU; QEMU returns the default QNaN for `QNaN + 1.0` (one QNaN operand: the operand QNaN is mandatory, as `fp_nan_propagation_quiet`) | ABS.fmt p.32; MD00082 Vol I-A Rev 6.01 §6.3.1.5, p.82 ("When possible, this QNaN result is one of the operand QNaN values"; with two NaN operands which one is returned is not specified, `fpr:f2` stays `unpredictable`) |

Declared `unpredictable` fields (not deviations): `div` by zero `HI`/`LO` (DIV, p.165), `mul` `HI`/`LO`
(MUL, p.299), `sc` without a preceding `ll` (SC, p.348), `recip`/`rsqrt` accuracy (RECIP.fmt p.336), which NaN
is returned for two NaN operands (MD00082 §6.3.1.5, p.82), and the implementation-defined identification
registers (PRId, Config, Config1, FIR), the implementation-dependent `rdhwr` values `SYNCI_Step` and `CCRes`
(MD00090 Vol III Rev 6.02 Table 9.40, p.176; QEMU 24Kf: 32 and 2, the model: 0 and 1), and `Cause` in
`timer_count_compare` (the Malta board raises hardware interrupt 0 after some milliseconds; the model has no
interrupt inputs).
The MARS-side deviations are item 14 above and §9 items 1, 3, 4, 5.

**Possible future work.** Emulator-compatibility toggles (a mode in which the model reproduces QEMU's or
MARS's behaviour for these cases) could be added later; none exist, and the default is always the manual.

## 11. The manual spec's implementation constants and choices (`Manual.modelImpl`, `Manual.modelOracle`)

The independent spec (`Semantics/Manual/`, `docs/MANUAL-SPEC.md`) takes the implementation's
constants (`Impl`) and one resolution of every manual choice (`Oracle`) as arguments. The model's
values (`Semantics/Manual/Choices.lean`), each the spec-side statement of a pin recorded above:

| Field | Model's value | Manual text | Pin |
|---|---|---|---|
| `Impl.CountIncrement` | 1 per instruction time | "The rate at which the counter increments is implementation-dependent" (MD00090 Vol III Rev 6.02 §9.27, p.183) | `timerTick`, one per `step` |
| `Impl.PRId` | `0x0001_0000` | §9.40, Table 9.57, p.221 | `prIdValue` |
| `Impl.ConfigFixed` | `0x8000_8580` | §9.45, Table 9.64, p.233-235 | `configValue` |
| `Impl.Config1` | `0x8000_0001` | §9.46, Table 9.65, p.237-240 | `config1Value` |
| `Impl.Config2` | `0x8000_0000` | §9.47, Table 9.66, p.241-243 | `config2Value` |
| `Impl.Config3` | 0 | §9.48, Table 9.67, p.245-251 | `config3Value` |
| `Impl.IntCtl` | `0xE000_0000` (`IPTI = 7`, `VS = 0`) | §9.33, Table 9.48, p.199 | `intCtlValue` |
| `Impl.SRSCtl` | 0 | §9.34, Table 9.49, p.203 | `srsCtlValue` |
| `Impl.CCRes`, `Impl.SYNCIStep` | 1, 0 | MD00086 Vol II-A Rev 6.06, RDHWR, Table 5.4, p.332 | `ccResValue`, `synciStepValue` |
| `Impl.WaitRestartsOnNotEnabled` | true | "It is implementation-dependent whether the pipeline restarts when a non-enabled interrupt is requested" (WAIT, p.442) | `standbyStep` |
| `Oracle.ctiInSlot` | Reserved Instruction (PAUSE: executes as its `SLL`) | "Processor operation is UNPREDICTABLE if a control transfer instruction (CTI) is placed in the delay slot" (BEQ, p.72) | §9 item 1 |
| `Oracle.cp0Undefined` | Reserved Instruction | "The results are UNDEFINED if coprocessor 0 does not contain a register as specified by rd and sel" (MTC0, p.290; MFC0, p.266) | `mtc0`/`mfc0` arms |
| `Oracle.storeClearsLL` | true (every store clears `LLbit`) | "A coherent store is executed between an LL and SC sequence on the same processor to the block ... (if Config5LLB=1; else whether such a store causes the SC to fail is not predictable)" (MD00086 Vol II-A Rev 6.06, SC, p.347), and for other blocks "the SC may fail where it could have succeeded" (p.347-348). The wording "the SC may succeed or it may fail" is MD00086 Rev 2.50, SC, p.243 (and SCE, Rev 6.06 p.351), not 6.06 SC | `State.llBit` |
| `Oracle.loadClearsLL` (7R) | false (no load clears `LLbit`) | "A load that executes on the processor executing the LL/SC sequence to the block ... will not cause the SC to fail (if Config5LLB=1; else such a load may cause the SC to fail)" (SC, p.347); p.347-348 for other blocks | `ll`/`sc`: loads do not touch `llBit` |
| `Oracle.ebaseWriteBEV0` (7R) | `.proceed`: the write takes effect | "The operation of the processor is UNDEFINED if the Exception Base field is written with a different value when StatusBEV is 0" (MD00090 Vol III Rev 6.02 §9.41, p.223) | `mtc0` to EBase writes regardless of `BEV` |
| `Oracle.unpredictableEncoding` (7R) | Reserved Instruction (after the coprocessor-usability check of the word's space) | a nonzero unnamed field ("Fields that contain zeros but are not named ... If such fields are set to non-zero values, the operation of the processor is UNPREDICTABLE", MD00086 Vol II-A Rev 6.06 §2.1.1, p.12), CLO/CLZ `rt ≠ rd` (p.134-135), EXT `lsb + msbd > 31` (p.183), INS `lsb > msb` (p.193), a JR/JALR hint other than 0 and `10000` (JR p.207, JALR p.196); "UNPREDICTABLE operations may cause ... arbitrary exceptions" (§1.2.1, p.3) | strict `decode` returns `none` for these words: Reserved Instruction |
| `Oracle.absNegNaN` (7R) | `.A'` | ABS.fmt p.32, NEG.fmt p.307, MD00082 §6.3.1.5 p.82 | §9 item 21 |
| `Oracle.cvtQNaNToD`, `Oracle.cvtQNaNToS` (7R) | the core's widening / narrowing of the payload (`Mips.Fp.f32ToF64`, `Mips.Fp.f64ToF32`) | "When possible, this QNaN result is one of the operand QNaN values" (MD00082 Vol I-A Rev 6.01 §6.3.1.5, p.82): not possible across formats | §9 item 22 |
| `Impl.recipS/D`, `Impl.rsqrtS/D` (7R) | `DIV.fmt` of `1.0`; `SQRT.fmt` then `DIV.fmt` (flags ORed), current FCSR environment | accuracy within 1 ULP (RECIP.fmt p.336) / 2 ULP (RSQRT.fmt p.343), rounding-mode dependence implementation dependent; the bounds are `Impl.RecipAccurate`/`RecipExact`/`RsqrtAccurate` (`Manual/Accuracy.lean`). Wave 12a: the Invalid Operation / Division-by-Zero conditions are constrained by operand class (`Impl.RecipFlags`: QNaN no condition, MD00082 Vol I-A Rev 6.01 §6.3.1.5 p.82; SNaN Invalid, §6.3.1.4 p.81; zero Division by Zero, §6.7.2.2 p.100; `RSQRT` of a negative non-zero operand Invalid, §6.7.2.1 p.100; otherwise neither, a subnormal operand with FS = 1 excepted, §6.7.2.4 p.102); Overflow, Underflow, Inexact are left free ("does not meet the accuracy specified by the IEEE 754 Floating Point standard") | §9 item 13 |
| `Impl.WF` (7R) | `modelImpl.WF` (theorem `Manual.modelImpl_WF`) | `SRSCtl.HSS = 0` ("only the normal GPRs are implemented", Vol III Table 9.49 p.203) and so `PSS = 0` (p.204); `IntCtl.VS = 0` without VI/EIC modes (Table 9.48, p.201) | no shadow sets, no vectored interrupts |
| `Oracle.causeCE` | 0 | "The CE field is loaded, but not defined, for any exception type other than a coprocessor unusable exception" (MD00090 Vol III Rev 6.02 §6.2.3, p.87) | `exceptionEntry` |
| `Oracle.resetUndefined` | keep, except `Config.K23 = KU = 2`, `LLbit = 0` | "only the following registers have defined state" (§6.2.5, p.89) | `resetException` |
| `Oracle.linkSourceIs31` (7B S3) | proceed: the condition is tested on the value `rs` had before the link, then `$ra` is linked | "GPR 31 must not be used for the source register rs ... The result of executing such an instruction is UNPREDICTABLE" (BLTZAL p.98, BGEZAL p.76, BLTZALL p.99, BGEZALL p.80) | §9 item 18 |
| `Oracle.jalrRsIsRd` (7B S3) | proceed: the target is read from `rs` before `rd` is written | "Register specifiers rs and rd must not be equal ... The result of executing such an instruction is UNPREDICTABLE" (JALR, p.196) | §9 item 18 |
| (removed in 7R) `Oracle.shadowSetUndefined` | — | replaced by `Impl.WF` (`HSS = PSS = 0`): RDPGPR p.335, WRPGPR p.444, ERET p.177 follow their Operation with shadow set 0 (`SGPR`) | `rdpgpr`/`wrpgpr`/`eret` arms |
| `Impl.FIR` (7B S4) | `0x0033_0000` (`S`, `D`, `W`, `L` = 1; `F64`, `PS`, `Has2008` = 0) | `FIR` is implementation-dependent, read by `CFC1 fs = 0` (MD00082 Vol I-A Rev 6.01 §6.5.1, Table 6.5, p.87-88; MD00086 Vol II-A Rev 6.06, CFC1, p.129-130) | §9 item 13 (`FIR.L`), `firValue` |
| `Oracle.fprOddRead` (7B S4) | the pair `(FPR[fpr+1], FPR[fpr])` (index mod 32) | `valueFPR <- UNPREDICTABLE` for `fpr` odd, D / UNINTERPRETED_DOUBLEWORD, FR = 0 (MD00086 Vol II-A Rev 6.06, Figure 2.22, p.22) | §9 item 13 ("an odd register number for a double") |
| `Oracle.fprOddWrite` (7B S4; an `Outcome` since 7R) | `.arbitrary`: `FPR[fpr] <- value31..0`, `FPR[fpr+1] <- value63..32` | `StoreFPR` with `fpr` odd: `UNPREDICTABLE` (Figure 2.23, p.22-23) | same |
| `Oracle.cfc1Unpredictable` (7B S4) | 0 | `CFC1` with `fs` naming no FP control register: "Prior to Release 6, the result is UNPREDICTABLE" (MD00086 Vol II-A Rev 6.06, CFC1, p.129-130) | §9 item 13 (`cfc1` of a nonexistent control register reads 0) |
| `Oracle.ctc1Unpredictable` (7B S4; an `Outcome` since 7R) | `.arbitrary` with: `fs` nonexistent: `FCSR` unchanged; reserved bits set: the page's write with the reserved bits ignored (`FCSR` bits 22..18 stay 0) | `CTC1` `UNPREDICTABLE` arms (MD00086 Vol II-A Rev 6.06, CTC1, p.149-150) | §9 item 13 (`ctc1` pins) |

7B S4 readings of the FPU pages (no model change): (1) the Release 5 `UFR`/`UNFR` and Release 6 `FRE`/`NFRE` aliases of `CFC1`/`CTC1` (`fs` = 1, 4, 5, 6; CFC1 p.129-130, CTC1 p.149-150) need `Config5` and `FIR.UFRP`, which this Release 2 profile lacks; they are treated as control registers that do not exist (the pre-Release 6 clean Operation is MD00086 Rev 2.50, CTC1, p.106). (2) `ValueFPR`/`StoreFPR` (p.22-23): the comparison glyphs of `FP32RegistersMode`/`fpr0` are lost in the text extraction; read as "32-bit FPR model and `fpr` odd is UNPREDICTABLE" (consistent with "FP32RegistersMode ... 32, 32-bit FPRs, in which 64-bit data types are stored in even-odd pairs", p.7), and `UNPREDICTABLE32 || value31..0` as the 32-bit register holding `value31..0`. (3) The `C.cond.fmt` Operation (p.112-113) says `SignalException(InvalidOperation)`; it is the FP exception of Vol I-A §6.7.1 (taken only when `Enables.V` is set; otherwise the Boolean result is written and `Flags.V` set, p.110). (4) `SWXC1` p.406 prints the alignment test as `vAddr1..0 != 0^3`; the Restrictions say "EffectiveAddress1..0 != 0". (5) `PREFX` (p.329) refers to `PREF` (p.321): no addressing-related exception, no architectural effect, so the Operation performs no translation. (6) `CVT.W.fmt` p.160 prints the default result as `2^63-1` (typo for `2^31-1`, see §9 item 13).
| `Oracle.divByZero`, `Oracle.divuByZero` | `(HI, LO)` unchanged, no exception | "If the divisor in GPR rt is zero, the arithmetic result value is UNPREDICTABLE" (DIV, p.165; DIVU, p.171) | §9.2, `div_by_zero_spec` |
| `Oracle.mulHILO` | `(HI, LO)` unchanged | "The contents of HI and LO are UNPREDICTABLE after the operation" (MUL, p.299) | `mul_leaves_hi_lo_unchanged` |
| `Oracle.extOutOfRange` | Reserved Instruction (7R; was `.proceed`) | "The operation is UNPREDICTABLE if lsb+msbd > 31" (EXT, p.183) | `decode` rejects such words (Reserved Instruction, `Oracle.unpredictableEncoding`); the `ext` arm of `step` raises Reserved Instruction for constructor values in the range (7R), `ext_spec_fields` |
| `Oracle.insLsbAboveMsb` | Reserved Instruction (7R; was `.proceed`) | "The operation is UNPREDICTABLE if lsb > msb" (INS, p.193) | as EXT: `decode` rejects, the `ins` arm raises Reserved Instruction, `ins_spec_fields` |

Wave 12a, a model-side strengthening of the limits on UNPREDICTABLE and UNDEFINED outcomes
(`Manual.UnpredictableLimits`, `Manual.UndefinedOutcomeValid`): such an outcome leaves the hardware
interrupt inputs `HW` unchanged. MD00086 Vol II-A Rev 6.06 §1.2.1-1.2.2 (p.3-4) has no sentence about
them; they are inputs (MD00090 Vol III Rev 6.02 §6.1.1.1, Table 6.2, p.73) read through the read-only
`Cause.IP7..IP2` (§9.36, p.209; Table 9.52, p.211), so no instruction writes them. `modelOracle` and
the witness oracles of `Refine/ChoiceWitness.lean` satisfy it (`modelOracle_valid`, `wo_valid`).

Two readings the spec states explicitly: the timer advances after the instruction of the instruction
time (`Manual.TimerTick`; implementation-dependent placement) and an interrupt can be taken at the
nullified delay slot of a branch-likely (§9 item 1b).

### 11.1 7B S2 (memory, atomic, unaligned, trap, syscall pages): readings and pins

| Item | Reading in `Semantics/Manual/` | Manual text | Model |
|---|---|---|---|
| `Impl.SynciAddressError` | false (no Address Error) | "An Address Error Exception (with cause code equal AdEL) may occur if the effective address references a portion of the kernel address space ... It is implementation dependent whether such an exception does occur" (SYNCI, p.412) | `synci` computes the address and does nothing |
| PREF | no state change, no exception | "PREF does not cause addressing-related exceptions ... the exception condition is ignored" (PREF, p.321); "Any action, including doing nothing, is permitted" (p.321); `PrepareForStore` (hint 30) not taken | `pref` is a no-op |
| SYNC | no state change | "SYNC has the same effect as a NOP" on a strongly ordered system (SYNC Programming Notes, p.410) | `sync` is a no-op |
| LWR `temp` line | `GPR[rt]31..32-8*byte \|\| memword31..8*byte` | The printed Operation (LWR, p.248) is `temp ← memword31..32-8*byte \|\| GPR[rt]31-8*byte..0`. It contradicts Figure 4.6 on the same page (big-endian `vAddr1..0 = 0` loads only `I`; `= 3` loads `I J K L`): as printed, `vAddr1..0 = 3` (`byte = 0`) would leave `GPR[rt]` unchanged and `= 0` (`byte = 3`) would load 3 bytes of memory over the high bytes. The same line is in MD00086 Rev 2.50. The mirrored line reproduces all four rows of the figure; the Figure (and QEMU, `tests/oracle/lwl_lwr_align.asm`) win | `lwr` byte-by-byte |
| `StoreMemory` byte lanes | `storedLanes p a`: lanes `0..p` if `a = p`, else `p..p+a` | "The low-order two (or three) bits of pAddr and the AccessLength field indicate which of the bytes within the MemElem data should be stored" (§2.2.2.2.4, p.20) says nothing more. `SWR` calls `StoreMemory(CCA, WORD-byte, ..)` with `pAddr1..0 = vAddr1..0` (big-endian) and must store the bytes `0..pAddr1..0` (Figure 5.14, p.402), while `SB`/`SH`/`SW`/`SWL` (`AccessLength = 3 - pAddr1..0`) store `pAddr1..0 ..` upward (Figure 5.10, p.398). `a = p` occurs for no store but `SWR` (and `a = p = 0`, one byte, either way) | `swr`, `swl` byte-by-byte |
| `SC` and the address | `atomic_update = LLbit ∧ vAddr31..2 = LLAddr31..2`, used for the store and for the result; `LL` records `LLAddr ← vAddr` | The Operation tests `LLbit` only; the prose says "An SC will fail if the aligned address of the SC does not match that of the preceding LL" (SC, p.347) | `llAddr` |
| `SC` reads `LLbit` before its own store | result `0^31 \|\| atomic_update`, then `LLbit ← 0` | the store of the `SC` itself is not a store "between the execution of LL and SC" (SC, p.347), so `Oracle.storeClearsLL` does not apply to it | same observable result |
| Trap `code` field | not used | "the code field is available for use as software parameters" (TEQ, p.416; SYSCALL p.415; BREAK p.109) | ignored |
Readings of the manual text made by the 7B S1 transcription (integer ALU, `Semantics/Manual/Ops/{IntArith,Shift,MulDiv,BitOps,Immediate}.lean`):

* `div`, `mod` (MD00086 Vol II-A Rev 6.06, Table 1.1, p.5: "2's complement integer division", "2's complement modulo") do not name a rounding rule; the spec truncates toward zero and gives the remainder the sign of the dividend (`BitVec.sdiv`/`BitVec.srem`), as `DIV` hardware does and as the model does.
* WSBH, p.445: the printed Operation reads `GPR[rs]`; the Description ("Within each halfword of GPR rt") and the format diagram (the field at 25..21 is `0`) make the source `GPR[rt]`. Transcribed with `rt`.
* ROTR p.339, ROTRV p.340: the printed page has `ArchitectureRevision() < 2` (read from the PDF; only the text extraction of 6.06 loses the `<`). With `ArchitectureRevision() = 2` the UNPREDICTABLE branch is never taken; the spec keeps the line as a comment (7R).
* CLO p.134, CLZ p.135: UNPREDICTABLE if `rt != rd` (pre-Release 6); `Instruction.clo/clz` carry no `rt`, the diagram line of `Manual.enc` has `rt = rd`. A word with `rt != rd` matches the diagram with an UNPREDICTABLE field value: `Manual.UnpredictableEncoding`, `Oracle.unpredictableEncoding` (7R).
* EXT p.183, INS p.192 (7R): the constructor's `pos`/`size` map to the diagram's 5-bit fields as `encode`/`Manual.enc` write them (`lsb = pos`, `msbd = size - 1`, `msb = pos + size - 1`, each mod 32); model and spec read the same fields for every constructor value (a constructor `size = 0` is `msbd = 31`).
* SLL p.376, SRL p.385, SRA p.383, ROTR p.339 (7R model fix): `s ← sa` is the 5-bit field; the model shifts by `sa mod 32` (it used the raw constructor value, which `decode` never makes 32 or more). The trusted `sll_spec_raw` is unchanged (its `decode` hypothesis gives `shamt < 32`).
* JR p.206-207, JALR p.196, JR.HB p.208-209, JALR.HB p.198-199 (7R model fix): hint 0 is JR/JALR, hint `10000` (bit 10) is JR.HB/JALR.HB (new constructors `jrHb`/`jalrHb`; `ClearHazards()` has no state, hazards clear immediately, see the `EHB` pin), any other hint is an UNPREDICTABLE encoding (Reserved Instruction). Before 7R `decode` ignored the hint field, which made `DecoderSound decode` false (review reproducer `r4`).
* MTC0 to EBase with `Status.BEV = 0` and a different Exception Base: UNDEFINED (MD00090 Vol III Rev 6.02 §9.41, p.223), `Oracle.ebaseWriteBEV0` (7R).
* Reset (7R): the oracle's `Status` is masked with the Status bits this profile implements (`StatusWritable`; Vol III Table 9.47, p.189-196) before the Operation's assignments (§6.2.5, p.89-90).
* MTHI p.297, MTLO p.298: "If an MTHI instruction is executed following [DIV/DIVU/MULT/MULTU], but before an MFLO or MFHI instruction, the contents of LO are UNPREDICTABLE". The condition depends on instruction history that `Arch` does not carry; not modelled (the model does not model it either).
