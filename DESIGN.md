# Design

How the Lean development is organised and how `step` works. The what-is-proved-and-trusted
account is in `docs/OVERVIEW.md` ("What is proved, what is tested, what is trusted"); the
per-instruction semantics are in `docs/spec/INSTRUCTION-REF.md`; pinned conventions and
divergences are in `docs/spec/SPEC-NOTES.md`.

## 1. Scope

A small-step semantics of a **MIPS32 Release 6** processor: little-endian, one branch delay slot for the branches
and jumps that have one, the Release 6 compact branches and compact jumps with their forbidden slot, no
branch-likely instructions, no `HI`/`LO`, a 64-bit FPU (`Status.FR = 1`) with the IEEE 754-2008 NaN encoding
(`FIR.Has2008 = 1`, `FCSR.NAN2008 = ABS2008 = 1`), and the Coprocessor 0 exception model. `step : State → State`
is one instruction time of the processor; `run s n` is `step` iterated `n` times. Everything that is a
convention of this model rather than of the architecture (loading a program, the MARS-style `syscall` services,
deciding when a run is over) is the environment layer, `Semantics/Env.lean` (§4a). The Release 6 `Instruction` type has 203
constructors (`python3 scripts/trace.py`). Kernel Mode and User Mode, the CP0 access rule, the Reset exception, the Fixed Mapping MMU, the timer
(`Count`/`Compare`), interrupts in interrupt compatibility mode (software requests, the timer, six hardware input
lines that the environment holds deasserted; Interrupt exception with vector offset `0x180`/`0x200`), standby after
`wait`, `IntCtl` and `SRSCtl` (no shadow sets beyond the normal GPRs, `RDPGPR`/`WRPGPR` on set 0) are modeled:
`step = timerTick ∘ stepCore`, where `stepCore` takes an enabled interrupt, or stays in standby, or fetches and
executes. Not modeled: vectored/EIC interrupts, the TLB (Fixed Mapping MMU), caches, EJTAG, coprocessor 2, the
optional modules (MSA, microMIPS, VZ, MT, DSP, EVA, XPA, MCU, CRC, GINV, VP) and every other release
(`docs/spec/MIPS-COVERAGE-GAPS.md`; the classification of every instruction page is `docs/spec/R6-COVERAGE.md`).

**Releases and profiles.** The release-specific pieces are keyed once, so that earlier releases (R5, R3, R2, R1) can be
added later, backwards, as further profiles; none is implemented. The Release 2 model, which this one replaced in
place, is at the code repository's tag `mips32r2-final`.

- `Release` (`Semantics/Types.lean`): an inductive type with one arm, `r6`. `Profile` holds `release : Release` and
  `bigEndianMem : Bool`; `profile : Profile := { release := .r6, bigEndianMem := false }` is the profile of the
  model. Release 6 requires little-endian support (`Config5.DEC = 0`, MD00090 Vol III Rev 6.02 §9.50, Table 9.69,
  p.261); the byte-order helpers (`byteShift`, `byteOfValue`, ...) and every memory access read `bigEndianMem`.
- **One union `Instruction` type, one decoder table per release** (`Semantics/Instruction.lean`). `decodeFor : Release →
  W32 → Option Instruction` has one arm per release (`.r6 => decodePrimary`) and `decode w = decodeFor profile.release w`.
  An instruction is available in a release exactly when that release's table emits it. The Release 6 table is one function
  per opcode group, each a table keyed by the field the manual's opcode tables key on (MD00086 Vol II-A Rev 6.06,
  Table A.2 and the sub-tables of Appendix A, p.451 onwards): `decodePrimary` (opcode), `decodeSpecial` (`funct`),
  `decodeRegimm` (`rt`), `decodeSpecial3` (`funct`, with BSHFL), `decodeCop0` (`CO`, then `funct` or `rs`),
  `decodeCop1` (`rs`, with `decodeCop1S`/`decodeCop1D` keyed by `funct`) and the shared helpers for the compact-branch
  encodings that reuse one opcode for several instructions told apart by `rs`/`rt` (Table A.26, p.464). A sibling
  table for another release reuses or replaces each function. The encodings Release 6 removes ("6R"/"6Rm", Table A.1,
  p.451) do not decode: `step` raises Reserved Instruction (Coprocessor Unusable in an unusable coprocessor's space).
- **Coprocessor 0 layout table** (`cp0Layout : Release → Nat → Nat → Option Cp0Reg`, `Semantics/Exec/Cp0.lean`): the
  `(rd, sel)` ↦ register map of the release, documented register by register against MD00090 Vol III Rev 6.02
  Table 9.1 (UserLocal, HWREna, BadVAddr, BadInstr, BadInstrP, Count, Compare, Status, IntCtl, SRSCtl, Cause, EPC, PRId,
  EBase, Config..Config5, LLAddr, ErrorEPC, KScratch1..6). `MFC0`/`MTC0` consult it; a pair it does not name reads 0
  and ignores writes (MD00086 Vol II-A Rev 6.06 MFC0 p.266, MTC0 p.290). `cp0Read` / `cp0Write` give each register's
  value and write rule (which bits are R/W, which are read-only).

## 2. Module map and dependency graph

Generated from the `import` lines of the repository (Lean/Std imports omitted; per-family files grouped).

```
Word ─┬─ Types ─┬─ State ───────────────────────────────┐
      │         ├─ Instruction ─┬─ Asm (Asm/*)          │
      │         │               └─ Specs/WellFormed     │
      └─ FpOps ─┬─ FpOpsFacts                           ├─ Exec/Base ── Exec/<Family> ── Step ── Specs/Defs ── Specs/* ── StatementsProofs
                └─ FpCompareFacts                       │                                  │       (Statements: imports Defs only)
         (Exec/Base imports Word, Types, State, Instruction, FpOps) ┘                       └─ Tests/StepFixtures ── Tests/Step*Tests
                                         Step ── Env (loader, hosted run) ── Specs/Defs, Specs/Fixtures, Tests/StepFixtures
Word, Types, Instruction, FpOps ── Manual/* (independent transcription; nothing else of the model)
Manual/Relation + Step ── Refine/Defs (abs, Inv) ── Refine/Abs ── Refine/* ── Refine/Instr ── Refine/Step ── Refine/Determinism ── StatementsProofs
                                     (Statements: imports Specs/Defs and Refine/Defs only)
FpOps ── FpOpsSpec ── FpOpsCorrect* ── StatementsProofs   (FpOpsSpec: definitions only; Statements imports it)
```

| File | Contents | Imports (project) |
|---|---|---|
| `Semantics/Word.lean` | `W32 = BitVec 32`, sign extension, signed view | none |
| `Semantics/Types.lean` | `Release`/`Profile`/`profile`, byte-order helpers, `Program` (assembler output, loader input), `State` (the processor), the bit masks of the CP0 registers, instruction-word builders (`mkRT`/`mkIT`/`mkJT`), constants (`textBase`, `spInit`, the vectors) | Word |
| `Semantics/State.lean` | `initialState`, `powerOnState`, register / FP register accessors, operating mode, the Fixed Mapping MMU (`translate`), memory accessors and writers | Word, Types |
| `Semantics/Instruction.lean` | `Instruction` (203 constructors), the Release 6 decoder tables and `decodeFor`/`decode` (strict), `encode` | Word, Types |
| `Semantics/Asm.lean`, `Semantics/Asm/*.lean` | assembler: source text to `Program`, one encoder table per family (§8a) | Word, Types, Instruction |
| `Semantics/FpOps.lean` | `Mips.Fp`: pure bit-level IEEE-754 arithmetic, conversions, compare, FCSR, the Release 6 operations (fused multiply-add, min/max, class, rint, CMP) | Word |
| `Semantics/FpOpsFacts.lean`, `FpCompareFacts.lean` | kernel-checked facts about `FpOps` (corner cases; meaning of the compare result) | FpOps |
| `Semantics/FpOpsSpec.lean` | the IEEE 754 / Release 6 FPU reference definitions (trusted, definitions only) | FpOps |
| `Semantics/FpOpsCorrect*.lean` | the proofs that the rounding core and every FP operation meet `FpOpsSpec` (§7) | FpOpsSpec, FpOps |
| `Semantics/Exec/Base.lean` | the vocabulary of execution: `advance`/`mkNext` (the delay-slot exit), `isBranchLike`, `exceptionEntry` and the `take*` helpers, coprocessor usability, the FP finish helpers, CP0 values, the timer, interrupts, `rdhwr` values | Word, Types, State, Instruction, FpOps |
| `Semantics/Exec/<Family>.lean` | one `exec<Family> : State → Instruction → Option State` per family (§4) | Exec/Base |
| `Semantics/Step.lean` | `execTables`, `execBody`, `execInstr`, `execute`, `stepCore`, `step`, `run`, `resetException`/`resetState` | all of `Exec/*` |
| `Semantics/Env.lean` | **not the architecture**: `load`, `hostedStart`, `HaltReason`, `HostEnv`, `Hosted`, `hostStep`, `runHosted`, `runProgram`, the hosted services | Step |
| `Semantics/Specs/*.lean` | the specification: statement vocabulary (`Defs`, `WellFormed`), plumbing (`Lemmas`, `Tactics`, `Fixtures`), global theorems and one file per instruction family; index `StepSpec.lean` | Step, FpOpsFacts, FpCompareFacts |
| `Semantics/Manual/*.lean` | the independent manual specification: `Arch`, the pseudocode vocabulary, CP0/memory/FPU/exception/interrupt/timer/reset processing, `Encoding` (`enc`), `Decode` (the spec's own decoder), one Operation per manual page (`Ops/*`), `Operation`, `Cycle` (`InstructionTime`), `Relation`, `Choices`, `Accuracy` (`docs/MANUAL-SPEC.md`) | Word, Types, Instruction, FpOps (checked by `scripts/manual_independence.py` and `manual_deps.py`) |
| `Semantics/Refine/*.lean` | the refinement: `Defs` (`abs`, `Inv`; definitions only), bridges, `<ctor>_refines` per family, the cycle paths, `allInstrRefines`, `step_eq_manual` and corollaries (§9) | Manual, Step, Specs (Invariants, RegFileSize, DecodeSpec), Env |
| `Semantics/Statements.lean` | the trusted surface: 221 statements, proofs `sorry` (challenge module of `lake comparator`); imports `Specs/Defs`, `Refine/Defs`, `Manual/*`, `FpOpsSpec` only | Specs/Defs, Refine/Defs, FpOpsSpec |
| `Semantics/StatementsProofs.lean` | the same statements proved from `Specs/*`, `Refine/*` and `FpOpsCorrect*` (solution module) | Specs/StepSpec, Refine/*, FpOpsCorrect* |
| `Semantics/Tests/*.lean` | `#guard`s and `example`s for each definition file | the file under test; Step tests import `Tests/StepFixtures` |
| `Semantics.lean`, `Checked.lean` | library roots; `Checked` is what `lake check` replays | all of the above except `Statements` |
| `MipsRun.lean`, `DiffHarness.lean`, `EquivHarness.lean` | executables (run one program to JSON; corpus vs MARS; equivalence corpus and the manual-spec check), all through the hosted run | Word, Types, State, Instruction, Asm, Step, Env |

`Semantics/Step.lean` does not import `Env`, `Asm`, `FpOpsFacts`, `FpCompareFacts` or any `Specs`/`Tests`
file: the processor model depends only on itself. Within `Specs`, `Lemmas` imports `Defs` and `FpOpsFacts`; `Tactics`
imports `Lemmas`; each family file imports `Tactics` and `Fixtures` (some also `Invariants`, `DelaySlot` or
`Exception`). Spec files do not import `Tests` (their example builders are in `Specs/Fixtures.lean`).
Mathlib is a declared dependency in `lakefile.toml`, but no file of the project imports it (only `Std`
and `Lean.Elab.Tactic`).

## 3. `State`

`Semantics/Types.lean`. General registers are `W32`; the FPRs are 64 bits.

| Field | Meaning |
|---|---|
| `pc` | program counter |
| `regs` | 32 GPRs (array of size 32; register 0 is hardwired by `writeReg`). There is no `HI`/`LO`: Release 6 removed them |
| `fpRegs : Array (BitVec 64)` | 32 FP registers, each the raw 64-bit pattern: the 64-bit FPU of Release 6 (`Status.FR = 1`, read-only: "Release 6 disallows bi-modal support"). A double or a longword is the whole register; a word is the low 32 bits, and a 32-bit write leaves the upper half UNPREDICTABLE (MD00082 Vol I-A Rev 6.01 §6.6.2, p.98), pinned to unchanged (`writeFpReg`) |
| `fcsr` | the FP control/status register, the writable fields only (RM, Flags, Enables, Cause, `FS`, the condition-code bits of the stored word); `FIR` is a constant, and `FCSR.NAN2008`/`ABS2008` read 1 (`Mips.Fp.readFCSR`) |
| `physMem` | **physical** memory, sparse bytes, `Std.HashMap PAddr UInt8`; absent bytes read as 0 (a pin); reached only through the MMU (`translate`); instructions are fetched from here |
| `pendingBranch : Option W32` | `some t`: the instruction at `pc` is in a branch delay slot (or the forbidden slot of a not-taken compact branch) and control goes to `t` after it |
| `llBit`, `llAddr` | LL/SC link bit and address |
| `cp0Status`, `cp0Cause`, `cp0Epc`, `cp0BadVAddr`, `cp0ErrorEpc`, `cp0EBase`, `cp0ConfigK0`, `cp0ConfigK23`, `cp0ConfigKU`, `cp0Count`, `cp0Compare`, `cp0TimerInt`, `cp0HWREna` | the stored CP0 registers (Status write mask `0x3040FF17`, including `UM`, `RW` (bit 28) and `CU1`; see SPEC-NOTES) |
| `cp0UserLocal`, `cp0BadInstr`, `cp0BadInstrP`, `cp0KScratch : Fin 6 → W32`, `cp0Config5SBRI` | the Release 6 registers (`UserLocal`, `BadInstr`, `BadInstrP`, `KScratch1..6`) and the one writable `Config5` bit |
| `hwInt : BitVec 6` | the hardware interrupt lines HW5..HW0: inputs, driven by the environment, never written by `step` |
| `standby` | the processor is in the lower power mode entered by `wait` (or `pause` with `LLbit` set) |

The state is self-contained: instruction fetch is `readMemWord s s.pc`, from the same memory loads and stores
use, so self-modifying code works. There is no output field: the output of the hosted
services is environment state (`Hosted.out`, §4a). There is no `nullified` marker: Release 6 has no branch-likely
instruction.

**Address translation (the MMU).** The model has the Fixed Mapping MMU (`Config.MT = 3`; MD00090 Vol III
Rev 6.02 Appendix A.1, p.313-317; Vol I-A Rev 6.01 §2.4.2, p.32). Addresses are `VAddr` (what programs compute)
or `PAddr` (indices into `physMem`), both `W32`. `State.lean` holds the whole MMU:
`fixedMappingPA erl va` (Table A.1: kuseg `+0x4000_0000` when `ERL = 0`, identity when `ERL = 1`; kseg0 and
kseg1 → the low 512 MB; kseg2/kseg3 identity), `accessAllowed s va` (Kernel Mode, or a useg address:
Table 4.2) and `translate s va = if accessAllowed s va then some (fixedMappingPA ERL va) else none`.
`translate` is called in exactly one layer: the six `readMem*`/`writeMem*` functions, which check alignment
(a misaligned load or store is an Address Error: permitted by MD00082 Vol I-A Rev 6.01 App. B.2, p.128), translate, and
read or write `physMem` in the byte order of `profile`; `none` from them is an Address Error, which the caller raises as
AdEL (fetch, load) or AdES (store) with `BadVAddr` = the virtual address. Instruction fetch is
`readMemWord s s.pc`, so fetch, loads and stores share the translation; no other code reads `physMem`
except the loader and observers (§4a). The TLB registers read 0 and ignore writes, and the TLB instructions raise
Reserved Instruction (A.1.3, p.317).

**Modes and reset.** `kernelMode s` (`UM = 0` or `EXL` or `ERL`), `userMode s = !kernelMode s`, `cp0Usable s`
(Kernel Mode only: Release 6 has no `Status.CU0`; bit 28 is the software bit `RW`) follow MD00090 Vol III Rev 6.02
ch.3 (p.21-23) and Table 9.47 (p.190). `resetException s` is the Reset exception
(§6.2.5, p.89-90: `pc ← 0xBFC0_0000`, `BEV ← 1`, `ERL ← 1`, `Cause.DC ← 0`, `EBase`, `Config.K0 ← 2` (and the pinned
`K23 = KU = 2`), `ErrorEPC ←` restart PC; undefined registers keep their value); `resetState = resetException powerOnState`,
where `powerOnState` pins every undefined value to 0. `initialState pc` (all registers 0 except `$sp = spInit`,
`Status = CU1`, `EBase = 0x80000000`) is the state after the hosted boot convention (§4a).

## 4. The step pipeline

```
step s = timerTick (stepCore s)

stepCore s:
  interruptTaken s   -> takeInterrupt s               (Interrupt exception, BadInstr not touched)
  s.standby          -> standbyStep s                  (stay, or restart on a pending request)
  otherwise          -> execute s

execute s:
  fetch   readMemWord s s.pc            (translate s pc, then the little-endian word from State.physMem)
            none (pc not word-aligned,
                  or outside useg in User Mode) -> Address Error (AdEL), BadVAddr = pc
  decode  decode w                      (= decodeFor profile.release w)
            none                         -> Reserved Instruction
                                            (a COP0 word with CP0 unusable -> Coprocessor Unusable, CE = 0;
                                             a COP1-space word with CU1 = 0 -> Coprocessor Unusable, CE = 1;
                                             a COP2-space word -> Coprocessor Unusable, CE = 2)
  guards  execInstr s instr
            isBranchLike instr and s.pendingBranch.isSome -> Reserved Instruction (§5)
            usesCop1 instr and Status.CU1 = 0              -> Coprocessor Unusable, CE = 1
            usesCop0 instr and not cp0Usable s             -> Coprocessor Unusable, CE = 0
  body    execBody s instr              -> the next State (or an exception, below)
  commit  mkNext / advance: pc := pendingBranch target if one is pending, else pc + 4
```

**The Exec tables.** What each instruction does is not one `match` over 203 constructors but a list of per-family
tables, `Semantics/Exec/<Family>.lean`. Each family defines `exec<Family> : State → Instruction → Option State`, which
returns the instruction's effect for the instructions of its family and `none` for every other one. `Step.lean` lists them:

```
execTables = [execIntArith, execShift, execBitOps, execImmediate, execMemory, execAtomic,
              execBranch, execJump, execTrap, execSyscall, execSystem, execCp0,
              execFpuMove, execFpuControl, execFpuMemory, execFpuArith, execFpuConvert, execFpuR6]
execBody s i = (execTables.findSome? (fun f => f s i)).getD s
```

so `execBody` is "the first table that handles the instruction", and every constructor is in exactly one table (the
fallback `s` is never reached; `trace.py --check` finds each constructor's arm in the `exec*` files). Adding an
instruction touches its family's table only. The families: `IntArith` (add/sub, slt, logical, the R6 `MUL`/`MUH`/`DIV`/`MOD`
forms, `SELEQZ`/`SELNEZ`), `Shift`, `BitOps` (`CLO`/`CLZ`, `EXT`/`INS`, `SEB`/`SEH`/`WSBH`, `BITSWAP`, `ALIGN`), `Immediate`
(`ADDIU`, `AUI`, the PC-relative `ADDIUPC`/`AUIPC`/`ALUIPC`/`LWPC`, ...), `Memory` (the integer loads and stores, `SYNC`, `PREF`, `SYNCI`), `Atomic` (`LL`/`SC`),
`Branch` (the branches with a delay slot, `NAL`/`BAL`, the compact branches with a forbidden slot, `BC1EQZ`/`BC1NEZ`),
`Jump` (`J`/`JAL`/`JALR`, the compact jumps `JIC`/`JIALC`), `Trap` (traps, `BREAK`, `SIGRIE`), `Syscall`, `System` (`ERET`/`ERETNC`, `WAIT`, `PAUSE`, `CACHE`,
`RDHWR`), `Cp0` (`MFC0`/`MTC0`, `DI`/`EI`, `DVP`/`EVP`, `RDPGPR`/`WRPGPR`, and the `cp0Layout` table), and the six FPU families
(`FpuMove`, `FpuControl`, `FpuMemory`, `FpuArith`, `FpuConvert`, `FpuR6`). The Release 6 FPU instructions
(`CMP.cond.fmt`, `SEL`, `SELEQZ`/`SELNEZ`, `MADDF`/`MSUBF`, `MIN`/`MAX`/`MINA`/`MAXA`, `CLASS`, `RINT`) are one table, `FpuR6`.
`exec_unfold` (a tactic in `Step.lean`) reduces `execBody s i`, for `i` a constructor application, to that instruction's arm.

`step` has no halting case: overflow, address error, reserved instruction, System Call (`syscall`, always),
breakpoint, traps, Coprocessor Unusable and FP traps are architectural exceptions (a state transition to the
vector). `run s n` is `step` iterated `n` times; nothing else happens in `run`. Both are total by their types.

## 4a. The environment layer (`Semantics/Env.lean`; not the architecture)

```
hostedStart     = bootConvention textBase resetState
                  (reset, then what a boot ROM would do: Status := CU1, $sp := spInit, pc := textBase;
                   equal to initialState textBase, hostedStart_is_reset_then_boot)
load p          = loadImage p hostedStart      (write every image word at loadAddr va = fixedMappingPA false va,
                                                its physical address with ERL = 0; pc = textBase)
loadAtReset p   = loadImage p resetState       (MipsRun --reset: start at 0xBFC0_0000; boot code is the program's;
                                                same placement, so the boot code must clear ERL before using kuseg)
hostStep env h  : stopReason env h.machine = some r        -> halt r
                  services on, selectedService h.machine = some svc -> performService svc h
                  otherwise                                -> next { h with machine := step h.machine }
runHosted env fuel h   hostStep iterated; HostedResult = halted r h steps | limitReached h steps
runProgram p fuel services = runHosted { image := p, services } fuel { machine := load p }
```

- `Hosted` is the processor state plus the output buffer `out`.
- **Services** (MARS/SPIM numbering, selected when the instruction at `pc` is a `syscall`): 1 print int, 4 print
  string (at most `printStringFuel` bytes), 11 print char — append to `out` and complete the `syscall` with
  `advance` (`pc + 4`, or the pending branch target in a delay slot); 10 exit — stop with `exit`. Any other
  `$v0`: the processor steps (System Call exception). `services := false` (`MipsRun --bare`): no service.
- **Stopping conventions** (`stopReason`, checked before every step): `pc` word-aligned and not in the loaded
  image → `unhandledException ExcCode EPC BadVAddr` if `Status.EXL = 1` and `pc` is the general vector (an
  exception was taken and no handler was loaded), else `noInstruction pc`. The processor itself would go on
  (unloaded memory reads as 0, a `nop`).
- `hostStep_eq_step` / `runHosted_agrees_with_run` (`Specs/Hosted.lean`) state that the hosted run *is* `step`
  / the bare `run` whenever it neither stops nor performs a service.

## 5. Delay slots, compact branches, forbidden slots

A branch or jump with a delay slot does not change `pc` to its target. It sets `pc := pc + 4` (the delay-slot instruction) and
`pendingBranch := some t`: `t` is the target if the branch is taken, and the fall-through `pc + 8` if a
conditional branch is not taken, so `pendingBranch.isSome` is exactly "the next instruction is in a delay
slot". The delay-slot instruction goes through `mkNext`/`advance`, which sets `pc := t` and clears the
marker. Consequences: `jal`/`jalr`/`bal`... link `pc + 8`; an exception in the delay slot records
`EPC = pc - 4` and `Cause.BD = 1` and abandons the pending target (a later `eret` re-executes the branch);
a control-transfer instruction in a delay slot raises Reserved Instruction (Release 6 requires exactly this: "Release 6
implementations are required to signal a Reserved Instruction exception", MD00086 Vol II-A Rev 6.06 BEQ, p.72;
MD00082 Vol I-A Rev 6.01 §5.3.2.1, p.62). `isBranchLike` (`Exec/Base.lean`) lists the control-transfer instructions: the
branches and jumps, `NAL`, the compact branches and jumps, `BC1EQZ`/`BC1NEZ`, `ERET`, `ERETNC`, `WAIT`, `PAUSE`.

**Compact branches and jumps** (`BC`, `BALC`, `B<cond>C`, `B<cond>ZALC`, `BOVC`/`BNVC`, `JIC`/`JIALC`) have **no delay slot**: taken,
`pc` becomes the target at once (`Exec/Branch.lean`, `Exec/Jump.lean`). A conditional compact branch that is *not* taken has a
**forbidden slot**: the next instruction. The manual gives it the delay slot's rules (MD00082 Vol I-A Rev 6.01 §5.3.2.1-5.3.2.2, p.62):
a control transfer there raises Reserved Instruction (and only when the branch is not taken, MD00086 B<cond>C p.84), and an exception there
reports `EPC` = the branch with `Cause.BD = 1`. The model represents it as the delay slot of a not-taken branch: the compact
branch sets `pendingBranch := some (pc + 8)`, so the machinery above applies unchanged and no state of its own is needed.
Under this reading `BadInstrP` in a forbidden slot is the compact-branch word (SPEC-NOTES).

There are no branch-likely instructions in Release 6, so no instruction is ever nullified.

The general statement is `delay_slot_commits_target` (`Specs/DelaySlot.lean`, in the trusted surface):
a non-branch instruction that completes normally with `pc + 4` produces, in a delay slot, the same state with
`pc := t`; `forbidden_slot_cti_reserved` (`Specs/CompactBranch.lean`) is the forbidden-slot statement.

## 6. Exceptions

`exceptionEntry s code ce sync` (Vol III 6.2.3): if `Status.EXL = 0`, `EPC := pc` (or `pc - 4` in a delay slot or forbidden slot) and
`Cause.BD` set accordingly; `Cause.ExcCode := code` and `Cause.CE := ce`; `Status.EXL := 1`;
`pc :=` the general vector (`0x80000180` with `EBase` as base when `Status.BEV = 0`, `0xBFC00380` when
`BEV = 1`); `pendingBranch := none`. A synchronous exception (all but the Interrupt) also captures the faulting instruction
word in `BadInstr` and, in a delay slot, the branch in `BadInstrP` (MD00090 §9.25-9.26, p.179-181). `LLbit` is **not** changed by
exception entry: the event that makes an `SC` fail is the `eret`, which clears it; `ERETNC` does not (MD00086 SC p.347, ERETNC p.179).
Address errors also set `BadVAddr`. `eret` returns to `EPC` (`ErrorEPC` when `ERL = 1`) and clears `EXL` (or `ERL`) and `llBit`.
`Cause.CE` is 0 except for Coprocessor Unusable. Coprocessor Unusable is raised for any COP1 instruction when `Status.CU1 = 0`,
and for any Coprocessor 0 instruction outside Kernel Mode (there is no `CU0`).

## 7. Floating point

`Semantics/FpOps.lean` is the whole FPU model; no host `Float` appears in any definition. The FPU is the Release 6
one: `Status.FR = 1`, `FIR = 0x00F3_0000`, `FCSR.NAN2008 = ABS2008 = 1`.

- **Exact + one rounding.** Operands are unpacked to `Exact` (a dyadic rational `(-1)^sign × sig × 2^exp`), the
  operation is performed exactly for add, subtract and multiply (`Exact.add`/`mul`); division and square root
  compute the quotient / root to at least `prec + 2` significant bits with a sticky bit for a nonzero remainder
  (`Exact.div`/`Exact.sqrt`, integer division and `isqrt`), which rounds the same way the true value would; and
  the result is packed by `Format.roundCore` (format, rounding mode, flush flag, exact value), which
  returns the bits plus the three conditions (overflow, tiny, inexact) from which `Rounded.flags` derives the
  IEEE flags. The Release 6 operations are built on the same core: the fused `MADDF`/`MSUBF` (`f32Fma`/`f64Fma`,
  one rounding of `fd ± fs × ft`), `MIN`/`MAX`/`MINA`/`MAXA`, `CLASS`, `RINT`, and the longword (`.L`) conversions.
- **`Env`.** `envOf fcsr` extracts the rounding mode `RM`, the `Enables` and `FS` that an operation consults.
- **`fpUpdate fcsr flags`.** Sets `FCSR.Cause` to this operation's exceptions; if an enabled exception is among
  them it leaves `Flags` untouched and reports a trap, otherwise it ORs the exceptions into `Flags`. The `Exec/Fpu*` tables
  finish every FP arithmetic instruction through `fpFinishS`/`fpFinishD`, which either write the
  destination or, on a trap, take the Floating Point exception (ExcCode 15) without writing it. `SEL`/`SELEQZ`/`SELNEZ`
  and `CLASS` update no FCSR field.
- **IEEE 754-2008 NaNs.** With `NAN2008 = 1` a NaN is signaling iff the fraction's most significant bit is 0; the default
  QNaN is `0x7FC00000` / `0x7FF80000_00000000`. With `ABS2008 = 1`, `ABS`/`NEG` are non-arithmetic: only the sign bit changes
  and no exception is signaled. With `FCSR.FS = 1` every subnormal input is replaced by zero of the same sign, and that
  flush signals Inexact except in comparisons (MD00082 Vol I-A Rev 6.01 Table 6.8, p.93; §6.7.2.4, p.102).
- **Evidence.** Corner cases are kernel-checked in `FpOpsFacts.lean`, the meaning of the compare result in
  `FpCompareFacts.lean`; `Tests/FpOpsTests.lean` compares against Lean's `Float32`/`Float` with `#guard`s; the
  QEMU oracle compares whole programs. `roundCore`, `isqrt` and the arithmetic are proved correct against the IEEE definition of
  `Semantics/FpOpsSpec.lean` in `Semantics/FpOpsCorrect*.lean`, one file per step of the argument: the core (`Core`, `Pack`, `Scale`, `Grid`, `Nat`,
  `Shape`, `Value`, `Main`), the exact results and the sticky division/root (`Exact`, `DivSqrt`, `Ops`), every operation over every operand
  (`Arith`, `Special`, `Conv`, `Word`, `Compare`), the FCSR environment (`Env`, `Fcsr`), the Release 6 operations (`Fma`: `MADDF`/`MSUBF`;
  `R6`: `CMP`, `MIN`/`MAX`, `CLASS`, `RINT`), the `RECIP`/`RSQRT` accuracy (`Acc`, `Recip`, `Rsqrt`, `RsqrtAux`), and the statement-facing surface (`IEEE`, `Api`).
  See `docs/OVERVIEW.md` (d).

## 8. Test strategy

| Layer | Where | What it checks | Run by |
|---|---|---|---|
| In-build `#guard`/`example` | `Semantics/Tests/*.lean`, `Semantics/Specs/*.lean` | encodings, assembler output, `step` on concrete states, FP corner cases | every build, and `lake check` |
| MARS differential | `tests/corpus/*.asm` (29), `DiffHarness.lean` | final output and registers vs real MARS 4.5, for the programs that are valid Release 6 (MARS cannot run Release 6) | gate step 5 |
| Equivalence corpus, expected output | `tests/equiv/*.asm`, `tests/asm/*.asm`, `EquivHarness.lean` | base/variant program pairs; programs whose `# Expected output:` is checked | gate step 6 |
| QEMU/LLVM oracle | `tests/oracle/*.asm`, `tests/oracle/encodings.list`, `scripts/oracle.py` | the same machine code on `qemu-system-mipsel -cpu mips32r6-generic` and on the model; assembler vs `llvm-mc -mcpu=mips32r6`; every constructor executed | gate step 7 |
| Refinement against the manual transcription | `Semantics/Refine/*.lean` (proof, every state of `Inv`); `EquivHarness.lean` (`Manual.InstructionTime` vs `step` on every state of every corpus/oracle program) | `step_eq_manual`: `step` is one instruction time of `Semantics/Manual` | every build / `lake check`; gate step 6 |
| Traceability | `scripts/trace.py` | every constructor has decode, encode, step arm, spec theorem, `Refine.<ctor>_refines`; the README table is current | gate step 8 |

### 8a. The assembler (`Semantics/Asm.lean`, `Semantics/Asm/*`)

Tested, not proved. Like the executor it is a set of per-family tables, not one block: `Asm/Syntax` (`parseLine`), `Asm/Expr` (literals, `label±const`,
range checks, registers), `Asm/Float` (exact decimal to IEEE 754 for `.float`/`.double`), `Asm/Operands` (the operand-shape combinators: `Ctx`,
`Enc`, displacements), one encoder table per family (`Asm/Int` `intTable`, `Asm/Memory` `memoryTable`, `Asm/Branch` `branchTable`, `Asm/System`
`systemTable`, `Asm/Fpu` `fpuTable`), `Asm/Pseudo` (idioms, `li`/`la`), `Asm/Table` (`instrTable` = the union of the tables, and the
`removedMnemonics` that Release 6 dropped, which are assembler errors), `Asm/Layout` (segments, data directives in the byte order of `profile`,
the two passes). Every table entry produces an `Instruction` and the word is the model's `encode`, so the assembler can only emit the
Release 6 encodings. The oracle compares it with `llvm-mc` word for word (`tests/oracle/encodings.list`).

## 9. The manual specification and the refinement layering

Two layers sit above the model, and both are part of the evidence rather than of the model (`docs/MANUAL-SPEC.md` is the design and the
transcription guide).

- **`Semantics/Manual/` (trusted, independent).** The manuals' pseudocode transcribed into Lean as a state-transition specification over its own
  state `Manual.Arch`: the vocabulary (`Pseudocode`: `Pseudo`, `Delay`, the oracle for UNPREDICTABLE/UNDEFINED), the architecture processes (`CP0`,
  `Memory`, `FPU`, `Exceptions`, `Interrupts`, `Timer`, `Reset`), the instruction diagrams (`Encoding`: `Manual.enc`; `Decode`: the spec's own decoder
  `Manual.Decode`/`decodeDiagram`), one `Ops/<Family>.lean` per family with one def per manual page (including `CompactBranch`, `PcRel`, `FpuR6`, `VP`),
  `Operation` (constructor ↦ page), `Cycle` (`InstructionTime`: interrupt, standby, fetch, decode, execute, completion, timer), `Relation`
  (`Step`, `Oracle.Valid`, `ChoiceFree`, `ConsultsOracle`), `Choices` (the pins `modelImpl`/`modelOracle`) and `Accuracy` (`Impl.Valid`, the `RECIP`/`RSQRT`
  bounds). It may import only `Word`, `Types` (W32/VAddr/PAddr), `Instruction` (constructor names) and the `FpOps` rounding core, and name no definition
  of `Step`/`State`; gate step 1 enforces this on the source (`manual_independence.py`) and on the elaborated environment (`manual_deps.py`,
  `ManualIndependence.lean`).
- **`Semantics/Refine/` (proofs; `Refine/Defs.lean` trusted).** `Defs` (`abs : State → Manual.Arch`, `Inv`), `Abs`/`Bridge*`/`Fetch` (plumbing), one file
  per family with one `<ctor>_refines` per constructor (203, collected by `allInstrRefines` in `Instr.lean`), `Cycle` (the non-instruction paths),
  `Decode`/`DecodeDiagram`/`DecodeBridge` (the model's `decode` against the spec's decoder), `Invariant`, `Step` (the top theorems `step_eq_manual`,
  `run_refines_manual`), `Determinism`, `ChoicePoints`/`Choice*` (`ChoiceFree` is exact), `ImplValid` (`modelImpl_valid`). `ctc1_refines` and
  `cfc1_refines` need `FcsrReservedZero` from `Inv`.

## 10. The gate

`scripts/gate.sh` runs ten steps: forbidden constructs and manual-spec independence, build, `lake check`, `lake comparator`, DiffHarness,
EquivHarness, oracle, trace, manuals selftest, hygiene (`scripts/README.md`). Only a full green run writes the
stamp that `scripts/gate-commit.sh` requires.
