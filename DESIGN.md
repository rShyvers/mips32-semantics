# Design

How the Lean development is organised and how `step` works. The what-is-proved-and-trusted
account is in the root `README.md` ("What is proved, what is tested, what is trusted"); the
per-instruction semantics are in `docs/spec/INSTRUCTION-REF.md`; pinned conventions and
divergences are in `docs/spec/SPEC-NOTES.md`.

## 1. Scope

A small-step semantics of a pre-Release-6 MIPS32 processor with the Release 2 feature set:
big-endian, one branch delay slot, branch-likely, HI/LO, a 32-bit FPU (`Status.FR = 0`) with
legacy FP (`FIR.Has2008 = 0`), and the Coprocessor 0 exception model. `step : State → State` is one
instruction time of the processor; `run s n` is `step` iterated `n` times. Everything that is a convention of
this model rather than of the architecture — loading a program, the MARS-style `syscall` services, deciding
when a run is over — is the environment layer, `Semantics/Env.lean` (§4a). 181 constructors of `Instruction`
(`python3 scripts/trace.py`). Kernel Mode and User Mode, the CP0 access rule (`Status.CU0`), the Reset
exception, the Fixed Mapping MMU, the timer (`Count`/`Compare`), interrupts in interrupt compatibility mode
(software requests, the timer, six hardware input lines that the environment holds deasserted; Interrupt
exception with vector offset `0x180`/`0x200`), standby after `wait`, `IntCtl` and `SRSCtl` (no shadow sets
beyond the normal GPRs, `RDPGPR`/`WRPGPR` on set 0) are modeled: `step = timerTick ∘ stepCore`, where
`stepCore` takes an enabled interrupt, or stays in standby, or fetches and executes. Not modeled: vectored/EIC
interrupts, the TLB, caches, EJTAG, coprocessor 2, the L format and paired-single
(`docs/spec/MIPS-COVERAGE-GAPS.md`).

## 2. Module map and dependency graph

Generated from the `import` lines of the repository (Lean/Std imports omitted).

```
Word ─┬─ Types ─┬─ State ────────────────────────────┐
      │         ├─ Instruction ─┬─ Asm               │
      │         │               └─ Specs/WellFormed  │
      └─ FpOps ─┬─ FpOpsFacts                        ├─ Step ── Specs/Defs ── Specs/* ── StatementsProofs
                └─ FpCompareFacts                    │             │                      (Statements: imports Defs only)
         (Step also imports Word, Types, FpOps) ─────┘             └─ Tests/StepFixtures ── Tests/Step*Tests
                                         Step ── Env (loader, hosted run) ── Specs/Defs, Specs/Fixtures, Tests/StepFixtures
Word, Types, Instruction, FpOps ── Manual/* (independent transcription; nothing else of the model)
Manual/Relation + Step ── Refine/Defs (abs, Inv) ── Refine/Abs ── Refine/* ── Refine/Instr ── Refine/Step ── Refine/Determinism ── StatementsProofs
                                     (Statements: imports Specs/Defs and Refine/Defs only)
```

| File | Contents | Imports (project) |
|---|---|---|
| `Semantics/Word.lean` | `W32 = BitVec 32`, sign extension, signed view | none |
| `Semantics/Types.lean` | `Program` (assembler output, loader input), `State` (the processor), instruction-word builders (`mkRT`/`mkIT`/`mkJT`), constants (`textBase`, `spInit`, `exceptionVectorAddr`) | Word |
| `Semantics/State.lean` | `initialState`, register / FP register accessors, operating mode, the Fixed Mapping MMU (`translate`), memory accessors and writers | Word, Types |
| `Semantics/Instruction.lean` | `Instruction` (183 constructors), `decode` (strict), `encode` | Word, Types |
| `Semantics/Asm.lean` | assembler: source text to `Program` (mnemonic tables, idioms, directives, range checks) | Word, Types, Instruction |
| `Semantics/FpOps.lean` | `Mips.Fp`: pure bit-level IEEE-754 arithmetic, conversions, compare, FCSR | Word |
| `Semantics/FpOpsFacts.lean`, `FpCompareFacts.lean` | kernel-checked facts about `FpOps` (corner cases; meaning of the compare result) | FpOps |
| `Semantics/Step.lean` | `step : State → State`, `run`, exception entry, the instruction semantics (`execBody`) | Word, Types, State, Instruction, FpOps |
| `Semantics/Env.lean` | **not the architecture**: `load`, `hostedStart`, `HaltReason`, `HostEnv`, `Hosted`, `hostStep`, `runHosted`, `runProgram`, the hosted services | Word, Types, State, Instruction, Step |
| `Semantics/Specs/*.lean` | the specification: statement vocabulary (`Defs`, `WellFormed`), plumbing (`Lemmas`, `Tactics`, `Fixtures`), global theorems and one file per instruction family; index `StepSpec.lean` | Step, FpOpsFacts, FpCompareFacts |
| `Semantics/Manual/*.lean` | the independent manual specification: `Arch`, the pseudocode vocabulary, CP0/memory/FPU/exception/interrupt/timer/reset processing, `enc`, one Operation per manual page (`Ops/*`), `InstructionTime`, `Step`, `ChoiceFree`; the model's choices `modelImpl`/`modelOracle` (`docs/MANUAL-SPEC.md`) | Word, Types, Instruction, FpOps (checked by `scripts/manual_independence.py`) |
| `Semantics/Refine/*.lean` | the refinement: `Defs` (`abs`, `Inv`; definitions only), bridges, `<ctor>_refines` per family, the cycle paths, `allInstrRefines`, `step_eq_manual` and corollaries | Manual, Step, Specs (Invariants, RegFileSize, DecodeSpec), Env |
| `Semantics/Statements.lean` | the trusted surface: 216 statements, proofs `sorry` (challenge module of `lake comparator`); imports `Specs/Defs` and `Refine/Defs` only | Specs/Defs, Refine/Defs |
| `Semantics/StatementsProofs.lean` | the same statements proved from `Specs/*` and `Refine/*` (solution module) | Specs/StepSpec, Refine/Determinism |
| `Semantics/Tests/*.lean` | `#guard`s and `example`s for each definition file | the file under test; Step tests import `Tests/StepFixtures` |
| `Semantics.lean`, `Checked.lean` | library roots; `Checked` is what `lake check` replays | all of the above except `Statements` |
| `MipsRun.lean`, `DiffHarness.lean`, `EquivHarness.lean` | executables (run one program to JSON; corpus vs MARS; equivalence corpus), all through the hosted run | Word, Types, State, Instruction, Asm, Step, Env |

`Semantics/Step.lean` does not import `Env`, `Asm`, `FpOpsFacts`, `FpCompareFacts` or any `Specs`/`Tests`
file: the processor model depends only on itself. Within `Specs`, `Lemmas` imports `Defs` and `FpOpsFacts`; `Tactics`
imports `Lemmas`; each family file imports `Tactics` and `Fixtures` (some also `Invariants`, `DelaySlot` or
`Exception`). Spec files do not import `Tests` (their example builders are in `Specs/Fixtures.lean`).
Mathlib is a declared dependency in `lakefile.toml`, but no file of the project imports it (only `Std`
and `Lean.Elab.Tactic`).

## 3. `State`

`Semantics/Types.lean`. All values are `W32`.

| Field | Meaning |
|---|---|
| `pc` | program counter |
| `regs` | 32 GPRs (array of size 32; register 0 is hardwired by `writeReg`) |
| `hi`, `lo` | multiply/divide result registers |
| `fpRegs` | 32 FP registers as raw 32-bit patterns; a double occupies the pair `(N, N+1)` |
| `fcsr` | the FP control/status register as a raw word (eight condition codes, FS, Cause, Enables, Flags, RM) |
| `physMem` | **physical** memory, sparse bytes, `Std.HashMap PAddr UInt8`; absent bytes read as 0 (a pin); reached only through the MMU (`translate`); instructions are fetched from here |
| `pendingBranch : Option W32` | `some t`: the instruction at `pc` is in a branch delay slot and control goes to `t` after it |
| `llBit`, `llAddr` | LL/SC link bit and address |
| `cp0Status`, `cp0Cause`, `cp0Epc`, `cp0BadVAddr`, `cp0ErrorEpc`, `cp0EBase`, `cp0ConfigK0`, `cp0ConfigK23`, `cp0ConfigKU` | the implemented CP0 registers (Status mask `0x3040FF17`, including `UM` and `CU0`; see SPEC-NOTES §9 item 10) |

The state is self-contained: instruction fetch is `readMemWord s s.pc`, from the same memory loads and stores
use, so self-modifying code works (SPEC-NOTES §9 item 6). There is no output field: the output of the hosted
services is environment state (`Hosted.out`, §4a).

**Address translation (the MMU).** The model has the Fixed Mapping MMU (`Config.MT = 3`; MD00090 Vol III
Rev 6.02 Appendix A.1, p.313-317; SPEC-NOTES §9 item 27). Addresses are `VAddr` (what programs compute)
or `PAddr` (indices into `physMem`), both `W32`. `State.lean` holds the whole MMU:
`fixedMappingPA erl va` (Table A.1: kuseg `+0x4000_0000` when `ERL = 0`, identity when `ERL = 1`; kseg0 and
kseg1 → the low 512 MB; kseg2/kseg3 identity), `accessAllowed s va` (Kernel Mode, or a useg address:
Table 4.2) and `translate s va = if accessAllowed s va then some (fixedMappingPA ERL va) else none`.
`translate` is called in exactly one layer: the six `readMem*`/`writeMem*` functions, which check alignment,
translate, and read or write `physMem`; `none` from them is an Address Error, which the caller raises as
AdEL (fetch, load) or AdES (store) with `BadVAddr` = the virtual address. Instruction fetch is
`readMemWord s s.pc`, so fetch, loads and stores share the translation; no other code reads `physMem`
except the loader and observers (§4a).

**Modes and reset.** `kernelMode s` (`UM = 0` or `EXL` or `ERL`), `userMode s = !kernelMode s`, `cp0Usable s`
(Kernel Mode or `CU0`) follow MD00090 Vol III Rev 6.02 ch.3 (p.21-23). `resetException s` is the Reset exception
(§6.2.5, p.89-90: `pc ← 0xBFC0_0000`, `BEV ← 1`, `ERL ← 1`, `Cause.DC ← 0`, `EBase`, `Config.K0 ← 2` (and the pinned
`K23 = KU = 2`), `ErrorEPC ←`
restart PC; undefined registers keep their value); `resetState = resetException powerOnState`, where
`powerOnState` pins every undefined value to 0. `initialState pc` (all registers 0 except `$sp = spInit`,
`Status = 0x20000000`, `EBase = 0x80000000`) is the state after the hosted boot convention (§4a).

## 4. The step pipeline

```
step s:
  fetch   readMemWord s s.pc            (translate s pc, then the big-endian word from State.physMem)
            none (pc not word-aligned,
                  or outside useg in User Mode) -> Address Error (AdEL), BadVAddr = pc
  decode  decode w
            none                         -> Reserved Instruction
                                            (a COP0/CACHE word with CP0 unusable -> Coprocessor Unusable, CE = 0;
                                             a COP1-space word with CU1 = 0 -> Coprocessor Unusable, CE = 1;
                                             a COP2-space word -> Coprocessor Unusable, CE = 2)
  guards  execInstr s instr
            isBranchLike instr and s.pendingBranch.isSome -> Reserved Instruction (pin, §5)
            usesCop1 instr and Status.CU1 = 0              -> Coprocessor Unusable, CE = 1
            usesCop0 instr and not cp0Usable s             -> Coprocessor Unusable, CE = 0
  body    execBody s instr                -> the next State (or an exception, below)
  commit  mkNext / advance: pc := pendingBranch target if one is pending, else pc + 4
```

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

## 5. Delay slots

A branch or jump does not change `pc` to its target. It sets `pc := pc + 4` (the delay-slot instruction) and
`pendingBranch := some t`: `t` is the target if the branch is taken, and the fall-through `pc + 8` if a
conditional branch is not taken, so `pendingBranch.isSome` is exactly "the next instruction is in a delay
slot". The delay-slot instruction goes through `mkNext`/`advance`, which sets `pc := t` and clears the
marker. Consequences: `jal`/`jalr`/`bltzal`... link `pc + 8`; an exception in the delay slot records
`EPC = pc - 4` and `Cause.BD = 1` and abandons the pending target (a later `eret` re-executes the branch);
a control-transfer instruction in a delay slot raises Reserved Instruction (pin: UNPREDICTABLE for branches and
jumps, UNDEFINED for `eret`/`wait`; "UNPREDICTABLE operations may cause arbitrary exceptions" and "must not halt or
hang the processor", MD00086 Vol II-A Rev 6.06 §1.2.1, p.3-4; Release 6 requires exactly this exception, MD00082
Vol I-A Rev 6.01 §5.3.2.1, p.62; SPEC-NOTES §9 item 1).

Branch-likely instructions (`beql`, ..., `bc1fl`, `bc1tl`) behave as ordinary branches when taken. When not
taken, the delay slot is nullified in its own instruction time ("I+1: ... else NullifyCurrentInstruction()",
MD00086 Vol II-A Rev 6.06, BEQL p.73): the branch's step moves to the delay slot with `pendingBranch = some (pc + 8)`
and `State.nullified = true`, and the next step (`nullifiedStep`) skips the slot without fetching it, unless an
interrupt is taken there first (`EPC` = the branch, `BD = 1`; SPEC-NOTES §9 item 1b).

The general statement is `delay_slot_commits_target` (`Specs/DelaySlot.lean`, in the trusted surface):
a non-branch instruction that completes normally with `pc + 4` produces, in a delay slot, the same state with
`pc := t`. Its side conditions are in the README.

## 6. Exceptions

`exceptionEntry s code ce` (Vol III 6.2.3): if `Status.EXL = 0`, `EPC := pc` (or `pc - 4` in a delay slot) and
`Cause.BD` set accordingly; `Cause.ExcCode := code` and `Cause.CE := ce`; `Status.EXL := 1`;
`pc :=` the general vector (`0x80000180` with `EBase` as base when `Status.BEV = 0`, `0xBFC00380` when
`BEV = 1`); `pendingBranch := none`; `llBit := false`. Address errors also set `BadVAddr`. `eret` returns to
`EPC` (`ErrorEPC` when `ERL = 1`), clears `EXL` (or `ERL`) and `llBit`. `Cause.CE` is 0 except for Coprocessor
Unusable. Coprocessor Unusable is raised for any COP1 instruction when `Status.CU1 = 0`; CP0 instructions never
raise it (everything runs as kernel).

## 7. Floating point

`Semantics/FpOps.lean` is the whole FPU model; no host `Float` appears in any definition.

- **Exact + one rounding.** Operands are unpacked to `Exact` (a dyadic rational `(-1)^sign × sig × 2^exp`), the
  operation is performed exactly for add, subtract and multiply (`Exact.add`/`mul`); division and square root
  compute the quotient / root to at least `prec + 2` significant bits with a sticky bit for a nonzero remainder
  (`Exact.div`/`Exact.sqrt`, integer division and `isqrt`), which rounds the same way the true value would; and
  the result is packed by `Format.roundCore` (format, rounding mode, flush flag, exact value), which
  returns the bits plus the three conditions (overflow, tiny, inexact) from which `Rounded.flags` derives the
  IEEE flags.
- **`Env`.** `envOf fcsr` extracts the rounding mode `RM`, the `Enables` and `FS` that an operation consults.
- **`fpUpdate fcsr flags`.** Sets `FCSR.Cause` to this operation's exceptions; if an enabled exception is among
  them it leaves `Flags` untouched and reports a trap, otherwise it ORs the exceptions into `Flags`. `Step.lean`
  finishes every FP arithmetic instruction through `fpFinishS`/`fpFinishD`/`fpFinishCmp`, which either write the
  destination or, on a trap, take the Floating Point exception (ExcCode 15) without writing it.
- **Legacy NaN.** Fraction MSB 1 = signaling; default QNaN `0x7FBFFFFF` / `0x7FF7FFFF_FFFFFFFF`; `abs`/`neg` are
  arithmetic.
- **Evidence.** Corner cases are kernel-checked in `FpOpsFacts.lean`, the meaning of the compare result in
  `FpCompareFacts.lean`; `Tests/FpOpsTests.lean` compares against Lean's `Float32`/`Float` with `#guard`s; the
  QEMU oracle compares whole programs. Since wave 10 `roundCore`, `isqrt` and the arithmetic are proved correct
  against the IEEE definition of `Semantics/FpOpsSpec.lean` (`Semantics/FpOpsCorrect*.lean`; README (d)).

## 8. Test strategy

| Layer | Where | What it checks | Run by |
|---|---|---|---|
| In-build `#guard`/`example` | `Semantics/Tests/*.lean`, `Semantics/Specs/*.lean` | encodings, assembler output, `step` on concrete states, FP corner cases | every build, and `lake check` |
| MARS differential | `tests/corpus/*.asm`, `DiffHarness.lean` | final output and registers vs real MARS 4.5 | gate step 5 |
| Equivalence corpus, expected output | `tests/equiv/*.asm`, `tests/asm/*.asm`, `EquivHarness.lean` | base/variant program pairs; programs whose `# Expected output:` is checked | gate step 6 |
| QEMU/LLVM oracle | `tests/oracle/*.asm`, `tests/oracle/encodings.list`, `scripts/oracle.py` | the same machine code on `qemu-system-mips` (24Kf) and on the model; assembler vs `llvm-mc` | gate step 7 |
| Refinement against the manual transcription | `Semantics/Refine/*.lean` (proof, every state of `Inv`); `EquivHarness.lean` (`Manual.InstructionTime` vs `step` on every state of every corpus/oracle program) | `step_eq_manual`: `step` is one instruction time of `Semantics/Manual` | every build / `lake check`; gate step 6 |
| Traceability | `scripts/trace.py` | every constructor has decode, encode, step arm, spec theorem; `docs/TRACE.md` and the README table are current | gate step 8 |

## 9. The gate

`scripts/gate.sh` runs ten steps: forbidden constructs, build, `lake check`, `lake comparator`, DiffHarness,
EquivHarness, oracle, trace, manuals selftest, hygiene (`scripts/README.md`). Only a full green run writes the
stamp that `scripts/gate-commit.sh` requires.
