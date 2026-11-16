# MIPS32 Semantics

A small-step operational semantics of a pre-Release-6 MIPS32 processor in Lean 4. The repository also has an
assembler, machine-checked proofs that the semantics refines an independent transcription of the architecture
manuals, two differential oracles (MARS 4.5; `qemu-system-mips` with `llvm-mc`), and one gate script that runs
everything.

This branch holds the semantics only: code, proofs, tests and the gate. The prose documentation is on the orphan
branch `documentation`, including the full account of what is proved, tested and trusted (`OVERVIEW.md`). Mount it
at `docs/` (gitignored here); paths such as `docs/spec/SPEC-NOTES.md` in the sources then resolve:

```sh
git worktree add docs documentation
```

## Target profile

The target is pre-Release-6 MIPS32 with the Release 2 feature set:

- big-endian, one branch delay slot, branch-likely, `HI`/`LO`;
- a 32-bit FPU (`Status.FR = 0`) with legacy FP (`FIR.Has2008 = 0`);
- Coprocessor 0 with the Vol III exception model, interrupt compatibility mode, Count/Compare;
- the Fixed Mapping MMU.

The normative manuals are **MD00086 Vol II-A Rev 6.06**, **MD00090 Vol III Rev 6.02** and **MD00082 Vol I-A Rev
6.01**, read for their pre-Release-6 wording. They are not committed because they are copyrighted:
`manuals/fetch.sh` downloads them and `manuals/mipsdoc.py` looks things up (see `manuals/AGENTS.md`). Where the manual
and an emulator disagree, the manual wins; MARS and QEMU are test oracles only. Release 6, MIPS64, DSP, MSA,
microMIPS and MIPS16e are out of scope.

## What is proved

- `Semantics/Step.lean` defines `step : State → State`, one instruction time. It handles an interrupt, else a WAIT
  standby, else a nullified branch-likely slot, else fetch through the MMU, strict decode, execute and commit. The
  timer then advances. Every exception is a state transition. `run` iterates `step`.
- `Semantics/Manual/` transcribes the manuals' pseudocode independently: each instruction page's Operation, plus
  exception, interrupt, timer and reset processing, and the spec's own decoder built from the format diagrams. Gate
  step 1 checks the independence: the transcription names no definition of the model beyond an allow-list.
- **`step_eq_manual`** (`Semantics/Refine/Step.lean`): for every state satisfying `Refine.Inv`, one `step` is exactly
  one manual instruction time, seen through `Refine.abs`. The manual's UNDEFINED/UNPREDICTABLE choices are resolved
  by the model's pins, which are proved valid (`modelOracle_valid`, `modelImpl_valid`). The theorem covers all 183
  instructions and every non-instruction path, and the trusted surface also has these relatives:
  - `step_refines_manual` and `run_refines_manual`;
  - determinism exactly where the manual makes no choice: `manual_step_deterministic`, `choiceFree_exact`;
  - decoder agreement: `decode_agrees_manual`, `decode_none_manual`;
  - the invariant: `step_preserves_inv`, `inv_resetState`, `inv_load`;
  - reset: `resetState_refines_manual`.
- The FPU (`Semantics/FpOps.lean`, bit patterns, no host floats) is proved against an IEEE 754 reference written from
  MD00082 ch. 6 (`Semantics/FpOpsSpec.lean`). That covers the rounding core, arithmetic, conversions, compares, the
  FCSR update, the multiply-add family, and the RECIP/RSQRT error bounds.
- The trusted surface is `Semantics/Statements.lean`: 216 statements with proofs elided. `lake comparator` checks
  them against `Semantics/StatementsProofs.lean`. Trust rests on those statements plus the definitions they mention:
  - the model files;
  - `Semantics/Manual/*` and `Semantics/Refine/Defs.lean`;
  - `Semantics/FpOpsSpec.lean`.
- `lake check` replays everything in the kernel, and only `propext`, `Classical.choice` and `Quot.sound` may appear as
  axioms. No `sorry`, `native_decide` or `bv_decide` appears outside the comparator challenge file.

Limits, pins and divergences are listed in full in `docs/OVERVIEW.md` and `docs/spec/SPEC-NOTES.md`.

## Instruction coverage

`python3 scripts/trace.py --readme` generates this table, and the gate fails if it is stale. The per-instruction
matrix is `docs/TRACE.md`.

<!-- BEGIN GENERATED: trace.py --readme -->
| Family | Constructors | Spec theorem | MARS corpus | QEMU oracle | Mnemonics |
|---|---:|---:|---:|---:|---|
| R-type reg/reg/reg | 12 | 12 | 12 | 12 | add, addu, sub, subu, and, or, xor, nor, slt, sltu, movn, movz |
| R-type shift | 3 | 3 | 3 | 3 | sll, srl, sra |
| R-type variable shift | 3 | 3 | 3 | 3 | sllv, srlv, srav |
| R-type rotate | 2 | 2 | 0 | 2 | rotr, rotrv |
| R-type mult/div | 4 | 4 | 4 | 4 | mult, multu, div, divu |
| R-type move | 2 | 2 | 2 | 2 | mflo, mfhi |
| R-type move, write direction | 2 | 2 | 2 | 2 | mthi, mtlo |
| R-type jump register | 4 | 4 | 2 | 4 | jr, jalr, jr.hb, jalr.hb |
| R-type SPECIAL2 bit-count | 2 | 2 | 2 | 2 | clo, clz |
| R-type GPR multiply, SPECIAL2 | 1 | 1 | 1 | 1 | mul |
| R-type multiply-accumulate, SPECIAL2 | 4 | 4 | 4 | 4 | madd, maddu, msub, msubu |
| R-type SPECIAL3 BSHFL sign-extend | 3 | 3 | 0 | 3 | seb, seh, wsbh |
| R-type SPECIAL3 bitfield extract/insert | 2 | 2 | 0 | 2 | ext, ins |
| SPECIAL3 RDHWR | 1 | 1 | 0 | 1 | rdhwr |
| I-type arith/logic | 7 | 7 | 7 | 7 | addi, addiu, slti, sltiu, andi, ori, xori |
| I-type lui | 1 | 1 | 1 | 1 | lui |
| I-type load/store | 10 | 10 | 10 | 10 | lw, sw, lb, lbu, lh, lhu, sh, sb, ll, sc |
| I-type unaligned load/store | 4 | 4 | 0 | 4 | lwl, lwr, swl, swr |
| I-type branch reg/reg | 2 | 2 | 2 | 2 | beq, bne |
| I-type branch reg-only | 2 | 2 | 2 | 2 | blez, bgtz |
| I-type REGIMM zero-comparison branches | 4 | 4 | 4 | 4 | bltz, bgez, bltzal, bgezal |
| I-type "branch likely" family | 8 | 8 | 0 | 8 | beql, bnel, blezl, bgtzl, bltzl, bgezl, bltzall, bgezall |
| I-type REGIMM trap-immediate family | 6 | 6 | 6 | 6 | teqi, tnei, tgei, tgeiu, tlti, tltiu |
| Instruction-cache synchronize hint | 1 | 1 | 0 | 1 | synci |
| J-type | 2 | 2 | 2 | 2 | j, jal |
| syscall | 1 | 1 | 1 | 1 | syscall |
| R-type trap-on-condition | 9 | 9 | 7 | 9 | teq, tne, tlt, tge, tltu, tgeu, break, sync, pref |
| Coprocessor 0 | 8 | 8 | 0 | 8 | mfc0, mtc0, di, ei, eret, wait, rdpgpr, wrpgpr |
| Coprocessor 1 | 15 | 15 | 6 | 15 | mfc1, mtc1, mfhc1, mthc1, cfc1, ctc1, lwc1, swc1, ldc1, sdc1, lwxc1, ldxc1, swxc1, sdxc1, prefx |
| Arithmetic, single | 18 | 18 | 16 | 18 | add.s, sub.s, mul.s, div.s, sqrt.s, abs.s, mov.s, neg.s, recip.s, rsqrt.s, round.w.s, trunc.w.s, ceil.w.s, floor.w.s, cvt.w.s, cvt.d.s, cvt.s.w, cvt.d.w |
| Arithmetic, double | 16 | 16 | 10 | 16 | add.d, sub.d, mul.d, div.d, sqrt.d, abs.d, mov.d, neg.d, recip.d, rsqrt.d, round.w.d, trunc.w.d, ceil.w.d, floor.w.d, cvt.w.d, cvt.s.d |
| Compare | 2 | 2 | 2 | 2 | c.cond.s, c.cond.d |
| Conditional moves | 10 | 10 | 6 | 10 | movf.s, movt.s, movf.d, movt.d, movn.s, movz.s, movn.d, movz.d, movf, movt |
| Multiply-add family | 8 | 8 | 0 | 8 | madd.s, msub.s, nmadd.s, nmsub.s, madd.d, msub.d, nmadd.d, nmsub.d |
| FP branches | 4 | 4 | 2 | 4 | bc1f, bc1t, bc1fl, bc1tl |
| **Total** | **183** | **183** | **119** | **183** | |

Columns count constructors of `Instruction`. "Spec theorem": has a `<ctor>_spec_raw`/`_spec` theorem. "MARS corpus" / "QEMU oracle": the mnemonic occurs as an instruction in a `tests/corpus/*.asm` / `tests/oracle/*.asm` program (a text scan; it shows the instruction is exercised, not that every behaviour is).
<!-- END GENERATED -->

## Building and the gate

```sh
lake exe cache get      # mathlib build cache
scripts/gate.sh         # the full gate (about 6 minutes); --quick while iterating (not green)
lake exe MipsRun prog.asm   # assemble and run one program, JSON out (--bare, --reset, --max-steps N)
```

The gate (`scripts/README.md`) runs these steps:

1. forbidden constructs and manual-spec independence;
2. `lake build` with zero warnings;
3. `lake check`;
4. `lake comparator`;
5. DiffHarness vs MARS;
6. EquivHarness, including `Manual.InstructionTime` vs `step`;
7. the QEMU/LLVM oracle;
8. traceability;
9. the manuals tool selftest;
10. hygiene.

Only a fully green run writes the stamp that `scripts/gate-commit.sh` needs.

Prerequisites:

- `elan` (toolchain pinned in `lean-toolchain`);
- a JRE (step 5);
- `qemu-system-mips` and LLVM 21 (`llvm-mc`, `ld.lld`, `llvm-objdump`, `llvm-objcopy`; set `ORACLE_LLVM_DIR`) for step 7;
- Python 3;
- the manual texts (`manuals/fetch.sh`, which needs `curl` and `pdftotext`) for step 9.

## Layout

```
Semantics/Word, Types, State, Instruction, FpOps, Step .lean   the model (definitions only)
Semantics/Env.lean, Asm.lean   the environment (loader, hosted services; outside the architecture), the assembler
Semantics/Manual/              the independent transcription of the manuals
Semantics/Refine/              the proof that step refines it (step_eq_manual)
Semantics/FpOpsSpec.lean, FpOpsCorrect*.lean   the IEEE 754 reference and the FP correctness proofs
Semantics/Specs/               per-family and global theorems about step
Semantics/Statements.lean, StatementsProofs.lean, comparator.json   the trusted surface
Semantics/Tests/               #guard / example tests
Checked.lean, Semantics.lean   library roots (Checked is what lake check replays)
DiffHarness, EquivHarness, MipsRun .lean   executables
tests/                         corpus (MARS), equiv, asm, oracle (QEMU) programs
scripts/                       gate.sh, gate-commit.sh, oracle.py, trace.py, independence checks
manuals/                       mipsdoc.py, fetch.sh, SHA256SUMS (manual PDFs and texts are not committed)
vendor/mars/                   the MARS 4.5 jar (differential oracle only)
```

## License / provenance

MARS 4.5 (`vendor/mars/Mars4_5.jar`) is a third-party simulator, vendored here only as a differential-testing
oracle; see its own license. Everything else in this repository was written for this project. The semantics was
extracted from the demo [mips32-semantics-demo](https://github.com/rShyvers/mips32-semantics-demo) (formerly VibeCheck) so it can be read, built and reviewed on its own.
