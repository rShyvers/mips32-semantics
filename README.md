# MIPS32 Semantics

A formal, machine-checked semantics of the **MIPS32 Release 6** architecture in Lean 4.

The model is a small-step interpreter, `step : State → State`, that covers the whole Release 6 base
instruction set: 203 instructions, the 64-bit IEEE 754-2008 FPU, Coprocessor 0, exceptions, interrupts, the timer and reset. It is
**proved to refine an independent transcription of the MIPS architecture manuals**. The proofs are checked
by the Lean kernel, with no `sorry` and no extra axioms. The model is also tested differentially against QEMU,
LLVM and MARS.

| | |
|---|---|
| Instructions modelled | 203 of 203 Release 6 base instructions (every Vol II-A page accounted for: [coverage](https://github.com/rShyvers/mips32-semantics/blob/documentation/spec/R6-COVERAGE.md)) |
| Headline theorem | `step_eq_manual`: one `step` equals one manual instruction time, for every state satisfying the invariant |
| Trusted surface | 221 statements in [`Semantics/Statements.lean`](Semantics/Statements.lean), checked by `lake comparator` |
| Axioms | `propext`, `Quot.sound`, `Classical.choice` only (`lake check`) |
| Differential tests | 184 QEMU tests (176 programs), 687 LLVM encodings, 29 MARS programs; every instruction executed |

Documentation is on the [`documentation`](https://github.com/rShyvers/mips32-semantics/blob/documentation/README.md) branch. It covers what is proved, tested and trusted ([OVERVIEW](https://github.com/rShyvers/mips32-semantics/blob/documentation/OVERVIEW.md)), the design ([DESIGN](https://github.com/rShyvers/mips32-semantics/blob/documentation/DESIGN.md)), the per-instruction reference ([INSTRUCTION-REF](https://github.com/rShyvers/mips32-semantics/blob/documentation/spec/INSTRUCTION-REF.md)), and every interpretation choice and emulator divergence ([SPEC-NOTES](https://github.com/rShyvers/mips32-semantics/blob/documentation/spec/SPEC-NOTES.md)).

## Target profile

MIPS32 Release 6, as specified by **MD00086 Vol II-A Rev 6.06**, **MD00090 Vol III Rev 6.02** and **MD00082 Vol I-A
Rev 6.01** (the final revisions):

- little-endian; delay-slot branches plus compact branches with forbidden slots; no `HI`/`LO`, no branch-likely;
- a 64-bit FPU (`Status.FR = 1`) with IEEE 754-2008 NaNs (`FIR.Has2008 = 1`, `FCSR.NAN2008 = ABS2008 = 1`);
- Coprocessor 0 with the Vol III exception model, interrupt compatibility mode, Count/Compare;
- the Fixed Mapping MMU; misaligned loads and stores raise Address Error;
- no optional modules (MSA, microMIPS, VZ, MT, DSP, EVA, XPA, MCU, CRC, GINV, VP, EJTAG).

Where the manual and an emulator disagree, the manual wins and the divergence is recorded. The manuals are not
committed because they are copyrighted: `manuals/fetch.sh` downloads them and `manuals/mipsdoc.py` searches them.
The earlier Release 2 model is kept at the tag [`mips32r2-final`](https://github.com/rShyvers/mips32-semantics/tree/mips32r2-final).
Earlier releases (R5, R3, R2, R1) are planned as profiles of this model.

## What is proved

- `Semantics/Step.lean` defines `step`, one instruction time. It handles an interrupt, else a WAIT standby, else
  fetch through the MMU, strict decode, execute and commit. The timer then advances. Every exception is a state
  transition. `run` iterates `step`.
- `Semantics/Manual/` transcribes the manuals' pseudocode independently: each instruction page's Operation, plus
  exception, interrupt, timer and reset processing, and the spec's own decoder built from the format diagrams. The
  gate checks the independence: the transcription may name no model definition outside an allow-list.
- **`step_eq_manual`** (`Semantics/Refine/Step.lean`): for every state satisfying `Refine.Inv`, one `step` is exactly
  one manual instruction time, seen through `Refine.abs`. The manual's UNDEFINED and UNPREDICTABLE choices are
  resolved by explicit pins, which are proved valid (`modelOracle_valid`, `modelImpl_valid`). The theorem covers all 203
  instructions and every non-instruction path. Related results on the trusted surface:
  - `step_refines_manual`, `run_refines_manual`;
  - determinism exactly where the manual makes no choice: `manual_step_deterministic`, `choiceFree_exact`;
  - decoder agreement: `decode_agrees_manual`, `decode_none_manual`;
  - the invariant: `step_preserves_inv`, `inv_resetState`, `inv_load`;
  - reset: `resetState_refines_manual`.
- The FPU (`Semantics/FpOps.lean`) works on bit patterns, with no host floats. It is proved against an IEEE 754
  reference written from MD00082 ch. 6 (`Semantics/FpOpsSpec.lean`). That covers the rounding core, arithmetic,
  conversions, compares, the FCSR update, fused multiply-add, and the RECIP/RSQRT error bounds.
- Trust rests on the 221 statements in `Semantics/Statements.lean` plus the definitions they mention: the model
  files, `Semantics/Manual/*`, `Semantics/Refine/Defs.lean` and `Semantics/FpOpsSpec.lean`.

## Instruction coverage

`python3 scripts/trace.py --readme` generates this table, and the gate fails if it is stale. The per-instruction
matrix is [`TRACE.md`](https://github.com/rShyvers/mips32-semantics/blob/documentation/TRACE.md).

<!-- BEGIN GENERATED: trace.py --readme -->
| Family | Constructors | Spec theorem | MARS corpus | QEMU oracle | Mnemonics |
|---|---:|---:|---:|---:|---|
| R-type reg/reg/reg | 10 | 10 | 10 | 10 | add, addu, sub, subu, and, or, xor, nor, slt, sltu |
| R-type shift | 4 | 4 | 3 | 4 | sll, pause, srl, sra |
| R-type variable shift | 3 | 3 | 3 | 3 | sllv, srlv, srav |
| R-type rotate | 2 | 2 | 0 | 2 | rotr, rotrv |
| R-type jump register | 2 | 2 | 1 | 2 | jalr, jalr.hb |
| Bit count | 2 | 2 | 2 | 2 | clo, clz |
| R-type SPECIAL3 BSHFL sign-extend | 3 | 3 | 0 | 3 | seb, seh, wsbh |
| R-type SPECIAL3 bitfield extract/insert | 2 | 2 | 0 | 2 | ext, ins |
| SPECIAL3 RDHWR | 1 | 1 | 0 | 1 | rdhwr |
| I-type arithmetic and logic with a 16-bit immediate | 7 | 7 | 7 | 7 | addiu, slti, sltiu, andi, ori, xori, aui |
| Release 6 integer instructions | 17 | 17 | 0 | 17 | mul, muh, mulu, muhu, div, mod, divu, modu, seleqz, selnez, lsa, align, bitswap, addiupc, lwpc, auipc, aluipc |
| I-type load/store | 10 | 10 | 9 | 10 | lw, sw, lb, lbu, lh, lhu, sh, sb, ll, sc |
| I-type branch reg/reg | 2 | 2 | 2 | 2 | beq, bne |
| I-type branch reg-only | 2 | 2 | 2 | 2 | blez, bgtz |
| I-type REGIMM zero-comparison branches | 4 | 4 | 2 | 4 | bltz, bgez, nal, bal |
| Instruction-cache synchronize hint | 1 | 1 | 0 | 1 | synci |
| J-type | 2 | 2 | 2 | 2 | j, jal |
| syscall | 1 | 1 | 1 | 1 | syscall |
| R-type trap-on-condition | 6 | 6 | 6 | 6 | teq, tne, tlt, tge, tltu, tgeu |
| Breakpoint, memory barrier and prefetch | 3 | 3 | 1 | 3 | break, sync, pref |
| Coprocessor 0 | 8 | 8 | 0 | 8 | mfc0, mtc0, di, ei, eret, wait, rdpgpr, wrpgpr |
| Coprocessor 1 | 10 | 10 | 6 | 10 | mfc1, mtc1, mfhc1, mthc1, cfc1, ctc1, lwc1, swc1, ldc1, sdc1 |
| FP arithmetic and conversions, single | 18 | 18 | 16 | 18 | add.s, sub.s, mul.s, div.s, sqrt.s, abs.s, mov.s, neg.s, recip.s, rsqrt.s, round.w.s, trunc.w.s, ceil.w.s, floor.w.s, cvt.w.s, cvt.d.s, cvt.s.w, cvt.d.w |
| FP arithmetic and conversions, double | 16 | 16 | 10 | 16 | add.d, sub.d, mul.d, div.d, sqrt.d, abs.d, mov.d, neg.d, recip.d, rsqrt.d, round.w.d, trunc.w.d, ceil.w.d, floor.w.d, cvt.w.d, cvt.s.d |
| Privileged and system instructions | 3 | 3 | 0 | 3 | eretnc, sigrie, cache |
| Release 6 compact branches and jumps | 24 | 24 | 0 | 24 | bc, balc, beqc, bnec, bltc, bgec, bltuc, bgeuc, blezc, bgezc, bgtzc, bltzc, beqzc, bnezc, blezalc, bgezalc, bgtzalc, bltzalc, beqzalc, bnezalc, bovc, bnvc, jic, jialc |
| Longword conversions | 12 | 12 | 0 | 12 | cvt.l.s, cvt.l.d, round.l.s, round.l.d, trunc.l.s, trunc.l.d, ceil.l.s, ceil.l.d, floor.l.s, floor.l.d, cvt.s.l, cvt.d.l |
| Release 6 FP instructions | 26 | 26 | 0 | 26 | cmp.af.s, cmp.af.d, bc1eqz, bc1nez, sel.s, sel.d, seleqz.s, seleqz.d, selnez.s, selnez.d, maddf.s, maddf.d, msubf.s, msubf.d, max.s, max.d, min.s, min.d, maxa.s, maxa.d, mina.s, mina.d, class.s, class.d, rint.s, rint.d |
| Virtual processors | 2 | 2 | 0 | 2 | dvp, evp |
| **Total** | **203** | **203** | **83** | **203** | |

Columns count constructors of `Instruction`. "Spec theorem": has a `<ctor>_spec_raw`/`_spec` theorem. "MARS corpus" / "QEMU oracle": the mnemonic occurs as an instruction in a `tests/corpus/*.asm` / `tests/oracle/*.asm` program (a text scan; it shows the instruction is exercised, not that every behaviour is).
<!-- END GENERATED -->

## Building and checking

```sh
lake exe cache get          # mathlib build cache
lake build                  # the model, proofs and in-build tests
scripts/gate.sh             # the full gate (about 10 minutes); --quick while iterating
lake exe MipsRun prog.asm   # assemble and run one program, JSON out (--bare, --reset, --coverage, --max-steps N)
```

[`scripts/gate.sh`](scripts/README.md) is the single source of truth. It runs these steps:

1. forbidden constructs and manual-spec independence;
2. `lake build` with zero warnings;
3. `lake check`;
4. `lake comparator`;
5. the MARS differential harness;
6. the equivalence harness, including `Manual.InstructionTime` vs `step`;
7. the QEMU/LLVM oracle (behaviour, encodings, and a check that every instruction is executed);
8. traceability;
9. the manuals tool selftest;
10. hygiene.

Prerequisites:

- `elan` (the toolchain is pinned in `lean-toolchain`, Lean 4.35.0);
- a JRE (step 5);
- `qemu-system-mipsel` (`-cpu mips32r6-generic`) and LLVM 21 (`llvm-mc`, `ld.lld`, `llvm-objdump`, `llvm-objcopy`;
  set `ORACLE_LLVM_DIR`) for step 7;
- Python 3;
- the manual texts (`manuals/fetch.sh`, which needs `curl` and `pdftotext`) for step 9.

To read the documentation locally, mount its branch at `docs/` (gitignored here). Paths such as
`docs/spec/SPEC-NOTES.md` in the sources then resolve:

```sh
git worktree add docs documentation
```

## Layout

```
Semantics/Word, Types, State, Instruction, FpOps, Step .lean   the model (definitions only)
Semantics/Exec/                per-family execution tables used by Step.lean
Semantics/Env.lean, Asm.lean   the environment (loader, hosted services; outside the architecture), the assembler
Semantics/Manual/              the independent transcription of the manuals
Semantics/Refine/              the proof that step refines it (step_eq_manual)
Semantics/FpOpsSpec.lean, FpOpsCorrect*.lean   the IEEE 754 reference and the FP correctness proofs
Semantics/Specs/               per-family and global theorems about step
Semantics/Statements.lean, StatementsProofs.lean, comparator.json   the trusted surface
Semantics/Tests/               #guard / example tests
Checked.lean, Semantics.lean   library roots (Checked is what lake check replays)
DiffHarness, EquivHarness, MipsRun .lean   executables
tests/                         corpus (MARS), equiv, asm, oracle (QEMU/LLVM) programs
scripts/                       gate.sh, gate-commit.sh, oracle.py, trace.py, independence checks
manuals/                       mipsdoc.py, fetch.sh, SHA256SUMS (manual PDFs and texts are not committed)
vendor/mars/                   the MARS 4.5 jar (differential oracle only)
```

## License

Licensed under the [Apache License, Version 2.0](LICENSE); see [NOTICE](NOTICE).

MARS 4.5 (`vendor/mars/Mars4_5.jar`) is third-party software under the MIT license, vendored unmodified only as a
differential-testing oracle. The MIPS manuals are not included; the sources cite them with short quotations only.
A demo built on an earlier version of these semantics is at
[mips32-semantics-demo](https://github.com/rShyvers/mips32-semantics-demo).
