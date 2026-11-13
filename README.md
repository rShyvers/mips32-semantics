# Semantic MIPS

A small-step operational semantics of a pre-Release-6 MIPS32 processor, written in Lean 4, with an
assembler, a specification and proofs, two differential oracles (MARS 4.5; `qemu-system-mips` with
`llvm-mc`), and a gate script that runs all of them.

Extracted from [VibeCheck](https://github.com/rShyvers/VibeCheck) (a
hackathon project that builds a consumer product on top of this semantics)
so the semantics can be read, built, and reviewed on their own, with no
dependency on anything else in that project.

## What this is

- `Semantics/Step.lean`: `step : Program → State → StepResult` executes **one instruction** (fetch, strict
  decode, execute, commit) and returns the next `State` or a halt reason. `run` is `step` iterated under a fuel
  bound. `step` is total.
- `Semantics/Instruction.lean`: the `Instruction` type (178 constructors), `decode` (strict) and `encode`.
- `Semantics/Asm.lean`: an assembler from source text to a `Program` (labels, directives, idioms, range checks).
- `Semantics/FpOps.lean`: the floating-point unit, defined on bit patterns without host floats.
- `Semantics/Specs/`, `Semantics/Statements.lean`: the specification and its proofs (see below for exactly what
  they establish).
- `DiffHarness.lean`, `EquivHarness.lean`, `MipsRun.lean`, `scripts/oracle.py`: the test executables.
- `scripts/gate.sh`: the ten-step gate.

## Target profile, and what "normative" means

The target is a **pre-Release-6 MIPS32 processor with the Release 2 feature set**: big-endian, one branch delay
slot, branch-likely instructions, `HI`/`LO`, a **32-bit FPU** (`Status.FR = 0`) with **legacy FP**
(`FIR.Has2008 = 0`, legacy NaN encoding), Coprocessor 0 with the exception model of Vol III.

The latest manual revisions are normative, read for their pre-Release-6 wording: **MD00086 Vol II-A Rev 6.06**,
**MD00090 Vol III Rev 6.02**, **MD00082 Vol I-A Rev 6.01**. Where the manual and an emulator disagree, the manual
wins and the difference is recorded (`docs/spec/SPEC-NOTES.md`); MARS and QEMU are test oracles, not specifications.
Where the manual says UNPREDICTABLE the model makes a choice and records it as a pin in `SPEC-NOTES.md`; a pin is
not an architectural statement. Emulator-compatibility toggles may be added later; none exist.
Release 6, MIPS64, DSP, MSA, microMIPS and MIPS16e are out of scope for good.

## What is proved, what is tested, what is trusted

Read this section before the numbers elsewhere. It says what each kind of evidence does and does not establish.

**(a) Kernel-checked.** `lake check` replays the library `Checked` (`Checked.lean`: the model, all of
`Semantics/Specs`, `StatementsProofs`, the facts files and the tests) in the kernel and the gate requires that the
axioms used are a subset of `propext`, `Classical.choice`, `Quot.sound`. The gate's step 1 rejects `sorry`, `admit`,
`axiom`, `native_decide`, `bv_decide`, `partial def`, `unsafe`, `@[implemented_by]` and `@[extern]` in the code of
every file under `Semantics/` (comments and strings stripped); the one allow-listed `sorry` is in
`Semantics/Statements.lean` (below), which nothing in `Checked` imports. So there is no `sorry` in anything
`Checked` imports.

**(b) The trusted surface for `lake comparator`.** `Semantics/Statements.lean` (1027 lines) states **66 theorems**
with their proofs elided. `Semantics/StatementsProofs.lean` states the same theorems in the same order and proves
each by the real theorem of the same name in `Semantics/Specs/`. `lake comparator` (config: `comparator.json`)
checks, for each name, that the solution proves the *same statement* as the challenge, uses no axiom outside the
three above, and passes the kernel. It does not check that a statement is the right one. To review the project you
read `Statements.lean`, plus the definitions that it mentions: the model files (`Word`, `Types`, `State`,
`Instruction`, `FpOps`, `Step`) and the statement vocabulary `Semantics/Specs/Defs.lean` and
`WellFormed.lean`. The 66 statements are a selection: every global theorem below and at least one per-instruction
statement per family. The arrangement and its limits are in `docs/PROOF-NOTES.md`.

**(c) The per-instruction `_spec_raw` theorems restate the implementation.** There is one for each of the 178
constructors (`python3 scripts/trace.py`). 176 of the 178 `_spec_raw` theorems are proved by unfolding `step` and closing with `rfl`
(`step_spec`/`fp_step_spec` in `Semantics/Specs/Tactics.lean`; `break_spec_raw` and `syscall_spec_raw` have explicit
proofs), and each states what `step` computes for that
instruction in terms of the model's own helper functions (`readReg`, `writeReg`, `signExt16`, ...; the `...Spec`
names in `Defs.lean` are abbreviations for the real definitions, not independent copies). They pin the behaviour
against regression and make each instruction's semantics readable in isolation. **They are not independent of the
implementation**: a mistake in `Step.lean` that is also a mistake in the reader's understanding of the manual
survives them. The evidence that the semantics matches the architecture is the manual review recorded in
`docs/AUDIT.md` and `SPEC-NOTES.md`, and the differential tests in (e).

The results that are genuinely global, or independent of how an individual instruction is written:

| Result | Where | In the trusted surface |
|---|---|---|
| `decode (encode i) = some i` for every constructor, under `WellFormed` | `Specs/DecodeSpec.lean` | `decode_encode` |
| `$zero` is unchanged by every `step` and by every `run`; a write to `$zero` is never observable | `Specs/Invariants.lean` | `step_preserves_zero_register`, `run_preserves_zero_register`, `run_initialState_zero_register`, `zero_write_not_observable` |
| register files keep size 32 under `step`; `run` from `initialState` is well-formed | `Specs/RegFileSize.lean` | `step_preserves_wellFormed`, `run_initialState_wellFormed` |
| exception entry: vector, `EXL`, pending branch abandoned, `LLbit` cleared, `EPC`/`Cause.BD` with and without delay slot, `ExcCode`, `CE` | `Specs/Exception.lean` | `exceptionEntry_always`, `_exl0_not_in_delay_slot`, `_exl0_in_delay_slot`, `_exl1`, `_excCode` (`_ce` is in `Exception.lean` only) |
| fetch/decode failure: misaligned `pc`, no instruction, undecodable word, Reserved Instruction | `Specs/Fetch.lean` | `step_misaligned_pc`, `step_no_instruction`, `step_undecodable`, `step_reserved_instruction` |
| general delay-slot theorem | `Specs/DelaySlot.lean` | `delay_slot_commits_target`; `branch_in_delay_slot_halts` |
| Coprocessor Unusable | `Specs/FpuCommon.lean` | `fp_coprocessor_unusable` |
| FP trap: an enabled FP exception takes ExcCode 15 and writes no FP register | `Specs/FpuCommon.lean` | `fpCompletesS_trap` (single-precision finish helper; the double and compare analogues `fpCompletesD_trap`, `fpCompletesCmp_trap` are in `FpuCommon.lean`) |
| FCSR round trip through `ctc1`/`cfc1` | `Specs/FpuControl.lean` | `fcsr_ctc1_cfc1_roundtrip` |
| FP compare: what the result bit means for all operands (unordered, equal, less, in terms of sign/exponent/fraction fields) | `Semantics/FpCompareFacts.lean`, `Specs/FpuCompare.lean` | `c_lt_s_sets_cc` only; the characterisation is kernel-checked but not in the surface |

The delay-slot theorem `delay_slot_commits_target` has a side condition: the instruction at `pc` is not branch-like
(`isBranchLike instr = false`), `s.pc + 4` is not the exception vector, it completes normally outside a delay slot
with `pc + 4`, and then in a delay slot with pending target `t` it yields the same state with `pc := t`.

**(d) Floating point.** Arithmetic is exact rational arithmetic followed by one rounding (add, subtract, multiply
exactly; divide and square root to `prec + 2` bits with a sticky bit; then `Format.roundCore`), defined on bit
patterns with no host floats in any definition. Its correctness against IEEE-754 is established by kernel-checked
corner-case theorems (`Semantics/FpOpsFacts.lean`) and by differential `#guard` tests against Lean's `Float32`/
`Float` (`Semantics/Tests/FpOpsTests.lean`) plus the QEMU oracle. **There is no general correctness proof of the
rounding core (`Format.roundCore`) or of the integer square root (`isqrt`).** That the compare predicates' field
order equals the order of the rational values is tested, not proved (`FpCompareFacts.lean` says so).

**(e) Differential evidence.**
- *MARS 4.5* (`tests/corpus`, 37 programs, `DiffHarness`): the model and the real simulator agree on every program.
  MARS defaults to little-endian memory, has no FCSR/FP exceptions, and lacks several instructions, so the corpus
  uses endian-invariant patterns and covers the original instruction subset best (SPEC-NOTES §9).
- *QEMU* (`qemu-system-mips -M malta -cpu 24Kf`, `tests/oracle`, `scripts/oracle.py`): the same machine code at the
  same addresses runs on QEMU and on the model, and registers, `HI`/`LO`, FPRs, FCSR, CP0 state, memory, output and
  termination are compared. The last gate run (`.gate/last-run.json`) reports 135 tests (126 programs in
  `tests/oracle`, 9 runnable programs of `tests/asm`): 126 pass, 9 are **declared deviations where QEMU departs
  from the manual** (the manual wins), 0 known model bugs. The deviations, with the citations from the tests'
  own `# oracle: expect-deviation` directives (`SPEC-NOTES.md` §10 has the table):
  misaligned `sc` (MD00086 Vol II-A Rev 6.06, SC, p.349); misaligned `lwxc1`/`ldxc1`/`swxc1`/`sdxc1`, QEMU performs
  the access (LWXC1 p.254, LDXC1 p.218, SWXC1 p.406, SDXC1 p.364); `FCSR.FS` flush leaves Underflow/Inexact clear
  (MD00082 Vol I-A Rev 6.01 §6.7.2.4, p.102); `abs`/`neg` of a signaling NaN does not signal Invalid (MD00086
  ABS.fmt p.32, NEG.fmt p.307; two tests); Inexact set with an enabled Overflow trap (MD00082 §6.7.2.6, p.102).
  Not covered: EBase relocation, `Status.ERL` writes, interrupts, `wait`.
- *LLVM encoding oracle* (`llvm-mc -triple=mips-unknown-elf -mcpu=mips32r2`): the assembler's output is compared
  word for word on 594 forms (`tests/oracle/encodings.list`): 581 identical, 13 declared differences (our
  `li`/`la`/`move`/`abs` expansions follow MARS/SPIM).

**(f) What is trusted.** Lean and its kernel; the three standard axioms; the manuals *as read by the authors*
(nothing machine-checks the reading); the statements in `Statements.lean` and the definitions they mention (the
model itself); the assembler, which is **tested but not proved** (`Semantics/Tests/AsmTests.lean`, the LLVM oracle,
the MARS corpus); the harnesses, `scripts/oracle.py` and the QEMU boot stub; and `docs/spec`, which is
human-written.

**(g) UNPREDICTABLE pins and known divergences.** Every place where the manual leaves behaviour open and the model
picks one, and every deliberate difference from MARS or QEMU, is in `docs/spec/SPEC-NOTES.md` (§9 and §10).

## Instruction coverage

Generated by `python3 scripts/trace.py --readme` from the sources (the same data as `docs/TRACE.md`); the gate
fails if this block is stale (`trace.py --check-readme`). The per-instruction table, with links to the decode and
encode clauses, the step arm, the spec theorems, the manual page and the tests, is `docs/TRACE.md`.

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
| R-type jump register | 2 | 2 | 2 | 2 | jr, jalr |
| R-type SPECIAL2 bit-count | 2 | 2 | 2 | 2 | clo, clz |
| R-type GPR multiply, SPECIAL2 | 1 | 1 | 1 | 1 | mul |
| R-type multiply-accumulate, SPECIAL2 | 4 | 4 | 4 | 4 | madd, maddu, msub, msubu |
| R-type SPECIAL3 BSHFL sign-extend | 3 | 3 | 0 | 3 | seb, seh, wsbh |
| R-type SPECIAL3 bitfield extract/insert | 2 | 2 | 0 | 2 | ext, ins |
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
| J-type | 2 | 2 | 2 | 1 | j, jal |
| syscall | 1 | 1 | 1 | 1 | syscall |
| R-type trap-on-condition | 9 | 9 | 7 | 9 | teq, tne, tlt, tge, tltu, tgeu, break, sync, pref |
| Coprocessor 0 | 6 | 6 | 0 | 5 | mfc0, mtc0, di, ei, eret, wait |
| Coprocessor 1 | 15 | 15 | 6 | 15 | mfc1, mtc1, mfhc1, mthc1, cfc1, ctc1, lwc1, swc1, ldc1, sdc1, lwxc1, ldxc1, swxc1, sdxc1, prefx |
| Arithmetic, single | 18 | 18 | 16 | 18 | add.s, sub.s, mul.s, div.s, sqrt.s, abs.s, mov.s, neg.s, recip.s, rsqrt.s, round.w.s, trunc.w.s, ceil.w.s, floor.w.s, cvt.w.s, cvt.d.s, cvt.s.w, cvt.d.w |
| Arithmetic, double | 16 | 16 | 10 | 16 | add.d, sub.d, mul.d, div.d, sqrt.d, abs.d, mov.d, neg.d, recip.d, rsqrt.d, round.w.d, trunc.w.d, ceil.w.d, floor.w.d, cvt.w.d, cvt.s.d |
| Compare | 2 | 2 | 2 | 2 | c.cond.s, c.cond.d |
| Conditional moves | 10 | 10 | 6 | 10 | movf.s, movt.s, movf.d, movt.d, movn.s, movz.s, movn.d, movz.d, movf, movt |
| Multiply-add family | 8 | 8 | 0 | 8 | madd.s, msub.s, nmadd.s, nmsub.s, madd.d, msub.d, nmadd.d, nmsub.d |
| FP branches | 4 | 4 | 2 | 4 | bc1f, bc1t, bc1fl, bc1tl |
| **Total** | **178** | **178** | **119** | **176** | |

Columns count constructors of `Instruction`. "Spec theorem": has a `<ctor>_spec_raw`/`_spec` theorem. "MARS corpus" / "QEMU oracle": the mnemonic occurs as an instruction in a `tests/corpus/*.asm` / `tests/oracle/*.asm` program (a text scan; it shows the instruction is exercised, not that every behaviour is).
<!-- END GENERATED -->

## What is not modeled

Nothing here is implemented, and an access raises Reserved Instruction (or Coprocessor Unusable for COP2 words).
Details, manual citations and priorities are in `docs/spec/MIPS-COVERAGE-GAPS.md`.

- Instructions: `rdhwr`, `rdpgpr`, `wrpgpr`, `cache`, `tlbp`, `tlbr`, `tlbwi`, `tlbwr`, `sdbbp`, `deret`, the
  coprocessor-2 family (`cop2`, `mfc2`, `mtc2`, `cfc2`, `ctc2`, `lwc2`, `swc2`, `ldc2`, `sdc2`, `bc2f`/`bc2t`/
  `bc2fl`/`bc2tl`), `luxc1`, `suxc1`, the L format (`cvt.l`, `round.l`, `trunc.l`, `ceil.l`, `floor.l`,
  `cvt.s.l`, `cvt.d.l`) and paired-single (`*.ps`, `alnv.ps`, `cvt.ps.s`, `cvt.s.pl`/`pu`, `pll`/`plu`/`pul`/`puu`).
  `pause` and `nal` decode (as `sll $0,$0,5` and `bltzal $0`) but have no assembler mnemonic.
- State: `Count`/`Compare` and all interrupts, `HWREna`, `IntCtl`, `SRSCtl`, shadow register sets, the TLB and
  mapped address translation, caches, `WatchLo`/`WatchHi`, user mode (`Status.UM`/`KSU`/`CU0`; everything runs as
  kernel), EJTAG, coprocessor 2, `Config2`..`Config5`.
- Self-modifying code: instruction fetch reads the immutable `Program`, not memory.
- The manuals themselves are inconsistent about the L format with `FR = 0` (`FIR.L = 1` is required, the L-format
  instructions are UNPREDICTABLE with `FR = 0`); the model reports `FIR.L = 0` (SPEC-NOTES §9 item 13).

## Building and the gate

One command runs everything: `scripts/gate.sh` (about 6 minutes; `--quick` runs steps 1, 8, 9, 10 only and is not
green). The steps (`scripts/README.md`): 1 forbidden constructs; 2 `lake build` of all targets with zero project
warnings; 3 `lake check` (kernel replay, axioms); 4 `lake comparator`; 5 DiffHarness vs MARS; 6 EquivHarness;
7 oracle (QEMU and LLVM); 8 traceability (`trace.py --check`, `docs/TRACE.md` and the README table current);
9 manuals tool selftest (SKIP when the manual texts are absent); 10 hygiene. Only a fully green run writes the stamp
that `scripts/gate-commit.sh` requires.

```sh
lake exe cache get      # fetch the mathlib build cache (Mathlib is a declared dependency; no module imports it)
scripts/gate.sh         # the full gate
lake build MipsRun && lake exe MipsRun prog.asm      # assemble and run one program, JSON out
```

Prerequisites: `elan` (the toolchain is pinned in `lean-toolchain`: `leanprover/lean4:v4.35.0`); a JRE (step 5 runs
`vendor/mars/Mars4_5.jar`); `qemu-system-mips` and LLVM (`llvm-mc`, `ld.lld`, `llvm-objdump`, `llvm-objcopy`;
point `ORACLE_LLVM_DIR` at them if they are not in `/usr/lib/llvm-21/bin` or on `PATH`) for step 7, which fails,
never skips, without them; Python 3 (standard library only). Individual targets: `lake build Semantics Checked
DiffHarness EquivHarness MipsRun`, `lake check`, `lake comparator`.

The manuals are not in the repository: they are copyrighted by MIPS Technologies, Inc., and their front matter
prohibits copying without written permission, so the PDFs and the extracted texts are `.gitignore`d. Fetch them
with `docs/spec/manuals/fetch.sh` (needs `curl` and `pdftotext`; it verifies `SHA256SUMS`) and look things up
with `docs/spec/manuals/mipsdoc.py` (`AGENTS.md` there). Without them step 9 is a SKIP and `docs/TRACE.md`
cannot be regenerated with its manual column.

## Repository layout

```
lakefile.toml, lean-toolchain, lake-manifest.json   Lean project files (targets: Semantics, Checked, DiffHarness, EquivHarness, MipsRun)
Checked.lean, Semantics.lean   library roots; Checked is what `lake check` replays
comparator.json                the 66 trusted theorem names, challenge and solution modules
Semantics/Word, Types, State, Instruction, Asm, FpOps, Step .lean   the model (definitions only)
Semantics/FpOpsFacts.lean, FpCompareFacts.lean   kernel-checked facts about FpOps
Semantics/Specs/               the specification: Defs, WellFormed (vocabulary); Lemmas, Tactics, Fixtures (plumbing);
                               DecodeSpec, Exception, Fetch, DelaySlot, Invariants, RegFileSize (global theorems);
                               one file per instruction family (Arith, Shift, MulDiv, ..., FpuArith, ...); StepSpec (index)
Semantics/Statements.lean      the trusted surface (66 statements, proofs elided)
Semantics/StatementsProofs.lean  the same statements, proved from Specs
Semantics/Tests/               #guard / example tests for each definition file
DiffHarness.lean, EquivHarness.lean, MipsRun.lean   executables
tests/corpus/  tests/equiv/  tests/asm/   programs for DiffHarness / EquivHarness (base-variant pairs; programs with checked output)
tests/oracle/                  QEMU oracle programs (*.asm with `# oracle:` directives), encodings.list, harness/boot.s, gen/gen_tests.py
scripts/                       gate.sh, gate-commit.sh, oracle.py, trace.py, README.md
docs/spec/                     INSTRUCTION-REF.md, SPEC-NOTES.md, MIPS-COVERAGE-GAPS.md, manuals/ (lookup tool; PDFs not committed)
docs/PROOF-NOTES.md            reading order, the comparator arrangement, proof history
docs/TRACE.md                  generated instruction traceability matrix
docs/AUDIT.md                  record of what was checked against the manuals
DESIGN.md                      module map, State, the step pipeline, delay slots, exceptions, FP model
vendor/mars/                   the MARS 4.5 jar, used by DiffHarness only
```

## How to review this project

1. `docs/PROOF-NOTES.md` (135 lines): reading order and the comparator arrangement.
2. The model (4418 lines in all): `Semantics/Word.lean` (32), `Types.lean` (268), `State.lean` (144),
   `Instruction.lean` (1370), `FpOps.lean` (1172), `Step.lean` (1432). `DESIGN.md` is the map.
3. The statements: `Semantics/Specs/Defs.lean` (115), `WellFormed.lean` (194), then `Semantics/Statements.lean` (1027).
4. For any instruction family: `Semantics/Specs/<Family>.lean`; the index and table is `Specs/StepSpec.lean` (109).
5. `docs/TRACE.md` (486 lines, generated): one row per instruction, from manual page to tests.
6. `docs/spec/SPEC-NOTES.md`: every pin and divergence; `docs/spec/MIPS-COVERAGE-GAPS.md`: what is missing;
   `docs/AUDIT.md`: what was checked against the manuals.
7. Not required for trust: `Specs/Lemmas.lean`, the proof-device parts of `DelaySlot`, `Invariants`, `RegFileSize`,
   `FpOpsFacts`, `FpCompareFacts` and `Tactics`; the kernel replays them.

## MipsRun

`lake exe MipsRun [--max-steps N] [prog.asm]` assembles a program (file or stdin) and runs it (default bound
1000000 steps), printing one JSON object. Exit code 0: assembled and ran to a halt or the step limit; 1: assembly
failed (`"assembled": false`, `"error"` set, other fields `null`); 2: usage or I/O error (no JSON).

Fields (success): `assembled`, `halted`, `halt_reason`, `steps`, `output`, `registers` (by ABI name), `error`
(`null`); then `halt` (`{"kind": ...}`: `exit`, `unhandled_exception` with `code`/`epc`/`badvaddr`, `no_instruction`
with `pc`, `branch_in_delay_slot` with `pc`, or `limit`), `initial` and `final` (each: `pc`, `gpr`, `hi`, `lo`,
`fpr` as raw 32-bit values, `fcsr`, `fp_cond_flag` (= FCSR bit 23, kept for compatibility), `ll_bit`, `ll_addr`,
`pending_branch`, `cp0` with `status`, `cause`, `epc`, `badvaddr`, `errorepc`, `ebase`), `fcsr_mask`, `image`
(`[address, word]` for every assembled word) and `memory` (every nonzero aligned word of the final memory).

**The `halt_reason` strings changed from the VibeCheck-era ones** (`illegal_instruction:0x...`,
`address_error:0x...`, `arithmetic_overflow`, `branch_in_delay_slot`). Overflow, address errors, reserved
instructions, `break`, traps and unknown syscalls are now architectural exceptions, so the strings are `exit`,
`unhandled_exception:<name>:epc=0x<EPC>` (address errors append `:badvaddr=0x<BadVAddr>`; `<name>` is
`address_error_load`, `address_error_store`, `syscall`, `breakpoint`, `reserved_instruction`, `coprocessor_unusable`,
`arithmetic_overflow`, `trap` or `exccode_N`), `no_instruction:0x<pc>` and `branch_in_delay_slot`; `halt_reason` is
`null` when the step limit is reached.

## License / provenance

MARS 4.5 (`vendor/mars/Mars4_5.jar`) is a third-party simulator, vendored
here only as a differential-testing oracle; see its own license. Everything
else in this repository was written for this project.
