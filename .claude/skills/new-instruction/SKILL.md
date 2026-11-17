---
name: new-instruction
description: Step-by-step recipe to add or complete one MIPS32 instruction end to end (constructor, decode/encode, step arm, spec theorem, assembler, reference entry, tests, TRACE). Use when implementing a missing instruction or closing a gap listed in docs/spec/MIPS-COVERAGE-GAPS.md.
---

# /new-instruction -- definition of done, in order

Conventions are by pattern; open the neighbouring instruction of the same shape and copy it. Files change often, so grep, do not trust line numbers.
Own these files for the duration (one writer per file): `Instruction.lean`, the family's `Semantics/Exec/<Family>.lean`, its `Semantics/Asm/<Family>.lean`, the one `Semantics/Specs/<Family>.lean`,
the matching `Semantics/Tests/*.lean`, `INSTRUCTION-REF.md`, one new test program. Check first that the instruction is in the target profile
(MIPS32 Release 6, see CLAUDE.md) and is not classified as removed or optional in `docs/spec/R6-COVERAGE.md`.

0. Look it up first (`/mips-manual`): `mipsdoc.py insn NAME`; note the Release 6 semantics, exceptions raised, delay-slot/forbidden-slot behaviour,
   UNPREDICTABLE cases (each needs a pin in SPEC-NOTES), printed page.
1. `Semantics/Instruction.lean`: add a constructor to `inductive Instruction` next to its family, with the field shape of its siblings
   (R-type `rs rt rd`/`shamt`, I-type `rs rt imm`, J `target`, FP `fmt fs ft fd`...), each field `W32` and commented with the manual page.
2. Same file: a `decode` clause (R-type under the SPECIAL funct match, I/J under the opcode match, REGIMM/COP1/SPECIAL2/SPECIAL3 in their
   sub-matches) and the inverse `encode` clause using the `mkRT`/`mkIT`/`mkJT` builders (`Types.lean`). Reserved bit patterns decode to `none`.
   Add the constructor to `Instruction.WellFormed` (`Semantics/Specs/WellFormed.lean`) and to the round trip in `Semantics/Specs/DecodeSpec.lean`
   (`decode_encode` must still hold for every constructor). Add round-trip evidence in `Semantics/Tests/InstructionTests.lean`.
3. `Semantics/Step.lean`: add the arm to the `match instr with` in `execBody`, in the family's block. Reads via `readReg s (regIdx rs)`, writes via
   `writeReg`, results via `mkNext s ...`; address errors/overflow go through the exception model (`takeException`, `takeAddressException`), never a
   bare halt. Branches follow the delay-slot machinery (`pendingBranch`; add the constructor to `isBranchLike`). COP1 instructions must be in `usesCop1`
   (Coprocessor Unusable) and finish through `fpFinishS`/`fpFinishD`/`fpFinishCmp` if arithmetic. Add a step test in the matching `Semantics/Tests/Step*Tests.lean`.
4. `Semantics/Specs/<Family>.lean` (find the family in the table in `Specs/StepSpec.lean`): `theorem <ctor>_spec_raw (p) (s) (w <fields>)
   (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.<ctor> ..)) (hpb : s.pendingBranch = none) : step p s = <RHS>` written with the
   `...Spec` helpers and state primitives, proved by the one-word script `step_spec` (FPU: add `(hcu : cu1Enabled s = true)` and use `fp_step_spec`).
   If the script fails, write the proof by hand; no `bv_decide`, no `native_decide`, no `sorry`. Add the zero-register, taken/not-taken or overflow
   corollaries the neighbours have, and a satisfiable `#guard` built with `Specs/Fixtures.lean`. Docstring cites INSTRUCTION-REF and SPEC-NOTES.
   The theorem restates what `step` computes; the evidence that it matches the manual is the manual lookup of step 0 and the tests of step 7.
   To put a theorem into the trusted surface: statement in `Semantics/Statements.lean`, same statement proved with `_root_.<name> ...` at the same position
   in `Semantics/StatementsProofs.lean`, name in `comparator.json` (see `docs/PROOF-NOTES.md`). Only global results and one representative per family belong there.
5. `Semantics/Asm.lean`: add `("mnemonic", opcode/funct, .form)` to the matching table (`rTable`, `iTable`, `bTable`, `cop1Table`, ...) or a dedicated
   parser case if the operand shape is new. Add a `#guard` in `Semantics/Tests/AsmTests.lean` and a form line in `tests/oracle/encodings.list`
   (`oracle.py --encodings` checks it against `llvm-mc`; every constructor's mnemonic must be listed).
6. On the `documentation` branch (mounted at `docs/`; `git worktree add docs documentation`), `docs/spec/INSTRUCTION-REF.md`: a `### mnemonic (FORM)` section (and a row in the summary table) with Lean names, Pre-R6 semantics, exceptions, and a
   citation (document+revision+section+printed page). Pins and divergences go in `docs/spec/SPEC-NOTES.md`; remove the item from `MIPS-COVERAGE-GAPS.md`.
7. Tests, in this order of preference: a `tests/oracle/<name>.asm` program (QEMU `mips32r6-generic` compares final registers/memory/CP0; directives `# oracle: ...`,
   see `scripts/README.md`; a QEMU difference from the manual is a declared `expect-deviation` with a citation, never a silent mismatch); and, if MARS
   supports the instruction, `tests/corpus/<name>.asm` (print observable results with syscalls 1/11/10; `lake exe DiffHarness`).
8. `scripts/gate.sh --fix` (regenerates the README coverage table); then `docs/check.sh --fix` (regenerates `docs/TRACE.md`) and check the
   instruction's row in `docs/TRACE.md`: manual page, REF entry, decode, encode, step arm, spec theorem, tests.
9. `/gate "<subject>"`. Done only when the full gate is green. Then `docs/check.sh --sync` and commit the docs on the `documentation` branch.
