---
name: new-instruction
description: Step-by-step recipe to add or complete one MIPS32 instruction end to end (constructor, decode/encode, step arm, spec theorem, assembler, reference entry, differential test, TRACE). Use when implementing a missing instruction or closing a gap listed in docs/TRACE.md.
---

# /new-instruction -- definition of done, in order

Conventions are by pattern; open the neighbouring instruction of the same shape and copy it. Files change often, so grep, do not trust line numbers.
Own these files for the duration (one writer per file): Instruction.lean, Step.lean, Asm.lean, StepSpec.lean, INSTRUCTION-REF.md, one new corpus file.

0. Look it up first (`/mips-manual`): `mipsdoc.py insn NAME`; note the Pre-R6 semantics, exceptions raised, delay-slot/likely behaviour, printed page.
1. `Semantics/Instruction.lean`: add a constructor to `inductive Instruction` next to its family, with the field shape of its siblings
   (R-type `rs rt rd`/`shamt`, I-type `rs rt imm`, J `target`, FP `fmt fs ft fd`...), each field `W32` and commented with the manual page.
2. Same file: a `decode` clause (R-type under the SPECIAL funct match, I/J under the opcode match, REGIMM/COP1/SPECIAL2/SPECIAL3 in their sub-matches)
   and the inverse `encode` clause using the `mkRT`/`mkIT`/`mkJT` builders (defined in Types.lean). Add round-trip evidence beside the others: a
   `decode (mk... ) = some (.ctor ..)` and `encode (.ctor ..) = ...` `example ... := by decide` or `#guard`. Reserved bit patterns must decode to `none`.
3. `Semantics/Step.lean`: add the arm to the `match instr with` in private `execInstr`, in the family's block. Reads via `readReg s (regIdx rs)`,
   writes via `writeReg`, results via `mkNext s ...`; address errors/overflow go through the exception model (see neighbours
   such as `lw` and `add`), never a bare halt. Branches/jumps follow the delay-slot machinery (`pendingBranch`, `isBranchLike`; extend it if the new
   instruction is branch-like).
4. `Semantics/Specs/StepSpec.lean`: `theorem <ctor>_spec_raw (p) (s) (w <fields>) (hfetch : fetchWord p s.pc = some w)
   (hdecode : decode w = some (.<ctor> ..)) (hpb : s.pendingBranch = none) : step p s = <spec-level RHS>`. The RHS is written with the
   `...Spec` helpers (`regIdxSpec`, `readReg`, `signExt16`, ...), independent of Step.lean's code. Standard proof shape:
   `obtain ⟨pc, regs, ..⟩ := s; simp only at hpb; subst hpb; unfold step; rw [hfetch]; dsimp only; rw [hdecode]; dsimp only; rfl`
   (fall back to `simp`/`split` on the arm's `if`/`match`; no `bv_decide`, no `native_decide`, no `sorry`). Add the `_nontrivial`/zero-register
   preservation cases wherever the existing `step_preserves_zero_register_nontrivial` style theorem enumerates constructors.
   Docstring cites INSTRUCTION-REF section and SPEC-NOTES item.
5. `Semantics/Asm.lean`: add `("mnemonic", opcode/funct, .form)` to the matching table (`rTable`, `iTable`, `jTable`, `bTable`, `cop1Table`, ...) or a
   dedicated parser case if the operand shape is new; pseudo-ops expand in the pseudo section. Add a `#guard` that assembling a source line yields the expected word.
6. `docs/spec/INSTRUCTION-REF.md`: a `### mnemonic (FORM)` section (and a row in the summary table) with Lean names, Pre-R6 semantics, exceptions, and a
   citation (document+revision+section+printed page). Divergences from MARS go in `docs/spec/SPEC-NOTES.md`.
7. Test: add `tests/corpus/<name>.asm` that prints observable results (syscalls 1/11/10), covering edge cases (negative, overflow, boundary);
   run `lake exe MipsRun tests/corpus/<name>.asm` and, if MARS supports it, `lake exe DiffHarness`. If MARS lacks the instruction or is wrong,
   state so, test against the manual by hand-computed expectations in a `#guard`, and record the divergence.
8. `python3 scripts/trace.py` and check the new row has: manual page, REF entry, decode, encode, step arm, spec theorem, test.
9. `/gate "<subject>"`. Done only when the full gate is green.
