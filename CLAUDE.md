# semantic-mips -- agent rules (auto-loaded; obey)

Formal semantics of MIPS32 in Lean 4 (+ Mathlib): decode/encode, assembler, small-step `step`,
and machine-checked spec theorems. Validated differentially against MARS 4.5 and the manuals.

## Target profile (do not drift)
- Pre-Release-6 MIPS32, Release 2 feature set, big-endian, legacy FP (`FIR.Has2008=0`).
- The latest manual revisions in `docs/spec/manuals/` (Vol I 6.01, Vol II-A 6.06, Vol III 6.02)
  are NORMATIVE, read for the pre-R6 wording. R6-only instructions/registers are out of scope.
- MARS is only a differential oracle. When MARS and the architecture disagree, the architecture wins;
  record the divergence in `docs/spec/SPEC-NOTES.md`.

## Hard rules
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `partial def`, `unsafe`,
  `@[implemented_by]`, `@[extern]`. `bv_decide` adds a native axiom that fails `lake check`.
- Never weaken a theorem statement to make it provable without saying so, loudly, in your report.
- Never delete a theorem or test silently. Removals are listed in the report with the reason.
- Every claim about the manual is looked up with `mipsdoc.py` and cited as
  document + revision + instruction/section + PRINTED page. Never cite from memory.
- Every reported bug needs an executed reproducer. Report only what you ran.
- Do not claim "green" from a partial run; only the full gate (below) counts.

## The gate (one command)
`scripts/gate.sh` is the single source of truth. Steps: 1 forbidden constructs (code only, comments/strings
stripped); 2 `lake build` of all targets, zero project warnings; 3 `lake check` kernel replay, axioms subset of
{propext, Classical.choice, Quot.sound}; 4 `lake comparator` ("Your solution is okay!"); 5 DiffHarness vs real MARS
(needs java; pass count must equal the number of `tests/corpus/*.asm`); 6 EquivHarness; 7 traceability
(`trace.py --check` + `docs/TRACE.md` up to date); 8 manuals tool selftest (SKIP if texts absent); 9 hygiene.
- While iterating: `scripts/gate.sh --quick` (steps 1,7,8,9; NOT green, no stamp). Use `--only STEP`/`--from STEP`.
- Before reporting done / before commit: `scripts/gate.sh --fix` (full; regenerates TRACE.md). Only a full green run
  writes `.gate/green`, bound to the exact tree content.
- Commit ONLY with `scripts/gate-commit.sh "<subject>" [body-file]` (or `--run`). Never `git commit` by hand,
  never `--no-verify`, never `--allow-warnings` unless the owner said so.
- Never push, merge, open PRs, or commit on `main`/`master` unless the owner asks. Commits are local.
- The `/gate` skill wraps this. `lake check` takes ~2-5 min; do not run it in parallel with other lake jobs in one tree.

## File map
- `Semantics/Word.lean` W32 = BitVec 32 helpers. `Types.lean` `State` record, `Program`, `HaltReason`, `StepResult`. `State.lean` register/memory/CP0 accessors (`readReg`, `writeReg`, ...).
- `Semantics/Instruction.lean` `Instruction` constructors, `decode`, `encode`, round-trip examples. TRUSTED.
- `Semantics/Asm.lean` assembler: mnemonic tables, pseudo-ops, parsing. `Semantics/FpOps.lean` FP arithmetic helpers.
- `Semantics/Step.lean` `step`/`run`, exception model. TRUSTED. `Semantics/Specs/StepSpec.lean` `<ctor>_spec_raw` + derived theorems.
- `Semantics/Specs/DecodeSpec.lean` decode-level specs. `Semantics.lean`/`Checked.lean` library roots (Checked = what `lake check` replays).
- `comparator.json` the trusted theorem list for `lake comparator`. TRUSTED. `lakefile.toml` targets.
- `DiffHarness.lean` corpus vs MARS. `EquivHarness.lean` equivalence corpus. `MipsRun.lean` run one .asm -> JSON.
- `tests/corpus/*.asm` differential programs; `tests/equiv/*.asm` equivalence pairs; `vendor/mars/` MARS jar + source.
- `docs/spec/INSTRUCTION-REF.md` per-instruction reference; `SPEC-NOTES.md` decisions/divergences; `docs/TRACE.md` GENERATED matrix.
- `docs/spec/manuals/` manual texts + `mipsdoc.py` lookup tool (see its `AGENTS.md`). `scripts/` gate and trace tooling.
- Trusted surface (changes need explicit owner-visible mention): Instruction.lean, Step.lean, State.lean, Types.lean,
  `comparator.json`, `lakefile.toml`, `Checked.lean`, and the theorem STATEMENTS in StepSpec.lean.

## Running things
- Run a program: `lake exe MipsRun prog.asm` (JSON out). `lake exe DiffHarness` (needs java). `lake exe EquivHarness`.
- Build: `lake build Semantics Checked DiffHarness EquivHarness MipsRun`. Check: `lake check`; `lake comparator`.
- Traceability: `python3 scripts/trace.py` (writes docs/TRACE.md), `--check` (CI-style), `--out FILE`.
- Manuals: `python3 docs/spec/manuals/mipsdoc.py insn NAME | section v3 "Cause Register" | search "..." | page v2 177`.
  Texts are not committed; `docs/spec/manuals/fetch.sh` fetches them. See the `mips-manual` skill.

## Concurrency (multi-agent waves)
- One writer per file. State your file ownership at the start; everything else is read-only.
- Parallel writers use separate git worktrees (`git worktree add`, then copy `.lake` in); merge is the orchestrator's job.
- Never run destructive git: no reset --hard, checkout --, clean, stash, rebase, force-push, branch switching in a shared tree.
- Do not run `lake` in a tree another agent is building (lock contention) -- use your own worktree.
- Scratch files go outside the repo (the session scratchpad), never in the tree.
- Re-read a file immediately before editing it; others may have changed it.
- The `/wave` skill is the orchestration checklist.

## Definition of done for an instruction
1. Constructor in `Instruction` (Instruction.lean).  2. `decode` clause and `encode` clause, plus a
round-trip `example`/`#guard`.  3. `execInstr` arm in Step.lean (private `execInstr`, called by `step`) (exceptions via the CP0 model).
4. `<ctor>_spec_raw` theorem in StepSpec.lean, proved, no sorry.  5. Assembler mnemonic in Asm.lean (+ `#guard` on its encoding).
6. INSTRUCTION-REF.md entry citing document+revision+section+printed page, with a SPEC-NOTES entry for any MARS divergence.
7. A differential program in `tests/corpus/` (or an oracle/equiv test) exercising it.  8. `docs/TRACE.md` regenerated.
9. Full gate green. Recipe: the `new-instruction` skill.
