# mips32-semantics — `documentation` branch

This is an orphan branch that holds only the project's prose documentation. It describes the MIPS32 Release 6 model (the Release 2 model is kept at tag `mips32r2-final` of the code repository). The code branch holds the semantics: the
Lean sources, proofs, tests and the gate. Mount this branch at `docs/` inside a checkout of the code branch. Repo-relative
paths in both branches, such as `docs/spec/SPEC-NOTES.md` and `../Semantics/Step.lean`, then resolve:

    git worktree add docs documentation       # from the code checkout's root; `docs/` is gitignored there

| File | What it is |
|---|---|
| `OVERVIEW.md` | The long-form overview: what is proved, tested and trusted, and its limits (the former code README) |
| `DESIGN.md` | Architecture of the Lean development (model, specs, manual spec, refinement, harnesses) |
| `MANUAL-SPEC.md` | Design of the independent manual transcription `Semantics/Manual/` and its transcription guide |
| `PROOF-NOTES.md` | Proof reading order, the comparator arrangement, notes per wave |
| `AUDIT.md` | Audit record |
| `TRACE.md` | GENERATED instruction traceability matrix (`scripts/trace.py`) |
| `spec/INSTRUCTION-REF.md` | Per-instruction semantics with manual citations (document, revision, section, printed page) |
| `spec/SPEC-NOTES.md` | Pins (choices the manual leaves open) and divergences of MARS/QEMU from the manual |
| `spec/R6-COVERAGE.md` | All 263 pages of Vol II-A 6.06 classified (implemented, removed in R6, optional module absent, TLB, idiom, gap) |
| `spec/COMPLIANCE.md` | Compliance matrix of the CP0 registers (Vol III ch. 9) against the manuals (`tools/compliance.py check`) |
| `spec/MIPS-COVERAGE-GAPS.md` | What the model does not cover: 0 open gaps, and what the profile leaves out on purpose |

## Keeping it in step with the code

`SYNC` records the code-branch commit these docs describe. Run `./check.sh` from the mounted `docs/` directory. It
fails when any of these holds:

1. `TRACE.md` differs from fresh `scripts/trace.py` output.
2. `tools/compliance.py check` fails (CP0 register matrix and R6 coverage table must list every manual section / instruction page once). This needs the manual texts, fetched with `manuals/fetch.sh` on the code branch.
3. The code under `Semantics/`, `tests/`, `scripts/` or the Lean roots changed after the `SYNC` commit.

`./check.sh --fix` regenerates `TRACE.md`. After reviewing the docs against the code changes, `./check.sh --sync`
records the current code HEAD in `SYNC`. It does so only when checks 1 and 2 pass.

Manual citations use `python3 manuals/mipsdoc.py` on the code branch (see `manuals/AGENTS.md` there).
