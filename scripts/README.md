# scripts/ -- the gated flow

Rule: every wave ends with a full gate run; only a fully green gate is committed, locally. One deterministic script enforces it.

| Script | What it does |
|---|---|
| `gate.sh` | Runs the 9 gate steps, prints `[n/9] name ... PASS/FAIL/SKIP (s)`, keeps logs in `.gate/logs/`, always writes `.gate/last-run.json`; on a full green run writes the stamp `.gate/green` (tree id of the exact verified content, timestamp, HEAD, toolchain, per-step results). |
| `gate-commit.sh "<subject>" [body-file]` | Commits only if on a non-main branch, the stamp exists, and the current tree id equals the stamp. Stages `git add -A`, re-verifies the staged tree, commits with a `Gate:` trailer block and `Co-Authored-By` last. Never pushes. `--run` runs the gate first. |
| `install-hooks.sh` | `git config core.hooksPath .githooks` for this clone (idempotent). The `pre-commit` hook then blocks any commit whose staged tree differs from the stamp. Bypass in an emergency: `git commit --no-verify`. |
| `trace.py` | Generates `docs/TRACE.md` (`--check`: exit 1 on missing step arm / spec theorem / sorry; `--out FILE`). |
| `gate-allow.txt` | Optional, absent by default. Lines `path:construct  # reason` allow a forbidden construct in one file. A line without a reason is an error. |

## Steps

| # | name | PASS when |
|---|---|---|
| 1 | forbidden | no `sorry admit native_decide bv_decide axiom partial def unsafe @[implemented_by @[extern` in CODE of `Semantics/**`, `Checked/Semantics/DiffHarness/EquivHarness/MipsRun.lean` (comments, docstrings, strings stripped first; `gate.sh --selftest` shows the stripper's cases) |
| 2 | build | `lake build Semantics Checked DiffHarness EquivHarness MipsRun` exits 0 and has 0 compiler warnings from project files (`--allow-warnings` relaxes) |
| 3 | check | `lake check` exits 0 and its `Uses axioms:` line is a subset of propext, Classical.choice, Quot.sound (missing line = FAIL) |
| 4 | comparator | `lake comparator` exits 0 and prints `Your solution is okay!` |
| 5 | diffharness | `lake exe DiffHarness` exits 0, and `SUMMARY: all N corpus programs PASS` has N = number of `tests/corpus/*.asm`; java and `vendor/mars/Mars4_5.jar` required (missing = FAIL) |
| 6 | equivharness | `lake exe EquivHarness` exits 0 with `SUMMARY: all N equivalence cases behaved as claimed` |
| 7 | trace | `trace.py --check` passes and regenerating TRACE.md matches the committed one (ignoring the `- git HEAD:` line); `--fix` rewrites it |
| 8 | manuals | `mipsdoc.py selftest` passes; SKIP (not PASS) if the manual texts are absent |
| 9 | hygiene | no conflict markers, no file >5 MB, no pdf to be committed; `git diff --check` is a warning only |

Flags: `--quick` (1,7,8,9 only; NOT green, no stamp), `--from STEP`, `--only STEP` (number, letter a-i or name), `--allow-warnings`,
`--fix`, `--json` (also print the JSON), `--selftest`. Exit 0 iff no step failed. Env for testing: `GATE_ROOT`, `GATE_DIR`, `GATE_CORPUS_DIR`.
The stamp is written only if the tree id is unchanged between the start and the end of the run.

## Typical flow
```
scripts/gate.sh --quick                 # while iterating: seconds, not a green gate
scripts/gate.sh --fix                   # end of wave: full gate (minutes), regenerates TRACE.md
scripts/gate-commit.sh "Subject line"   # commits exactly the verified tree, locally
# or both at once: scripts/gate-commit.sh --run "Subject line"
```

## CI
Replace the five gate `run:` steps in `.github/workflows/ci.yml` (keep checkout, elan, cache, `lake exe cache get`; add `actions/setup-java` and
`fetch.sh` only if the manuals step should not SKIP) with:
```yaml
      - name: Gate (build, check, comparator, DiffHarness, EquivHarness, trace, hygiene)
        run: |
          export PATH="$HOME/.elan/bin:$PATH"
          scripts/gate.sh
      - name: Upload gate logs
        if: always()
        uses: actions/upload-artifact@v4
        with: { name: gate-logs, path: .gate/ }
```
CI needs `python3` and `java` on the runner (ubuntu-latest has both). The stamp written in CI is irrelevant; the exit code is the verdict.

## Troubleshooting
- "stale stamp" / hook blocks: something changed after the gate (even a whitespace edit or a regenerated TRACE.md). Re-run `scripts/gate.sh`.
- "tree changed while the gate ran": another agent or editor wrote files during the run; re-run when the tree is quiet.
- java missing / `Mars4_5.jar` missing: step 5 FAILs by design. Install a JRE; the jar lives in `vendor/mars/`.
- Lock contention ("waiting for lock", hangs): another `lake` is running in the same tree. Wait, or gate from your own worktree
  (`git worktree add`, copy `.lake` in). `lake check` alone takes 2-5 min.
- TRACE.md stale: `python3 scripts/trace.py` (or `gate.sh --fix`) and include it in the commit.
- manuals SKIP: run `docs/spec/manuals/fetch.sh` (needs `pdftotext`); a SKIP does not block the stamp but is recorded in the commit trailer.
- Reading failures: logs are `.gate/logs/NN-name.log`; `.gate/` is gitignored.
