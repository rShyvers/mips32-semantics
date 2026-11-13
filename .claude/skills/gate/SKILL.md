---
name: gate
description: Run the full verification gate and, only if it is fully green, commit locally. Use at the end of every wave or whenever asked to "gate", "verify and commit", or before reporting a tree as done. Args = the commit subject.
---

# /gate -- run the gate, commit only on green

Args: `$ARGUMENTS` is the commit subject (ask for one if empty; do not invent a vague one).

1. Confirm you are not on `main`/`master` (`git branch --show-current`). If you are, stop and tell the owner.
2. Run the FULL gate with TRACE regeneration, from the repo root:
   `scripts/gate.sh --fix`
   It takes several minutes (`lake check` ~2-5 min). Do not run other `lake` jobs in the same tree meanwhile.
   Never pass `--allow-warnings` unless the owner explicitly said so in this conversation.
3. Read the result: last line `== gate: GREEN ...` or `RED`, plus `.gate/last-run.json`.
4. If RED (or PARTIAL):
   - Report the failing step(s) by name, the one-line note, and the excerpt from `.gate/logs/NN-step.log`
     (the script already printed the last 40 lines; quote them verbatim).
   - Do NOT commit, do NOT stage, do NOT edit the gate or its allowlist to get past it.
   - Stop. Fixing is a separate task for the file owner.
5. If GREEN:
   - Commit with `scripts/gate-commit.sh "$ARGUMENTS"` (add a body file as 2nd arg if the owner gave one).
     It re-verifies the tree id against the stamp, stages everything, and adds the Gate trailers.
   - If it refuses (stale stamp: the tree changed after the gate), re-run step 2; never work around it.
   - Report: the commit hash it prints, the step table, corpus/equiv counts, axioms, and any SKIP (e.g. manuals).
6. Verify the commit landed: `git log -1 --stat | head`.

## Forbidden
- `git commit` by hand, `git commit --no-verify`, `git add` + commit shortcuts, amending the gate trailers.
- `--allow-warnings` without the owner's say-so; editing `scripts/gate-allow.txt` to silence a hit.
- Pushing, merging, opening PRs, or committing on `main`/`master`.
- Claiming green from `--quick`, `--only` or `--from`: those never write a stamp and are not a gate.
