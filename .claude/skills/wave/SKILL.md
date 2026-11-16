---
name: wave
description: Orchestration checklist for running a wave of sub-agents on this repo (parallel proof/implementation/audit work) from planning through gated commit. Use when you are about to delegate work to more than one agent or when a task is too big for one agent.
---

# /wave -- run a wave of sub-agents safely

## 1. Plan
- Write the wave goal and a per-agent table: agent, task, FILES OWNED (one writer per file), read-only files, model.
- Parallel writers get their own worktree: `git worktree add .claude/worktrees/<name> -b wave/<name>`, then copy `.lake`
  into it (`cp -r .lake <worktree>/`). Never let two agents write the same file, even in different regions.
- Cheap models (haiku/sonnet) for mechanical or read-only work (gate runs, audits, greps); strongest model for proofs
  and spec decisions. Use the project agents in `.claude/agents/`: `mips-spec-auditor`, `lean-proof-engineer`, `gate-runner`.

## 2. Brief each agent (the brief is all it knows)
Include: goal; owned files; forbidden files; the hard rules (point at CLAUDE.md, restate no-sorry/no-axiom/no-statement-weakening);
exact commands (`scripts/gate.sh --quick` while iterating, full `scripts/gate.sh` before reporting; no `git commit`);
the scratch location outside the repo; report format: files changed, theorems added/removed, anything weakened (or "none"),
commands run with observed results, open problems. "Report only what you ran."

## 3. Verify -- never believe a report
- Run the gate yourself (or via `gate-runner`) on the merged tree; do not trust an agent's "all green".
- Spot-check 2-3 claims: `git diff --stat`, grep the theorem statements for weakening (changed hypotheses, `True`, deleted
  cases), rerun one reported reproducer, confirm no theorem or test disappeared (`scripts/trace.py` counts).
- Check agents stayed in their owned files (`git diff --name-only`).

## 4. Integrate and commit
- Merge worktree branches yourself (no force, no history rewriting). Resolve conflicts by hand, then re-gate.
- `/gate "<subject>"` -- `scripts/gate.sh --fix` then `scripts/gate-commit.sh`. Only a fully green gate is committed, locally.
- `--fix` regenerates the README coverage table so it is part of the same commit.
- Docs live on the `documentation` branch (mounted at `docs/`, its own worktree). After the code commit, update them there,
  run `docs/check.sh --fix` and `docs/check.sh --sync`, and commit on that branch.
- Never push, merge to main, or open a PR unless the owner asks.

## 5. Ledger
Keep a short running ledger for the owner (in your reply, not in the repo): decisions taken, statements changed, divergences
from MARS/manual and their citations, items deferred, gate result with commit hash, and anything an agent could not verify.
