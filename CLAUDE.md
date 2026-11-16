# mips32-semantics -- agent rules (auto-loaded; obey)

Formal semantics of MIPS32 in Lean 4: decode/encode, assembler, small-step `step`, and machine-checked spec theorems.
Validated differentially against MARS 4.5 and QEMU/LLVM, and against the manuals by review.

## Target profile (do not drift)
- MIPS32 **Release 6** (the final MIPS32), owner decision 2026-11-16, on branch `dev/r6` until it is complete.
  Little-endian only (`Config5.DEC=0`, `Config.BE=0`), 64-bit FPU (`Status.FR=1`), IEEE 754-2008 NaN
  (`FIR.Has2008=1`, `FCSR.NAN2008=ABS2008=1`), Fixed Mapping MMU, no optional modules (MSA, microMIPS, VZ, MT, DSP,
  EVA, XPA, MCU, CRC, GINV, VP, EJTAG). Misaligned load/store = Address Error. The pre-R6 Release 2 model is kept
  only at tag `mips32r2-final`; it is replaced in place, with no compatibility layer.
- Earlier releases will be added later, backwards (R5, R3, R2, R1), as profiles. Key release-specific pieces
  cheaply now (a `Release`/`Profile` with one arm; decoder tables per release; a CP0 layout table) and do not
  implement other releases.
- The manual revisions in `manuals/` (Vol I 6.01, Vol II-A 6.06, Vol III 6.02) are NORMATIVE.
- Style: clever is fine, a massive if/match block is not. Prefer tables keyed by opcode/format, per-format
  helpers and shared combinators; the trusted, auditor-facing files stay plain and readable.
- QEMU (`qemu-system-mipsel -cpu mips32r6-generic`) and LLVM (`-mcpu=mips32r6`) are the oracles. MARS cannot run
  R6; it is only a differential oracle for the corpus programs that are valid R6. When MARS and the architecture disagree, the architecture wins;
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
stripped) + manual-spec independence: `scripts/manual_independence.py` (token pre-check) and `scripts/manual_deps.py` →
`scripts/ManualIndependence.lean` (walks the Lean environment from every `Manual.*` constant against an allow-list); 2 `lake build` of all targets, zero project warnings; 3 `lake check` kernel replay, axioms subset of
{propext, Classical.choice, Quot.sound}; 4 `lake comparator` ("Your solution is okay!"); 5 DiffHarness vs real MARS
(needs java; pass count must equal the number of `tests/corpus/*.asm`); 6 EquivHarness (incl. the manual-spec check: `Manual.InstructionTime` vs `step` through `Refine.abs`); 7 oracle (`scripts/oracle.py` selftest + QEMU 24Kf/LLVM differential, behaviour and encodings; FAILs without qemu/llvm, undeclared mismatches fail, declared QEMU deviations and known model bugs are counted); 8 traceability
(`trace.py --check`: every constructor has step arm, spec theorem, `_refines`; `--check-readme`); 9 manuals tool selftest (SKIP if texts absent; any SKIP in a full run makes the gate RED, no stamp); 10 hygiene.
- While iterating: `scripts/gate.sh --quick` (steps 1,8,9,10; NOT green, no stamp). Use `--only STEP`/`--from STEP`.
- Before reporting done / before commit: `scripts/gate.sh --fix` (full; regenerates the README coverage table). Only a full green run
  writes `.gate/green`, bound to the exact tree content.
- Commit ONLY with `scripts/gate-commit.sh "<subject>" [body-file]` (or `--run`). Never `git commit` by hand,
  never `--no-verify`, never `--allow-warnings` unless the owner said so.
- Never push, merge, open PRs, or commit on `main`/`master` unless the owner asks. Commits are local.
- The `/gate` skill wraps this. `lake check` takes ~2-5 min; do not run it in parallel with other lake jobs in one tree.

## File map
- Model (definitions only, tests are elsewhere): `Semantics/Word.lean`, `Types.lean` (`State` incl. `hwInt` = environment-driven HW5..HW0 lines, never written by `step`, `standby` after WAIT, and `nullified` = the next instruction time is a nullified branch-likely delay slot; `Program`, `VAddr`/`PAddr`), `State.lean`
  (accessors, Kernel/User Mode, the Fixed Mapping MMU `translate`, the six memory-access functions on physical `physMem`), `Instruction.lean` (`Instruction`, strict `decode`, `encode`), `FpOps.lean` (FPU on
  bit patterns, no host floats; `FpOpsSpec.lean` = IEEE 754 reference definition written from MD00082 ch.6 (trusted), `FpOpsCorrect*.lean` =
  proofs that `roundCore`, add/sub/mul/div/sqrt (all operands), conversions, compares, ABS/NEG, the FCSR update and
  the MADD family meet it, plus RECIP/RSQRT error bounds), `Step.lean` (`step : State → State` = `timerTick ∘ stepCore`: interrupt if `interruptTaken`, else standby step after WAIT, else `nullifiedStep` for a nullified delay slot, else `execute`; `executesInstr` names the third case; `run`, exception model, CP0 access, `resetException`/`resetState`). `Env.lean`: the environment, NOT the
  architecture (`load` by physical address `loadAddr`, `bootConvention`, `hostedStart`, `HaltReason`, hosted services, `runHosted`). `Asm.lean` assembler (tested, not proved).
  `Semantics.lean`/`Checked.lean` roots

- Spec, one file per family: `Semantics/Specs/<Family>.lean` (`Arith`, `Shift`, `MulDiv`, `BitOps`, `Immediate`, `Memory`, `Atomic`,
  `Unaligned`, `Branch`, `BranchLikely`, `Jump`, `Trap`, `Syscall`, `Cp0`, `Fpu*`), global theorems in `DecodeSpec`, `Exception`,
  `Fetch`, `SelfModifying`, `DelaySlot`, `Invariants`, `RegFileSize`, `Mode` (Kernel/User Mode), `Reset` (reset state, boot convention), `Mmu` (address translation), `Loader` (loader correctness), `Timer` (Count/Compare, timerTick, RDHWR/HWREna), `Interrupt` (interrupt delivery, WAIT standby, IntCtl/SRSCtl), `Hosted` (the environment layer vs `step`). Vocabulary: `Defs.lean`, `WellFormed.lean`. Plumbing: `Lemmas`, `Fixtures`,
  `Tactics` (the `step_spec` / `fp_step_spec` / `cp0_step_spec` proof scripts). Index and reading guide: `Specs/StepSpec.lean` (it holds no theorem).
- Trusted surface: `Semantics/Statements.lean` (216 statements, proofs `sorry`, imported by nothing; it imports `Refine/Defs`, `Manual/*`, `FpOpsSpec`, `Manual/Accuracy`) + `Semantics/StatementsProofs.lean`
  (same statements proved from Specs) + `comparator.json`. `FpOpsFacts.lean`, `FpCompareFacts.lean` kernel-checked FP facts.
- Independent manual spec (Wave 7, design + transcription guide in `docs/MANUAL-SPEC.md`): `Semantics/Manual/` = the manual's
  pseudocode transcribed (`Arch`, `Pseudocode`, `Memory`, `FPU`, `CP0`, `Exceptions`, `Interrupts`, `Timer`, `Reset`, `Encoding`, `Decode` (the spec's OWN
  decoder `Manual.Decode`/`decodeDiagram`, from the format diagrams; the top theorems use it),
  `Ops/*` one def per manual page, `Operation`, `Cycle` (`InstructionTime`), `Choices` (`modelImpl`/`modelOracle` pins)). It may import
  only `Word`, `Types` (W32/VAddr/PAddr), `Instruction` (constructor names), `FpOps` rounding core; enforced by gate step 1.
  `Semantics/Refine/` = proofs that `step` refines it: `Defs.lean` (`abs : State → Manual.Arch`, `Good`, `Inv` — trusted definitions),
  `Abs`/`Bridge*`/`Fetch` plumbing, `<Family>.lean` `<ctor>_refines` (all 183), `Instr.lean` (`allInstrRefines`), `Cycle` (non-instruction
  paths), `Decode` (`decoderSound_decode`), `DecodeDiagram`/`DecodeBridge` (`decode_agrees_manual`, `decode_diagram_complete`,
  `decode_none_manual`: the model's `decode` agrees with `Manual.Decode`), `Invariant` (`step_preserves_inv`), `Step.lean` (TOP: `step_eq_manual`, `run_refines_manual`),
  `Determinism` (`manual_step_deterministic`, `modelOracle_valid`, `interrupt_choice_exists`), `ChoicePoints` (`operation_choiceFree`, `cf_<ctor>`;
  imports `ChoiceFp`), `ChoiceWitness`/`ChoiceRows{,Fp,Fma}`/`ChoiceExact` (`choiceFree_exact`, `choiceFree_iff`: ChoiceFree is exact);
  `Manual/Relation.lean` = `Step`/`Oracle.Valid` (§1.2.1 limits incl. non-interference, §1.2.2 UNDEFINED, QNaN)/`UnpredictableLimits`/
  `ConsultsOracle` (with `CmpAbsorbs`/`MaddAbsorbs`)/exact `ChoiceFree`; `Manual/Choices.lean` = the pins `modelImpl`/`modelOracle`; `Manual/Accuracy.lean` = `Impl.Valid` (WF, RECIP/RSQRT ULP bounds;
  re-transcribes Table 6.2 as `FPValue` because `Manual/` may not import `FpOpsSpec`); `Refine/ImplValid.lean` = `modelImpl_valid`.
- Tests: in-build `#guard`/`example` in `Semantics/Tests/*.lean` (and in Specs); `tests/corpus` (vs MARS), `tests/equiv`, `tests/asm`
  (checked output), `tests/oracle/*.asm` + `encodings.list` (QEMU/LLVM oracle, directives below). Executables: `DiffHarness.lean`,
  `EquivHarness.lean`, `MipsRun.lean` (one .asm -> JSON; `--bare` = no hosted syscall services; `--reset` = start at the reset vector from `resetState`). `vendor/mars/` is the MARS jar only (source not vendored).
- This branch is the semantics: code, tests, gate, `README.md` (short; its coverage table is GENERATED), `manuals/` (lookup tool
  `mipsdoc.py`, `fetch.sh`, see its `AGENTS.md`), `scripts/` gate, oracle, trace (`scripts/README.md`).
- Docs live on the orphan branch `documentation`, mounted as a worktree at `docs/` (gitignored here):
  `git worktree add docs documentation`. Paths such as `docs/spec/SPEC-NOTES.md` in code comments refer to it. It holds
  `OVERVIEW.md` (what is proved/tested/trusted, limits), `DESIGN.md`, `MANUAL-SPEC.md`, `PROOF-NOTES.md` (reading order, comparator
  arrangement), `TRACE.md` (GENERATED), `AUDIT.md`, `spec/{INSTRUCTION-REF,SPEC-NOTES,COMPLIANCE,MIPS-COVERAGE-GAPS}.md`,
  `tools/compliance.py`. `docs/check.sh` checks it against the code (TRACE.md current, compliance check, no code change since
  the commit in `docs/SYNC`); `--fix` regenerates TRACE.md, `--sync` records the code HEAD. Docs commits are made on that
  branch after `docs/check.sh` passes; the code gate does not cover them. When code changes, update the docs in the same wave.
- Trusted surface changes need explicit owner-visible mention: the model files, `comparator.json`, `lakefile.toml`, `Checked.lean`,
  the statements in `Statements.lean`, everything in `Semantics/Manual/` (incl. the `Choices.lean` pins), `Semantics/Refine/Defs.lean`,
  and `Semantics/FpOpsSpec.lean` (the IEEE/FP reference definitions the FP theorems are stated against).
- Per-instruction `_spec_raw` theorems restate what `step` computes (proved by `rfl`-style scripts); they are NOT independent of
  `Step.lean`. Do not describe them as a correctness proof (`docs/OVERVIEW.md`, "What is proved, what is tested, what is trusted"). The independent correctness
  result is `step_eq_manual` (step refines the manual transcription in `Semantics/Manual/`, for every state satisfying `Refine.Inv`).

## Oracle directives (`# oracle: ...` comments in `tests/oracle/*.asm`; full table in `scripts/README.md`)
`expect-deviation <field> <manual citation>` QEMU differs from the manual (manual wins; a stale declaration fails);
`unpredictable <field> <citation>` not compared; `known-model-bug <field> <citation> <desc>`; `expect <field>=<value>`;
`ignore-regs`; `max-steps N`; `bare` (model runs `MipsRun --bare`; needs a `.ktext` handler). Run one: `python3 scripts/oracle.py --only NAME -v`.

## Adding a theorem to the trusted surface
Add the statement (docstring, proof `sorry`) to `Semantics/Statements.lean`; add the same statement, proved by
`_root_.<name> <binders>`, at the same position in `Semantics/StatementsProofs.lean`; add `Trusted.<name>` to `comparator.json`.
Details and pitfalls (matcher naming): `docs/PROOF-NOTES.md`, "The comparator arrangement". Then `scripts/gate.sh --fix`.

## Running things
- Run a program: `lake exe MipsRun prog.asm` (JSON out). `lake exe DiffHarness` (needs java). `lake exe EquivHarness`.
- Build: `lake build Semantics Checked DiffHarness EquivHarness MipsRun`. Check: `lake check`; `lake comparator`.
- Traceability: `python3 scripts/trace.py` (writes docs/TRACE.md, needs the docs mount, and the README coverage block), `--check`, `--readme`, `--check-readme`, `--write-readme`, `--out FILE`.
- Manuals: `python3 manuals/mipsdoc.py insn NAME | section v3 "Cause Register" | search "..." | page v2 177`.
  Texts are not committed; `manuals/fetch.sh` fetches them. See the `mips-manual` skill.

## Concurrency (multi-agent waves)
- One writer per file. State your file ownership at the start; everything else is read-only.
- Parallel writers use separate git worktrees (`git worktree add`, then copy `.lake` in); merge is the orchestrator's job.
- Never run destructive git: no reset --hard, checkout --, clean, stash, rebase, force-push, branch switching in a shared tree.
- Do not run `lake` in a tree another agent is building (lock contention) -- use your own worktree.
- Scratch files go outside the repo (the session scratchpad), never in the tree.
- Re-read a file immediately before editing it; others may have changed it.
- The `/wave` skill is the orchestration checklist.

## Definition of done for an instruction
1. Constructor in `Instruction` (Instruction.lean).  2. `decode` and `encode` clauses plus a round-trip test in `Tests/InstructionTests.lean`
(and `WellFormed`, `DecodeSpec` still hold).  3. `execBody` arm in Step.lean (exceptions via the CP0 model).
4. `<ctor>_spec_raw` in the matching `Semantics/Specs/<Family>.lean`, proved with `step_spec`/`fp_step_spec`, no sorry.
5. Assembler mnemonic in Asm.lean + a `#guard` in `Tests/AsmTests.lean` + a form in `tests/oracle/encodings.list`.
6. INSTRUCTION-REF.md entry citing document+revision+section+printed page; SPEC-NOTES entry for any pin or divergence.
7. A test: `tests/corpus` (MARS supports it) and/or a `tests/oracle` program.  8. `scripts/gate.sh --fix` (regenerates the
README table).  9. Full gate green; then the docs items (6, `docs/check.sh --fix`/`--sync`) on the `documentation` branch. Recipe: the `new-instruction` skill.
