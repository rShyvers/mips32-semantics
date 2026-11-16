# Proof notes

Notes about *how the proofs and their files came to be*, kept out of the Lean sources so that those
read as a specification. Nothing here is needed to trust a theorem: the statements are in
`Semantics/Statements.lean` and `Semantics/Specs/*.lean`, and the kernel checks the proofs.

## What to read, in order

1. The model: `Semantics/Word.lean`, `Types.lean`, `State.lean`, `Instruction.lean`, `FpOps.lean`,
   `Step.lean` (definitions only; their tests are in `Semantics/Tests/`). Then, separately, the environment
   around the processor (not the architecture): `Env.lean`.
2. The statement vocabulary: `Semantics/Specs/Defs.lean`, `Semantics/Specs/WellFormed.lean`.
3. The statements: `Semantics/Statements.lean` (the selected surface, proofs elided), then, for any
   family of interest, `Semantics/Specs/<Family>.lean` (index and table: `Semantics/Specs/StepSpec.lean`).
4. Once: `Semantics/Specs/Tactics.lean` (the two proof scripts).

`Lemmas.lean`, the proof-device parts of `DelaySlot.lean` / `Invariants.lean` / `RegFileSize.lean`,
`DecodeSpec.lean`'s field lemmas, `FpOpsFacts.lean` and `FpCompareFacts.lean`'s arithmetic cores need
not be read: they are plumbing, replayed by `lake check`.

## The comparator arrangement

`lake comparator` (built into this toolchain's Lake; `lake comparator --help`) judges a *solution*
module against a *challenge* module: for each name in `comparator.json` it requires the same
statement in both, no axiom outside `permitted_axioms`, and kernel acceptance of the solution.

* **Challenge:** `Semantics/Statements.lean`. Statements only, every proof is `sorry`. It imports the
  model and `Specs/Defs.lean` (which re-exports `Specs/WellFormed.lean`), and no proof file.
* **Solution:** `Semantics/StatementsProofs.lean`. The same statements, in the same order, each proved
  by the real theorem of the same name (`_root_.add_spec_raw s w rs rt rd hfetch hdecode hpb`).
* Both put the theorems in `namespace Trusted`, so `comparator.json` lists `Trusted.<name>`.

Before this arrangement `comparator.json` named `Semantics.Specs.StepSpec` as both challenge and
solution, so the statement comparison compared a file with itself and only the axiom check had
content (8 theorems).

**Why a bridging solution module, and not the proof files directly.** A statement containing a
`match` refers to an auxiliary "matcher" constant that Lean names after the first theorem *of the
current module* needing that shape of match (`lw_spec_raw.match_1`), and reuses within the module.
In the proof files `lw_spec_raw` (`Memory.lean`) and `ll_spec_raw` (`Atomic.lean`) each get their own
matcher; in a single statements file the second reuses the first's. The two statements are then
definitionally equal but not syntactically identical, and the comparator (which compares terms)
reports `Challenge and solution theorem statement do not match: 'll_spec_raw'` (observed when the
proof index was used as the solution). Restating the surface in one solution module, in the same
order as the challenge, makes both sides name their matchers identically; each restatement is
closed by the real theorem (the kernel unfolds the matchers).

**Why the `sorry` is contained.** `Semantics.Statements` is imported by nothing: not by
`Semantics.lean`, not by `Checked.lean`. It is built only by `lake comparator`. So `lake build` of
the gate's targets has no `sorry` warning and `lake check` replays no `sorry`. The gate's
forbidden-construct scan (step 1) covers every file under `Semantics/`, so `scripts/gate-allow.txt`
allow-lists exactly `Semantics/Statements.lean:sorry`.

**It does detect a changed statement** (run on 2026-11-12 during this restructuring, then
reverted): adding a hypothesis `(_hextra : v ≠ 0#32)` to `Trusted.zero_write_not_observable` in
`StatementsProofs.lean` still builds, and `lake comparator` exits 1 with
`Challenge and solution theorem statement do not match: 'Trusted.zero_write_not_observable'`.
Changing a statement in `StatementsProofs.lean` so that the cited theorem no longer proves it fails
earlier, at the build.

**Adding a theorem to the surface:** add its statement (with docstring, proof `sorry`) to
`Statements.lean`; add the same statement with proof `_root_.<name> <binders…>` at the same position
in `StatementsProofs.lean`; add `Trusted.<name>` to `comparator.json`. If the positions differ, a
`match` may be named differently on the two sides and the comparator will say so.

## The proof scripts (`Semantics/Specs/Tactics.lean`)

176 per-instruction proofs (before wave 5, which added `rdhwr_spec_raw`, also by `step_spec`) were the same two scripts copied: 103 of the form destructure `s`,
substitute `pendingBranch := none`, `unfold step`, rewrite fetch (`hfetch : readMemWord s s.pc = some w`
since the pure-step wave) and decode, `rfl` (now `step_spec`), and 73 FPU ones that additionally discharge the delay-slot / Coprocessor-Unusable
guards with `execInstr_eq_body` (now `fp_step_spec`). `di`/`ei`/`pref` omitted one `dsimp only`;
`step_spec` has `try dsimp only` there, which is the only behavioural difference from the copies.
`fp_step_spec` selects `fpFinishS_eq`/`fpFinishD_eq`/`fpFinishCmp_eq` by rewriting the statement's
right-hand side right-to-left: a plain `first | exact … | exact …` made Lean unfold large FP terms
before failing (deterministic timeouts in `FpuArith`).

Proofs that differ were left as they were (overflow corollaries, taken/not-taken corollaries,
`syscall`, `break`, the structural invariants, …).

## Layout decisions

* **Tests out of the definition files.** `Word`, `Types`, `State`, `Instruction`, `Asm`, `FpOps`,
  `Step` now hold definitions only; their `#guard`/`example` blocks moved verbatim to
  `Semantics/Tests/`. To make that possible two `Asm.lean` helpers lost `private`
  (`natToW32`, `fpCondNames`: the tests name them) and `cop1Mnemonics` (the names of the still
  private `cop1Table`; `scripts/oracle.py` now finds its tables with or without `private`) was added for
  the one test that checks the table has no duplicate names — no existing definition changed.
  `Step.lean`'s `private` test helpers became `namespace StepTest` in `Tests/StepFixtures.lean`.
* **Specs do not import Tests.** The spec files' own example builders (`prog1Spec`, `setRegsSpec`,
  `buildProgSpec`) are in `Specs/Fixtures.lean`; they duplicate three helpers of
  `Tests/StepFixtures.lean` on purpose, so that the proof files depend only on the model.
* **`FpOps.lean` §10/§11.** The kernel-checked facts are now `Semantics/FpOpsFacts.lean`, the
  differential tests against the host's floats `Semantics/Tests/FpOpsTests.lean`.
* **`Instruction.WellFormed`** moved from `DecodeSpec.lean` to `Specs/WellFormed.lean`, because it
  is part of the statement of `decode_encode`.
* The former section numbering of `StepSpec.lean` ("Group 0 … Group 8", "Group N", "Group N+1",
  with "Group 5" used seven times) reflected the order in which sections were written; the family
  files replace it.

## History, by theorem

* **`syscall1_spec`** (`Syscall.lean`; since the pure-step wave `hosted_print_int`, `Hosted.lean`) originally lacked `hpb : s.pendingBranch = none` and was
  false as stated: with `s.pendingBranch = some 0xabcd#32`, `step` yields `pc = 0xabcd#32`. The
  hypothesis was added before the proof was written.
* **`step_preserves_zero_register`** (`Invariants.lean`) was first proved by a per-instruction
  dispatch over the `_spec_raw` theorems, and was incomplete (39 instructions had no case). It is
  now structural (`execInstr_zeroKept`), needs no fetch/decode hypothesis, and covers instructions
  added later automatically. **`step_preserves_zero_register_nontrivial`** is the old
  hypothesis-carrying statement, kept under its name as a one-line corollary.
* **`lb`/`lbu`/`lh`/`lhu_spec_raw`** (`Memory.lean`) were written as the single-instruction
  restatements that old dispatch used; they remain as the specs of those instructions.
* **`lw_misaligned_no_load`** (`Memory.lean`) was `lw_misaligned_no_next` when address errors were
  modeled as halts rather than as the Address Error exception.
* **`clo`/`clz`/`mul`/`seb`/`seh`/`wsbh`/`ext`/`ins`** had an `execInstr` arm and `#guard`s before
  they had `_spec_raw` theorems; the theorems were added afterwards.
* **`lwc1_misaligned_spec`, `swc1_misaligned_spec`** existed at commit 5b21c3d, were lost when the
  FPU was rewritten (94468fb), and were restored in this restructuring together with
  `lwxc1_misaligned_spec`/`swxc1_misaligned_spec` and the lemmas `readMemWord_misaligned` /
  `writeMemWord_misaligned` (`Lemmas.lean`).
* **Compare predicates.** The 94468fb rewrite replaced twenty per-predicate compare specs by
  `cCondS_spec_raw`/`cCondD_spec_raw` ("applies `f32Compare`"). `Semantics/FpCompareFacts.lean` now
  states what the result bit means for all operands (`f32Relation_less_iff`, `f32Compare_lt`, …,
  and `c_lt_s_sets_cc` etc. in `FpuCompare.lean`), in terms of the sign / exponent / fraction
  fields. **Not proved:** that this field order equals the order of the rational values of
  `toExact32`/`toExact64`; that remains covered only by the differential `#guard`s against the
  host's floats (`Tests/FpOpsTests.lean`).
* **`step_preserves_wellFormed` / `run_initialState_wellFormed`** (`RegFileSize.lean`) were added
  because several theorems assume `regs.size = 32` / `fpRegs.size = 32` and nothing showed `step`
  preserves it.
* **Module headers.** `State.lean`, `Instruction.lean`, `Step.lean` used to describe themselves by
  the development wave and worker that wrote them, and named "MD00086 Rev 2.50" as ground truth.
  The normative manuals are the latest revisions (CLAUDE.md); remaining "Rev 2.50" table/page
  citations in comments are historical.
* **`#guard` vs `decide`.** `State.physMem` (and the `Program` a fixture loads into it) are `Std.HashMap`s
  that do not reduce in the kernel, so every check that runs `step` on a concrete program is a `#guard`
  (compiled evaluation), while pure arithmetic side conditions use `by decide`.

## The pure-step wave: what changed in the statement shapes

`step` used to be `step : Program → State → StepResult`, fetching from an immutable `Program` and
returning `.next s'` or `.halt r`. It is now `step : State → State` (fetch from memory, no halting
case); loading, the MARS-style services and the stopping conventions moved to `Semantics/Env.lean`.

* **Pattern (every per-instruction theorem).** The `(p : Program)` binder is gone; the fetch
  hypothesis `hfetch : fetchWord p s.pc = some w` became `hfetch : readMemWord s s.pc = some w` (the
  big-endian word in memory at `pc`; `readMemWord` is `none` exactly for a misaligned `pc`); `step p s`
  became `step s`; a right-hand side `StepResult.next X` became `X`; a hypothesis
  `hstep : step p s = StepResult.next s'` became `hstep : step s = s'`. `step_spec`/`fp_step_spec` absorbed
  this (only the destructuring pattern lost the `out` field). Fixtures place programs in memory with the
  loader's `loadImage` (`stepIn` in `Specs/Fixtures.lean`; `hstep` in `Tests/StepFixtures.lean`).
* **Global invariants are now unconditional.** `step_preserves_zero_register (s) : readReg (step s) 0 =
  readReg s 0` and `step_preserves_wellFormed (s) (hwf) : (step s).RegFilesWF` no longer take a `hstep`
  hypothesis; `run_*` are about `run s n : State` (no `.finalState`).
* **Changed beyond the pattern.** `syscall_spec_raw` is now the plain System Call exception (no `hpb`,
  no dispatch); the old dispatch statement is `hostStep_syscall_spec` (`Specs/Hosted.lean`),
  `syscall1_spec` became `hosted_print_int`, `syscall10_spec` became `hosted_exit`.
  `branch_in_delay_slot_halts` → `branch_in_delay_slot_reserved_instruction` and `eret_in_delay_slot_halts`
  → `eret_in_delay_slot_reserved_instruction` (Reserved Instruction instead of a halt).
  `step_no_instruction` and `step_unhandled_exception` were removed (the processor has no such case; the
  convention is `hostStep_stop` in `Hosted.lean`); `step_fetches_from_memory` took `step_no_instruction`'s
  place on the surface. `exceptionEntry_always` and `wait_preserves_state` lost their `out = out`
  conjunct (the field no longer exists). `rotr_output_ne_srl_output` compared two programs at the same
  `pc`; it now compares `s` and `{ s with mem := m' }`. `mthi_mfhi_round_trip` and
  `beq_taken_delay_slot_lands_on_target` state their second fetch as `readMemWord s (s.pc + 4) = some w2`.
  `beql_not_taken_squashes_delay_slot`'s `run` conjunct is `run s 1 = { s with pc := s.pc + 8 }`.
* **Removed proof devices.** `run_go_preserves_zero_register`, `run_go_preserves_regfile_sizes` (`run` is
  now plain structural recursion), `zeroKept_halt`, `sizesKept_halt` (no halt), `writeReg_proj_out`,
  `writeReg_out` (no `out` field). `ZeroKept`/`SizesKept`/`DelaySlotRel` are now relations between two
  states; because the "next" lemma is definitional it moved out of `zk_simp`/`sk_simp` into fallback
  macros (`zk_simp_next`, `sk_simp_next`), otherwise it fires first and blocks the specific lemmas.
* **Added.** `SelfModifying.lean` (`readMemWord_writeMemWord_same`, `sw_next_instruction_is_fetched`,
  `store_changes_next_instruction`), `Hosted.lean` (`hostStep_eq_step`, `runHosted_agrees_with_run`, the
  service theorems, `runHosted_preserves_zero_register` / `_wellFormed`), `step_fetches_from_memory`.

## Wave 3 (reset state and User Mode): what changed in the statement shapes

`execInstr` gained a third guard: a coprocessor-0 instruction (`usesCop0`: `mfc0`, `mtc0`, `di`, `ei`,
`eret`, `wait`) raises Coprocessor Unusable (`Cause.CE = 0`) when `cp0Usable s = false` (User Mode and
`Status.CU0 = 0`); `step` raises the same for an undecodable COP0/CACHE word (`isCop0Word`).

* **Hypothesis added (the old statements are false in User Mode).** `mfc0_spec_raw`, `mtc0_spec_raw`,
  `di_spec_raw`, `ei_spec_raw`, `eret_spec_raw`, `wait_spec_raw`, `eret_clears_llBit`,
  `wait_preserves_state` take `hcp0 : cp0Usable s = true`. The other case is one general theorem,
  `cp0_instruction_user_mode_unusable` (`Cp0.lean`), rather than six per-instruction duplicates.
  `step_reserved_instruction` takes `hc0 : isCop0Word w = false ∨ cp0Usable s = true`;
  `step_undecodable`'s right-hand side has a new first branch (`isCop0Word w && !cp0Usable s` →
  `exceptionEntry s excCodeCpU 0#32`); the new case is `step_reserved_cop0_unusable`.
  `execInstr_eq_body` (`Lemmas.lean`) takes a third disjunction for the new guard.
* **Proof script.** `cp0_step_spec` (`Tactics.lean`) is `step_spec` for the CP0 instructions: it
  discharges the three guards with `execInstr_eq_body` (`hpb`, `rfl` for "not a COP1 instruction",
  `hcp0`) and closes by `rfl`. `fp_step_spec` discharges the new guard with `rfl`.
* **New files.** `Specs/Mode.lean` (`userMode_iff`, `cp0Usable_false_iff`,
  `exceptionEntry_enters_kernel_mode`, `exception_from_user_mode_enters_kernel_mode`, `eret_to_user_mode`,
  `mtc0_status_enters_user_mode`) and `Specs/Reset.lean` (`resetException_spec`, `resetException_keeps`,
  `resetState_spec`, `bootConvention_spec`, `hostedStart_is_reset_then_boot`, `load_is_reset_then_boot`).
  `hostedStart_is_reset_then_boot` is `⟨rfl, rfl⟩`: the hosted start state did not change, it is now
  *defined* as reset followed by the boot convention.
* **Trusted surface.** 73 → 83 statements: added `step_reserved_cop0_unusable`,
  `cp0_instruction_user_mode_unusable`, `cp0Usable_false_iff`, `userMode_iff`,
  `exception_from_user_mode_enters_kernel_mode`, `exceptionEntry_enters_kernel_mode`, `eret_to_user_mode`,
  `resetException_spec`, `resetState_spec`, `hostedStart_is_reset_then_boot`; changed `step_undecodable`,
  `step_reserved_instruction`, `mfc0_spec_raw`, `mtc0_spec_raw`, `eret_spec_raw` as above.

## Wave 4 (Fixed Mapping MMU): what changed in the statement shapes

`State.mem` became `State.physMem`, **physical** memory; the six `readMem*`/`writeMem*` functions take a
virtual address, check alignment, translate it with `translate` (`State.lean`: the address-error check
`accessAllowed`, then `fixedMappingPA`, MD00090 Vol III Rev 6.02 Appendix A.1) and access `physMem`. They
keep their types (`Option`), and `none` still means Address Error, now also "kernel address from User
Mode". `kernelMode`/`userMode` moved from `Step.lean` to `State.lean` (the MMU needs them); `State` gained
`cp0ConfigK23`/`cp0ConfigKU` (`Config.K23`/`KU`, R/W with the Fixed Mapping MMU), so the destructuring
patterns of `step_spec`/`fp_step_spec`/`cp0_step_spec` and `DelaySlot.lean` grew by two fields.

* **Unchanged in form (meaning changed through the definitions).** Every `<ctor>_spec_raw` whose
  right-hand side already went through `readMemWord`/`readMemHalf`/`writeMemWord`/`writeMemHalf`/
  `readMemByte`/`writeMemByte` with a `none` → Address Error arm (`lw`, `sw`, `lh`, `lhu`, `sh`, `lb`,
  `lbu`, `ll`, `sc`, the FP loads/stores), and every `hfetch : readMemWord s s.pc = some w`.
  `step_misaligned_pc` is unchanged (alignment is checked before translation).
* **Changed (the old statements are false for User Mode + kernel address).** `lwl`/`lwr`/`swl`/`swr`
  used `(readMemByte …).getD 0` / `(writeMemByte …).getD s` everywhere (the byte functions could not
  fail); the step arms now match on the access at `addr` first (`none` → AdEL/AdES), and the four
  `_spec_raw` statements follow (`swr` now writes the byte at `addr` first; the stored bytes are the
  same). `sb_spec_raw` stated the result with `s.mem.insert addr …`; it is now a `match` on
  `translate s addr` (`none` → AdES; `some pa` → `physMem.insert pa …`), proved from the new helper
  `sb_spec_raw_writeMemByte`. `sw_next_instruction_is_fetched` and `store_changes_next_instruction` gained
  `hacc : accessAllowed s (s.pc + 4) = true` (from User Mode, `pc + 4` can be `0x8000_0000` while `pc` is
  in useg; the store is then an Address Error). `readMemWord_isSome_of_aligned` /
  `writeMemWord_isSome_of_aligned` (`Lemmas.lean`) gained the same kind of hypothesis.
  `readCString_mem` takes `Status` equality too (`readCString` reads through `readMemByte`);
  `readCStringOfMem` takes the `Status` word.
* **Config.** `configValue` is `0x8000_8580 ||| K23 << 28 ||| KU << 25 ||| K0` (`MT = 3`); `mfc0_spec_raw`'s
  `(16,0)` arm and `mtc0_spec_raw`'s `(16,0)` arm (which now also stores `K23`/`KU`) changed;
  `resetException_spec`/`resetState_spec` say `Config = 0xA400_8582`.
* **Proof scripts.** `DelaySlot.lean`'s structural proof also unfolds `translate`, `accessAllowed`,
  `kernelMode`, `erlSet`, so that the translation of both runs is the same term.
* **New files.** `Specs/Mmu.lean` (segment-by-segment facts about `fixedMappingPA`, `translate` in each
  mode, the User-Mode Address Error for every access function and at the step level, aliasing),
  `Specs/Loader.lean` (loader correctness: `loadImage_readMemWord`, `load_readMemWord`,
  `load_step_fetches_image`, `loadAtReset_readMemWord_kseg`; the HashMap fold is reduced to a list fold
  with `Std.HashMap.fold_eq_foldl_toList` and `distinct_keys_toList`). `readMemWord_writeMemWord_alias`
  (`SelfModifying.lean`) generalizes `readMemWord_writeMemWord_same` to two virtual addresses with the
  same translation.
* **Trusted surface.** 83 → 98 statements: added `fixedMappingPA_kuseg_erl0`, `fixedMappingPA_kuseg_erl1`,
  `fixedMappingPA_kseg0`, `fixedMappingPA_kseg1`, `fixedMappingPA_kseg23`, `fixedMappingPA_kseg0_kseg1_alias`,
  `translate_user_kernel_address`, `translate_erl1_kuseg_identity`, `step_fetch_user_kernel_address`,
  `lw_user_kernel_address`, `sw_user_kernel_address`, `kseg1_store_visible_through_kseg0`,
  `load_readMemWord`, `load_step_fetches_image`, `loadAtReset_readMemWord_kseg`; changed `sb_spec_raw`,
  `lwl_spec_raw`, `mfc0_spec_raw`, `mtc0_spec_raw`, `resetException_spec`, `resetState_spec`,
  `sw_next_instruction_is_fetched`, `store_changes_next_instruction`, and `exceptionEntry_always` /
  `fpCompletesS_trap` (`mem` → `physMem`, the field rename only).

## Wave 5 (timer and hardware registers): what changed in the statement shapes

`step s = timerTick (execute s)`: `execute` is the old `step` (fetch, decode, execute), `timerTick` advances
`Count` (unless `Cause.DC = 1`) and sets `Cause.TI` when `Count = Compare` (`Step.lean`). `Count` therefore
changes on every step, and **no theorem of the form `step s = X` stays true verbatim**.

* **Pattern (every step equation).** `step s = X` became `step s = timerTick (X)`: the conclusion now also says
  what happens to `Count`/`TI` (a strengthening; no hypothesis was added). This is mechanical: 341 statements
  in `Semantics/Specs`, `Statements.lean` and `StatementsProofs.lean` (55 trusted statements among them), done by
  a script that wraps the right-hand side of the conclusion. `step (load p) = execInstr (load p) instr` and
  `step (step s) = execInstr (step s) instr'` (`load_step_fetches_image`, `store_changes_next_instruction`)
  likewise. The proofs are unchanged: `unfold step` became `unfold step execute` and `rfl` compares
  `timerTick A` with `timerTick B` argument-wise.
* **Unchanged verbatim.** `step_preserves_zero_register`, `run_preserves_zero_register`,
  `step_preserves_wellFormed`, `run_initialState_wellFormed`, `delay_slot_commits_target` (its conclusion
  `{ s' with pc := t }` holds as stated, because `timerTick` does not read `pc` or `pendingBranch`), every
  `exceptionEntry_*`, the MMU/loader/hosted statements (the hosted services do not tick the timer: they replace
  a processor step by an environment action, SPEC-NOTES §9 item 25).
* **Changed beyond the pattern.** `beql_not_taken_squashes_delay_slot`: the `run s 1` conjunct also gained
  `timerTick`. `mfc0_spec_raw`/`mtc0_spec_raw`: new arms `(7,0)` HWREna, `(9,0)` Count, `(11,0)` Compare;
  `mfc0` of `(13,0)` reads `Cause ||| (TI ? TI|IP7 : 0)`. `resetState_spec`: four more conjuncts (`Count`,
  `Compare`, `TI`, `HWREna`). `hostStep_syscall_spec` (not in the surface): the fallback is
  `timerTick (takeException …)`. The two-step corollaries (`beq_taken_delay_slot_lands_on_target`,
  `mthi_mfhi_round_trip`) are proved for the ticked intermediate state; `cCondS_sets_cc`/`cCondD_sets_cc`
  read `fcsr` through `timerTick_fcsr`.
* **New proof devices.** `Lemmas.lean`: `timerTick_<field>` (`@[simp]`, `rfl`) for every field other than
  `Count`/`TI`, `writeReg_proj_cp0Count` etc. `Timer.lean`: `TimerKept` and the `tk_fwd`/`tk_simp` loop, the
  structural proof `execInstr_timerKept` (every constructor, ~25 s), modelled on `execInstr_sizesKept`.
  `DelaySlot.lean`: `delaySlotRel_rdhwr` (the generic loop cannot see that `hwrValue`/`rdhwrAllowed` agree on
  the two runs); `delay_slot_commits_target` needed one more `dsimp only` (the match is now under `timerTick`).
* **Trusted surface.** 98 → 116 statements: added `step_count_advances`, `step_count_stopped`,
  `step_timer_match_sets_ti`, `step_timerInt`, `mtc0_count_spec`, `mtc0_compare_clears_ti`, `causeValue_timer`,
  `rdhwr_spec_raw`, `hwrValue_cpuNum`, `hwrValue_synciStep`, `hwrValue_cc`, `hwrValue_ccRes`,
  `hwrValue_unimplemented`, `rdhwr_reserved_unimplemented`, `rdhwr_reserved_not_enabled`, `rdhwr_allowed`,
  `hwrena_write_masked`, `resetException_timer`; changed: the 55 step equations (pattern above),
  `beql_not_taken_squashes_delay_slot`, `mfc0_spec_raw`, `mtc0_spec_raw`, `resetState_spec`. None weakened.

## Wave 6 (interrupts, standby, IntCtl/SRSCtl, RDPGPR/WRPGPR): what changed in the statement shapes

`step s = timerTick (stepCore s)`, and `stepCore s` is `takeInterrupt s` when `interruptTaken s`, a standby step
when `s.standby`, and `execute s` otherwise (`Step.lean`). An interrupt can now preempt any instruction, so **no
per-instruction equation `step s = timerTick (X)` holds for every `s`**.

* **Pattern (every per-instruction step equation): a WEAKENING.** Each such theorem gained the last hypothesis
  `hexec : executesInstr s = true` (`executesInstr s = !interruptTaken s && !s.standby`). 68 trusted statements and
  the matching theorems in `Semantics/Specs` (about 270), added by a script that inserts the binder before the
  top-level colon of every theorem with a fetch hypothesis whose statement mentions `step s`, plus a second script
  appending `hexec` to the call sites. A predicate rather than its unfolding keeps it one hypothesis;
  `executesInstr_iff` (`Specs/Interrupt.lean`) unfolds it, and `executesInstr_load` shows it holds at the start of a
  loaded program (`Status.IE = 0`). Two-step statements (`store_changes_next_instruction`, trusted;
  `mthi_mfhi_round_trip`, `beq_taken_delay_slot_lands_on_target`, not trusted) also assume it of the intermediate
  state (`hexec2 : executesInstr (step s) = true`): the timer tick of the first step can raise a request.
  `hosted_print_int`, `hosted_exit`, `hostStep_syscall_spec`: `hexec : executesInstr h.machine = true`, because the
  hosted run performs a service only when the processor would execute the `syscall` (`Env.hostStep`).
* **Proofs.** `step_of_executesInstr : executesInstr s = true → step s = timerTick (execute s)` (`Lemmas.lean`); the
  tactics `step_spec`, `fp_step_spec`, `cp0_step_spec` rewrite with it instead of `unfold step`, so the 180-odd `rfl`
  proofs are unchanged. The global theorems (`step_preserves_zero_register`, `step_preserves_regfile_sizes`,
  `step_count_advances`, `step_count_stopped`, `step_timer_match_sets_ti`, `step_timerInt`) keep their statements and
  got two more cases (interrupt entry, standby); `TimerKept` gained a fifth conjunct `r.hwInt = s.hwInt`, which gives
  `step_hwInt` over every constructor almost for free (`execInstr_hwInt`; the `mtc0` arms that `execInstr_timerKept`
  excludes are closed by computation).
* **Changed beyond the pattern.** `mfc0_spec_raw`/`mtc0_spec_raw`: new arms `(12,1)` IntCtl, `(12,2)` SRSCtl, and
  `Cause` reads `Cause ||| (hwInt <<< 10) ||| (TI ? TI|IP7 : 0)`. `causeValue_timer`: the right-hand side gained
  `hwIntBits s` (the hardware lines; a strengthening, not a weakening: with `hwInt = 0` it is the old statement).
  `wait_spec_raw` (now trusted): `{ s with standby := true, pc := s.pc + 4 }` (was `{ s with pc := s.pc + 4 }`).
* **Trusted surface.** 116 → 139 statements: added `step_interrupt`, `interruptTaken_iff`, `no_interrupt_ie0`,
  `no_interrupt_exl`, `no_interrupt_erl`, `no_interrupt_masked`, `takeInterrupt_not_in_delay_slot`,
  `takeInterrupt_in_delay_slot`, `interruptVector_iv0`, `interruptVector_iv1_bev0`, `interruptVector_iv1_bev1`,
  `mtc0_cause_requests_software_interrupt`, `timer_requests_interrupt`, `step_hwInt`, `wait_spec_raw`,
  `step_standby_stays`, `step_standby_restarts`, `step_standby_interrupt`, `intCtlValue_fields`,
  `srsCtlValue_fields`, `mfc0_srsctl_spec`, `rdpgpr_spec_raw`, `wrpgpr_spec_raw`. Weakened (hypothesis added): the 68
  listed in SPEC-NOTES §9 item 29 (every per-instruction statement, the fetch/delay-slot/MMU/self-modifying step
  statements and the two hosted-service statements). Changed in form: `causeValue_timer`, `mfc0_spec_raw`,
  `mtc0_spec_raw`. None removed.

## Housekeeping wave: trusted surface 139 → 142

Added (no existing statement changed or removed): `canonicalVAddr_loadAddr` (left inverse outside kseg1),
`canonicalVAddr_loadAddr_kseg1` (a kseg1 address comes back as its kseg0 alias) and `loadAddr_canonicalVAddr`
(right inverse on the range of `loadAddr`, which misses physical 0x2000_0000–0x3FFF_FFFF). They justify the virtual
`memory` view in the `MipsRun` JSON render. Proofs in `Semantics/Specs/Loader.lean`.

## Wave 7A (branch-likely nullification, manual spec infrastructure): trusted surface 142 → 143

* **Model change (Task 0).** `State` gained `nullified : Bool` (the instruction at `pc` is the nullified delay
  slot of a not-taken branch-likely); `stepCore` consumes it in its own step (`nullifiedStep`), `executesInstr`
  requires `nullified = false`, `exceptionEntry`, `resetException` and `bootConvention` clear it. Every
  `obtain ⟨…⟩ := s` pattern gained the 26th field.
* **Changed (trusted, statement restated to the manual's behaviour, not weakened):** `beql_spec_raw` (not taken:
  `{ s with pc := s.pc + 4, pendingBranch := some (s.pc + 8), nullified := true }`, was `{ s with pc := s.pc + 8 }`);
  `beql_not_taken_squashes_delay_slot` (first conjunct as `beql_spec_raw`; second conjunct now
  `interruptTaken (step s) = false → run s 2 = timerTick (timerTick { s with pc := s.pc + 8 })`, was
  `run s 1 = timerTick { s with pc := s.pc + 8 }`: the nullified slot takes its own instruction time, and an
  interrupt may be taken at it, hence the hypothesis on the second step).
* **Changed (not trusted):** `bnel_spec_raw` … `bgezall_spec_raw`, `bc1fl_spec_raw`, `bc1tl_spec_raw` (same
  not-taken shape), `executesInstr_iff` (gained `s.nullified = false`), the proofs of `step_of_executesInstr`,
  `step_preserves_zero_register`, `step_preserves_regfile_sizes`, `stepCore_timerKept`, `step_hwInt` (one more
  case each).
* **Added:** `step_nullified` (trusted) and the lemmas `writeReg_proj_nullified`, `timerTick_nullified`.
* **Manual spec (7A).** `Semantics/Manual/*` (definitions, a new trusted surface for the later top theorems) and
  `Semantics/Refine/*` (proofs: `abs`, bridges, and `add_refines`, `lw_refines`, `sw_refines`, `lwl_refines`,
  `beq_refines`, `beql_refines`, `addS_refines`, `mtc0_refines`). No top theorem yet (7D). See
  `docs/MANUAL-SPEC.md`.

## Wave 7R (review fixes): trusted surface unchanged in size (143)

* **Trusted statements (`Statements.lean` / `StatementsProofs.lean` / `comparator.json`): none changed.**
  `sll_spec_raw` and `ext_spec_raw` keep their statements although `step` changed (shift by `shamt mod 32`;
  `ext` reads the diagram's 5-bit fields and raises Reserved Instruction for `lsb + msbd > 31`): their `decode`
  hypothesis gives `shamt < 32` and `pos < 32`, `1 ≤ size`, `pos + size ≤ 32` (`decode_wellFormed`), and the
  proofs now go through that (`ext_spec_raw` via the new `ext_spec_fields`). `jalr_spec_raw` is unchanged
  (the hazard-barrier forms are new constructors).
* **Restated (FP facts, `FpOpsFacts.lean`, kernel-checked; the model changed to the manual's reading A′ of
  ABS/NEG of a QNaN):** `f32Abs_of_nan`, `f64Abs_of_nan` (a QNaN gives the operand with the sign bit cleared /
  flipped, was the operand unchanged), `absNeg_cases` (two QNaN cases), `f32_madd_cases` (the NMADD-of-a-QNaN
  case: `0xFF800001`, was `0x7F800001`, and the NMADD operand order).
* **Restated (not trusted):** `maddS_spec_raw` … `nmsubD_spec_raw` (`Specs/FpuArith.lean`): `fpThen` chains of
  the separate operations, was `fpCompletesS/D` of `f32Madd` …; `ins_spec_raw` keeps its statement (proved via
  the new `ins_spec_fields`); `sll/srl/sra/rotr_spec_raw` keep theirs.
* **Added:** `jrHb_spec_raw`, `jalrHb_spec_raw` (`Specs/Jump.lean`), `ext_spec_fields`, `ins_spec_fields`
  (`Specs/BitOps.lean`), `zeroKept_fpThen`, `sizesKept_fpThen`, `Manual.modelImpl_WF`,
  `Refine.loadMemory_model`.
* **Proof plumbing:** the `execInstr` loops of `Invariants`, `RegFileSize`, `Timer` handle `fpThen`; the
  Refine pilots pass `modelImpl` to `GeneralExceptionProcessing` (which now takes the `Impl`) and use
  `loadMemory_model` (LoadMemory consults `Oracle.loadClearsLL`); `mtc0_refines` simplifies the EBase
  UNDEFINED branch (`Oracle.ebaseWriteBEV0 = .proceed`).

## Wave 7C merge (integer ALU and control/system refinements): trusted surface unchanged in size (143)

* **Model change (trusted surface, `Step.lean`).** `.j`/`.jal` use the low 26 bits of `target`
  (`target &&& 0x3FFFFFF#32`): the J format's `instr_index` is 26 bits ("I+1: PC ← PC_{GPRLEN-1..28} ||
  instr_index || 0^2", MD00086 Vol II-A Rev 6.06, J p.194, JAL p.195). No decoded instruction changes
  (`decode` produces `target < 2^26`); a hand-built constructor did. `j_spec_raw`/`jal_spec_raw` keep their
  statements (proved through `target_mask_of_lt` and `decode_wellFormed`); `#guard`s in
  `Tests/ManualTests.lean`.
* **Refinements.** `Refine.<ctor>_refines` for 83 of the 183 constructors: the integer ALU (7C S1), the
  branches, jumps, CP0 and system instructions (7C S3), and the deferred `ext`, `ins`, `eret`, `jr`, `jalr`,
  `jrHb`, `jalrHb` (merge). `sll`/`srl`/`sra_refines` no longer assume `shamt.toNat < 32` (the model shifts by
  `shamt mod 32` since 7R). `ext`/`ins` hold for every constructor value (both sides read the 5-bit fields
  and raise Reserved Instruction in the UNPREDICTABLE ranges). `jalr`/`jalrHb` include `rs = rd`
  (`modelOracle.jalrRsIsRd = .proceed`; both sides read `temp` before writing `rd`).
* **Repairs for 7R:** `GeneralExceptionProcessing` takes `modelImpl`; `rdpgpr`/`wrpgpr` unfold `Ops.SGPR`/
  `Ops.setSGPR` (set 0 is the GPRs) instead of evaluating `SRSCtlPSS`.

## Wave 7D part 1 (cycle refinement, conditional top theorems): trusted surface unchanged in size (143)

* **Model change (trusted surface, `Step.lean`).** `sc` compares its address with `llAddr` in bits 31..2
  (`s.llAddr >>> 2 == addr >>> 2`), as the manual says: "An SC will fail if the aligned address of the SC does
  not match that of the preceding LL" (MD00086 Vol II-A Rev 6.06, SC, p.347). Before, the whole addresses were
  compared. `ll` records only aligned addresses, so reachable behaviour is unchanged. **Restated (trusted):**
  `sc_spec_raw` (`Specs/Atomic.lean`, `Statements.lean`, `StatementsProofs.lean`: the condition is now
  `s.llBit && s.llAddr >>> 2 == addr >>> 2`). Regression `#guard` in `Specs/Atomic.lean`.
* **Added (not trusted):** `Manual/Relation.lean` (spec: `UnpredictableLimits`, `Oracle.Valid`, `Step`,
  `InstructionTimes`, `ChoiceFree`), `Refine/{Cycle,Decode,Invariant,Instr,Step,Determinism}.lean`; see
  `docs/MANUAL-SPEC.md` I.5. The top theorems are stated from `PendingRefines` (the per-instruction refinements
  of the 100 constructors not yet covered); the unconditional versions and their `Statements.lean` entries come
  when the memory and FPU groups merge.

## Wave 7D part 2 (all refinements, unconditional top theorems): trusted surface 143 → 156

* **Merged** (from the 7C worktrees, based on 7R): S4a FPU arithmetic/convert/compare (`Refine/{BridgeFpu,FpuArith,
  FpuConvert,FpuCompare}.lean`), S2 memory/atomic/unaligned/trap/syscall (`Refine/{BridgeMem,Memory,Atomic,Unaligned,
  Trap,Syscall}.lean`), S4b FPU memory/move/control/branch (`Refine/{BridgeFpuMove,FpuMemory,FpuMove,FpuControl,
  FpuBranch}.lean`). Every constructor now has `Refine.<ctor>_refines`.
* **Model change (trusted surface, `Step.lean`, from S4b).** `ctc1` to a control register that does not exist writes
  nothing but still runs `CheckFPException()`: in the CTC1 Operation the final `else … UNPREDICTABLE endif` is followed
  by `CheckFPException()` (MD00086 Vol II-A Rev 6.06, CTC1, p.150), so an FCSR already holding an enabled Cause bit (or
  `Cause.E`) traps. Before, the arm was a no-op. **Restated (trusted):** `ctc1_spec_raw` (`Specs/FpuControl.lean`,
  `Statements.lean`, `StatementsProofs.lean`): the `none` arm is now `if fcsrTrapPending s.fcsr then takeException s
  excCodeFPE else { s with pc := s.pc + 4 }`. SPEC-NOTES §9 item 13 updated; regression `#guard`s in
  `Tests/ManualTests.lean`.
* **Spec fixes (`Semantics/Manual/Ops`).** `C.cond.fmt` (S4a, `Ops/FpuCompare.lean`), `MOVF`/`MOVT`/`MOVF.fmt`/`MOVT.fmt`
  (S4b, `Ops/FpuMove.lean`) and `BC1F`/`BC1T`/`BC1FL`/`BC1TL` (S4b, `Ops/FpuBranch.lean`) read the condition code with the
  3-bit `cc` field (`low cc 3`): "cc: The Condition code number in the range 0..7" (MD00086 Vol II-A Rev 6.06, Figure
  2.25, p.23; C.cond.fmt diagram, p.110). Before, the whole constructor operand was used.
* **Hypothesis dropped:** `sc_refines` (S2) had `hll : s.llAddr.toNat % 4 = 0` because the model compared whole
  addresses; since 7D part 1 the model compares bits 31..2, and the lemma `aligned_word_eq` now states
  `(bits x 31 2 == bits y 31 2) = (y >>> 2 == x >>> 2)` for all words. `sc_refines` holds for every state.
* **Duplicates resolved (no statement lost).** `BridgeMem` now imports `BridgeIntAlu`/`BridgeControl` and no longer
  restates `execInstr_body` and `writeReg_pc` (identical statements there); its `complete_writeReg` (without `some`) is
  renamed `complete_writeReg_eq` (`BridgeControl.complete_writeReg` keeps its name). `BridgeFpuMove` imports `BridgeFpu`
  and no longer restates `writeFpReg_size`, `readFpD_abs`, `valueFPR64_model`, `storeFPR64_model` (identical statements)
  and `abs_writeFpD` (same statement, binders in another order; the one use was adapted). Its definition
  `FcsrReservedZero` (`s.fcsr.extractLsb' 18 5 = 0#5`) is replaced by the invariant's (`Refine/Defs.lean`) and the lemma
  `fcsrReservedZero_extract`, so `cfc1_refines` takes the invariant's `FcsrReservedZero`.
* **`Refine/Defs.lean` (new, definitions only):** `memOf`, `abs`, `Good` (moved from `Abs.lean`), `FcsrReservedZero`,
  `StatusImplemented` (moved from `Invariant.lean`), `Inv` (moved from `Instr.lean`). The challenge module imports it.
* **`Refine/Instr.lean`:** `instrRefines_<ctor>` for all 183 constructors (generated, constructor order) and
  `allInstrRefines : ∀ i, InstrRefines i`. Removed with the hypothesis they existed for: `Covered`,
  `instrRefines_covered`, `PendingRefines`, `allInstrRefines_of`, and `step_eq_manual_of` (`Refine/Step.lean`; its body
  is now `step_eq_manual`'s). `execute_abs` and `stepCore_abs` lost their `hI` hypothesis.
* **Unconditional:** `step_eq_manual`, `step_refines_manual`, `run_refines_manual`, `step_unique_of_choiceFree` lost
  `hP : PendingRefines`.
* **Trusted surface: 143 → 156 statements.** Added (last section of `Statements.lean`): `step_eq_manual`,
  `step_refines_manual`, `run_refines_manual`, `step_unique_of_choiceFree`, `modelOracle_valid`,
  `manual_step_deterministic`, `decoderSound_decode`, `resetException_refines_manual`, `resetState_refines_manual`,
  `step_preserves_inv`, `inv_resetState`, `inv_hostedStart`, `inv_load`. Changed: `ctc1_spec_raw` (above). None removed.
  `Statements.lean` now also imports `Semantics.Refine.Defs` (and through it `Semantics.Manual.*`); the comparator
  therefore takes the `Manual` definitions, `modelImpl`/`modelOracle`, `Refine.abs` and `Refine.Inv` as given
  (`docs/MANUAL-SPEC.md` I.5, "What the comparator trusts").

## Wave 8 (final tightening): trusted surface 156 → 158

* **`Manual.ChoiceFree` exact** (`Manual/Relation.lean`, spec). `OracleFreeOp` is replaced by `ConsultsOracle ins a`,
  which says per Operation whether it reaches an oracle choice whose value can change the result; an UNPREDICTABLE
  encoding whose coprocessor-usability check fires first is choice-free. Proof: `Refine/ChoicePoints.lean` (new):
  `operation_choiceFree` for all 183 constructors (113 by `rfl`; 70 by `cf_<ctor>`, a meta tactic `case_ite` that
  splits on the closed `if`s of the goal, and oracle-free rewrites of `LoadMemory`/`StoreMemory` while `LLbit = 0`,
  `ValueFPR64`/`StoreFPR64` on even registers, `signOp`/`cvt` away from a quiet NaN; `env_fpResult`: `FPResult`
  leaves RM/Enables/FS alone). `Refine/Determinism.lean` uses it in `execute_oracleFree`; `operation_oracleFree`
  (the `OracleFreeOp` lemma) is removed with `OracleFreeOp`.
* **The other direction** (not complete): `gep_causeCE_choice` (every exception other than Coprocessor Unusable),
  `interrupt_not_choiceFree`, `interrupt_choice_exists` (trusted). For `ConsultsOracle` it is argued, not proved.
* **`Manual.Oracle.Valid` restated** (spec): the three restrictions of MD00086 Vol II-A Rev 6.06 §1.2.1 (p.3-4) —
  non-interference (`NIValue`, `NIOutcome` over `AccessibleSame`/`SameMode`) added; restriction 2 is now
  `InaccessibleSame` (CP0 free when `CU0 = 1`; was: CP0 unchanged in every User Mode state); the UNDEFINED fields
  `cp0Undefined`, `ebaseWriteBEV0` are held to §1.2.2 (p.4: no hang) instead of the UNPREDICTABLE limits (a
  weakening, to match the manual); `QNaNValid` added (MD00082 Vol I-A Rev 6.01 §6.3.1.5, p.82). `KernelState` removed.
  `modelOracle_valid` re-proved (`qnan32_to64`, `qnan64_to32` for the model's `CVT` QNaN choices).
* **`Manual.Impl.Valid`** (spec, `Manual/Choices.lean`): `Impl.WF ∧ Impl.RecipAccurate` (RECIP.fmt p.336, 1 ULP of the
  IEEE core's correctly rounded `1.0 / fs`); `modelImpl_valid` (trusted).
* **Trusted surface: 156 → 158.** Added: `interrupt_choice_exists`, `modelImpl_valid`. Docstrings updated:
  `step_unique_of_choiceFree`, `modelOracle_valid` (statement text unchanged; meaning changed with the definitions).
  None removed.

## Wave 9 (last proof gaps): trusted surface 158 → 159

* **`choiceFree_exact` (trusted; `Refine/ChoiceExact.lean`).** `ChoiceFree modelImpl dec a = false` ⇒ two valid
  oracles give different instruction times, for every state and decoder. With `manual_step_deterministic`:
  `Refine.choiceFree_iff` (not trusted). Stated for `modelImpl` only (an arbitrary `Impl` could hide an odd-register
  read behind a constant `recipD`/`rsqrtD`).
* **Witnesses** (`Refine/ChoiceWitness.lean`): the family `wo p ce` (operations → Reserved Instruction, values
  constant, `Cause.CE = ce`), `wo_valid`. The two `ce` differ from each other and from `Cause.CE` of the state
  (`ceA`, `ceB`), so no lemma "Operations do not read `causeCE`" is needed. Each `ConsultsOracle` row
  (`rw_<ctor>`, 68 constructors, `Refine/ChoiceRows{,Fp,Fma}.lean`) proves `RunP` for two witnesses by unfolding
  the Operation and splitting its `if`s (`runp`, `runp_fp`; `runp_fe` keeps `FPResult` as one `if` on `trapC`).
  FP facts in `Refine/ChoiceFp.lean` (NaN branch of the core, `Dist`, FCSR algebra).
* **Spec change (`Manual/Relation.lean`, `ConsultsOracle`), three rows made exact:** `MFHC1` (`&& reg rt != 0`),
  `C.cond.D` (`CmpAbsorbs`), `MADD.D`/`MSUB.D` (`MaddAbsorbs`). Soundness re-proved: `cf_mfhc1`, `cf_cCondD`,
  `cf_maddD`, `cf_msubD` (`Refine/ChoicePoints.lean`, which now imports `Refine/ChoiceFp.lean`). Details and citations:
  `docs/MANUAL-SPEC.md` I.7.
* **Not done:** `RSQRT.fmt`'s 2-ULP bound and `RECIP.fmt` against the exact result (no error bound for the core's
  rounding exists to build on). `Impl.Valid` unchanged.
* **Test:** `tests/oracle/irq_wait_timer.asm` made robust to host scheduling (MANUAL-SPEC I.7); expectations
  unchanged.
* **Trusted surface 158 → 159:** added `choiceFree_exact` (Statements, StatementsProofs, `comparator.json`).
  `Semantics.lean` and `Checked.lean` import `Semantics.Refine.ChoiceExact`.

## Wave 10 (the IEEE rounding core proved): trusted surface 159 → 175

* **Reference definition (`Semantics/FpOpsSpec.lean`, definitions only, read for trust).** `Format.value` (Table 6.2,
  MD00082 Vol I-A Rev 6.01 p.80-81), `Grid p P` and the sets `Format.Unbounded` (precision `p`, exponent `≥ E_min -
  (p-1)`, unbounded above), `UnboundedRange` (unbounded both ways, for tininess) and their "even" subsets, `Cut` (an
  exact result by its comparisons with the rationals: `Cut.ofRat`, `Cut.sqrt`, `Cut.rsqrt`), `RoundDown`/`RoundUp`/
  `RoundNearestEven`, `CorrectlyRounded` (Table 6.10, p.95), `Format.overflowResult` (Table 6.14, p.100),
  `Format.RoundSpec`. "Even" = representable with one bit less of precision and one more of least exponent. Nearest
  uses midpoints; `nearest_ofRat_iff` proves it equals the `|r - v| ≤ |y - v|` reading for a rational `v`.
* **Proof structure (`Semantics/FpOpsCorrect*.lean`, 17 files, each < 5 s).** `Nat`: `bitLen`, `roundShift_spec`
  (integer rounding of `N / 2^k` per direction), `isqrt_spec`. `Grid`: on a uniform grid of unit `2h` above a grid
  point `L ≤ v` (`GridHyp`), the integer rounding `j` gives the correctly rounded `2jh` (`grid_correct`), unique
  (`grid_unique`); negation symmetry (`correctlyRounded_neg`). `Value`/`Shape`/`Pack`: `value_eq_toExact`,
  `value_pack`, the grid shape of the sets at every exponent (`gridHyp_of`). `Scale`/`Core`/`Main`: the core's
  `N`, `k`, `j` (`scaled_facts`, `cutRound_ofRat`), any cut that agrees with the exact value on the grids
  (`CutAgree`), tininess (`tiny_iff`), assembly (`assemble`), `roundCore_correct`. `Exact`/`DivSqrt`: `Exact.add`
  and `Exact.mul` are exact; the sticky-bit lemma `cutAgree_sticky`; `Exact.div_agree`, `Exact.sqrt_agree`. `Ops`/
  `Api`: the operations, the binary32/64 statements, flush to zero, `roundSpec_representable`. `Acc`/`Recip`/
  `RsqrtAux`/`Rsqrt`: bounds of a correctly rounded value in its binade (`binade_bounds`), `recip_error`,
  `rsqrt_core` (the arithmetic of `SQRT` then `DIV`: in each mode the two roundings' errors combine to at most
  `2^(-a-p+1)`, which is at most 2 ULP of `1/√y`), `rsqrt_error`. No Mathlib: core `Rat`, `grind`, `omega`.
* **Spec change (`Semantics/Manual/`):** new `Manual/Accuracy.lean` (`FPValue`, `FPMax`, `ULP`, `WithinULPs`,
  `WithinULPsRsqrt`, `Impl.RecipExact`, `Impl.RsqrtAccurate`); `Impl.Valid` moved there from `Manual/Choices.lean`
  and strengthened to `WF ∧ RecipAccurate ∧ RecipExact ∧ RsqrtAccurate`. `Manual.modelImpl_valid` moved to
  `Semantics/Refine/ImplValid.lean` (it needs the proofs, which `Semantics/Manual/` may not import). Statement text of
  `Trusted.modelImpl_valid` unchanged; its meaning is stronger. The exact-result bounds assume FCSR.FS = 0 and, for
  `RECIP`, `|1/fs| ≤` the largest finite number (MANUAL-SPEC I.8).
* **Trusted surface 159 → 175** (Statements, StatementsProofs, `comparator.json`): `value_eq_toExact`,
  `roundCore_correct_binary32`, `roundCore_correct_binary64`, `roundSpec_representable`, `roundCore_flush_tiny`,
  `roundCore_flush_normal`, `f32Add_correct`, `f32Sub_correct`, `f32Mul_correct`, `f32Div_correct`,
  `f32Sqrt_correct`, `f64Add_correct`, `f64Sub_correct`, `f64Mul_correct`, `f64Div_correct`, `f64Sqrt_correct`.
  `Statements.lean` now also imports `Semantics.FpOpsSpec` and `Semantics.Manual.Accuracy`. None removed; no
  statement text changed.
* **No model change.** No proof found the core incorrectly rounded; `FpOps.lean` is unchanged.


## Wave 11 (the last FP trust: every operand, conversions, compares, FCSR): trusted surface 175 → 211

* **Reference definitions (`Semantics/FpOpsSpec.lean`, new section, definitions only, read for trust).** Written from
  MD00082 Vol I-A Rev 6.01 ch.6 with `FIR.Has2008 = 0` and the MD00086 Vol II-A Rev 6.06 pages, not from
  `FpOps.lean`: `Format.signOf/expOf/fracOf`, `IsNaN`/`IsSNaN`/`IsQNaN` (Table 6.2, p.80: `b1 = 1` is signaling),
  `infBits`, `zeroBits`, `newQNaN` (Table 6.3, p.82), `Datum`/`Format.datum` (what an encoding denotes),
  `Signaled` (§6.7.2.3/5/6), `TinyBefore` and `RoundEnvSpec` (rounding under RM/Enables/FS, flush §6.7.2.4),
  `NaNResult` (§6.3.1.4-5, §6.7.2.1; any operand QNaN allowed), `invalidResult`, `AddSpec` (`isSub`), `MulSpec`,
  `DivSpec`, `SqrtSpec`, `signChanged`/`SignOpSpec` (ABS p.32 / NEG p.307, reading A′), `ConvertSpec`,
  `ExactSpec`, `WidenSpec`, `FromIntSpec`, `IsInt`/`IsEvenInt`/`ToWordSpec` (CVT.W p.160, ROUND.W p.342, TRUNC.W
  p.441, CEIL.W p.128, FLOOR.W p.186), `Relation`/`cmpRel`, `condTable` (the 16 rows of Tables 3.1/3.2, p.111-112),
  `condHolds`, `CompareSpec` (p.110-113), `flagBit`, `FcsrSpec` (§6.7.1 p.99, CheckFPException p.23), `FpOutcome`,
  `OpStep`, `OpThen`, `MaddSpec` (MADD p.256, MSUB p.287, NMADD p.308, NMSUB p.310). Each is a `match` on the
  operands' `datum`, so the cases are exhaustive by construction. New pin: SPEC-NOTES §9 item 30 (signs of exact zero
  results, where the manuals are silent: IEEE 754-1985 §6.3, named by MD00082 p.77; verified against IEEE Std 754-2019 §6.3 p.50 and §5.4.1 p.33 (the owner's local-only copy, `manuals/LOCAL-SOURCES.md`, `mipsdoc.py section ieee 6.3`; table in SPEC-NOTES §9 item 30) and earlier against the public P754 Draft 1.2.5 §8.3 p.44).
* **Proof structure (9 new files, each < 10 s by `lake env lean`; no Mathlib).** `Special` (classes ↔ the model's
  Boolean tests, `classify`, the NaN rule `nanResult_spec`, `nanResult_first`, ranges), `Env` (`signaled_flags`,
  `roundEnv_spec` for any cut the core agrees with on the grids, so it covers the sticky `DIV`/`SQRT` too; the
  flush test as tininess of the cut), `Arith` (`add_spec` … `sqrt_spec` on all operands, `Exact.add_zero` for the
  sign of an exact zero sum, `negBits_fields`), `Word` (`roundToInt_cr`: correct rounding to the integers via
  `grid_correct` on the half-unit grid; `isIntegral_iff`; `toW32_spec`), `Conv` (`convertNaN_qnan`,
  `convert_spec`, `roundSpec_exact`, `convert_exact`, `ofInt_spec`), `Compare` (`magN` strictly increasing: the
  sign-magnitude keys order the values; `relation_spec`; `compare_spec`), `Fcsr` (`fpUpdate_bit` for all 32 bits,
  `fpUpdate_spec`, `fcsrSpec_unique`), `IEEE` (the `BitVec` statements; `CVT.D.W` exactness `ofInt64_exact`;
  `ABS`/`NEG` via `and_top`/`xor_top`), `Step` (`two_steps*`/`three_steps*`: a chain of `fpThen` is a chain of
  `OpStep`; the eight `*_separate` theorems from the `*_spec_raw` of `Specs/FpuArith.lean`).
* **Trusted surface 175 → 211** (Statements, StatementsProofs, `comparator.json`): `newQNaN_binary32`,
  `newQNaN_binary64`, `nanResult_first`, `f32Add_spec`, `f32Sub_spec`, `f32Mul_spec`, `f32Div_spec`,
  `f32Sqrt_spec`, `f64Add_spec`, `f64Sub_spec`, `f64Mul_spec`, `f64Div_spec`, `f64Sqrt_spec`, `f64ToF32_spec`,
  `f32ToF64_spec`, `w32ToF32_spec`, `w32ToF64_spec`, `f32ToW32_spec`, `f64ToW32_spec`, `condTable_formula`,
  `f32Compare_spec`, `f64Compare_spec`, `f32Abs_spec`, `f32Neg_spec`, `f64Abs_spec`, `f64Neg_spec`,
  `fpUpdate_spec`, `fcsrSpec_unique`, `maddS_separate`, `msubS_separate`, `nmaddS_separate`, `nmsubS_separate`,
  `maddD_separate`, `msubD_separate`, `nmaddD_separate`, `nmsubD_separate`. None removed; no existing statement
  text changed. The statements have no restricting hypotheses: every operand bit pattern, every FCSR environment
  (the `*_separate` theorems carry the usual fetch/decode/`executesInstr` hypotheses of a `*_spec_raw`).
* **No model change.** No proof found a model bug; `FpOps.lean` and `Step.lean` are unchanged.


## Wave 12a (deep-audit fixes B1/B2, C-2, D4, D5): trusted surface unchanged in size

* **D4, spec strengthened (`Manual/Relation.lean`):** `UnpredictableLimits` and `UndefinedOutcomeValid` now
  also require `a'.HW = a.HW` (the hardware interrupt inputs). A model-side strengthening (no sentence of MD00086
  Vol II-A Rev 6.06 §1.2 states it; the inputs are not state an instruction writes: MD00090 Vol III Rev 6.02
  Table 6.2, p.73; `IP7..IP2` read-only, Table 9.52, p.211); SPEC-NOTES §11. `modelOracle_valid` re-proved
  (`Refine/Determinism.lean`); `wo_valid` unchanged (its outcomes are exceptions).
* **D5, spec strengthened (`Manual/Accuracy.lean`):** new `RecipFlagsOK` and `Impl.RecipFlags` (the Invalid
  Operation / Division-by-Zero conditions of `RECIP.fmt`/`RSQRT.fmt` by operand class; Overflow, Underflow,
  Inexact left free); `Impl.Valid` is now `WF ∧ RecipAccurate ∧ RecipExact ∧ RsqrtAccurate ∧ RecipFlags`.
  `Refine/ImplValid.lean`: `div_one_flags`, `recip_flagsOK`, `roundCore_noflush`, `sqrt_not_tiny` (a square root
  is never below the normal range when `fracBits + 2 ≤ bias`, so FS = 1 does not flush it), `toExact_facts`,
  `sqrt_flush`, `sqrt_pos_class`, `rsqrt_flagsOK`, `modelImpl_recipFlags`; `modelImpl_valid` re-proved.
* **Trusted statements restated (definition strengthened), text unchanged:** `modelOracle_valid` (and, through
  `Oracle.Valid`, the hypotheses/conclusions of `step_refines_manual`, `manual_step_deterministic`,
  `step_unique_of_choiceFree`, `interrupt_choice_exists`, `choiceFree_exact`), `modelImpl_valid`. Docstrings in
  `Statements.lean` updated. No model change.
* **B1/B2, model fix (`Step.lean`, multiply-add family):** the FCSR of `MADD/MSUB/NMADD/NMSUB.fmt` is per
  instruction: each operation (multiply, add/subtract, negate) is rounded and trap-checked with Cause = the
  union of the conditions so far (`fpStep`, `Mips.Fp.setCause`, `Mips.Fp.accFlags`), Flags |= the union only
  when no operation traps (`fpFinishS/D`). Citations: MADD.fmt p.256 / MSUB.fmt p.287 / NMADD.fmt p.308 /
  NMSUB.fmt p.310 (MD00086 Vol II-A Rev 6.06: "The Cause bits are ORed into the Flag bits if no exception is
  taken"); MD00082 Vol I-A Rev 6.01 Table 6.8 `Cause` p.94, §6.7.1 p.99. Transcription: `Manual.FPCheck` (Cause +
  CheckFPException, no Flags) then `FPResult` with the union (`Manual/Ops/FpuArith.lean`). Reference:
  `Mips.Fp.MaddSpec` restated with `OpAcc`/`OpDone` (`OpThen` removed). Proofs: `FpOpsCorrectStep`
  (`two_stepsS/D`, `three_stepsS/D`, `opAcc_mid`, `opAcc_last`, `finishS/D_setCause`; removed `then_outcome`,
  `finishS_outcome`, `finishD_outcome`), `FpOpsCorrectFcsr` (`setCause_bit`, `fpeEnabled_setCause`,
  `fpUpdate_setCause`, `setCause_setCause`, `fpUpdate_of_enabled`, `Flags.none_or`), `Refine/BridgeFpu`
  (`FPCheck_run`, `runAbs_FPCheck`), `Refine/FpuArith` (the eight `*_refines` re-proved), `Refine/ChoiceFp`
  (`FPCheck_eq`, `fpc_fpc`, `fpf_fpc`, `trapC_fpc`, `mul_inv_q`, `or_inv_absorb`, `inv_or_true`),
  `Manual.MaddAbsorbs` changed (first corner now needs `fr` a signaling NaN; second corner added: `fs`, `ft`
  even, `fr` odd, Invalid product), `cf_maddD/cf_msubD` re-proved, the NMADD/NMSUB choice rows now separate the
  readings `A`/`A'` by the result's sign (`row_AA'S`, `row_AA'D`) since Invalid of the negate no longer tells
  `A` from `B` when an earlier operation raised it. Trusted statements restated (definition `MaddSpec`
  changed, text unchanged): `maddS_separate` … `nmsubD_separate` (8); docstrings updated.
* **C-2 / F17, model change (`Step.lean`, `Instruction.lean`):** `Config1.M = 1` (`0x8000_0001`), `Config2`
  (16,2) = `0x8000_0000`, `Config3` (16,3) = 0, read-only (MD00090 Vol III Rev 6.02 §9.46 p.237, §9.47 p.241,
  §9.48 p.245); `decode` accepts `mfc0`/`mtc0` of (16,2), (16,3). `Impl.Config2/Config3` added, `Impl.WF` requires
  them. Trusted statements restated: `mfc0_spec_raw` (Config1 value; new (16,2)/(16,3) arms), `mtc0_spec_raw`
  (new arms, write ignored).

## Wave 12b (the spec's own decoder): trusted surface 211 → 216

* **Added (Statements, StatementsProofs, `comparator.json`):** `decode_diagram_sound`, `decode_diagram_complete`,
  `decode_agrees_manual`, `decode_none_manual`, `decoderSound_decodeDiagram`; `grep -c '^theorem'
  Semantics/Statements.lean` is **216**. The top theorems (`step_eq_manual`, `step_refines_manual`,
  `run_refines_manual`, `step_unique_of_choiceFree`) are restated with the spec's own decoder
  `Manual.decodeDiagram` (`Semantics/Manual/Decode.lean`, from `Manual.enc`) in place of the model's `decode`; no
  hypothesis added, conclusions unchanged. Proofs: `Refine/DecodeDiagram.lean`, `Refine/DecodeBridge.lean`.
* **Independence check on the elaborated environment:** gate step 1 also runs `scripts/manual_deps.py`
  (`scripts/ManualIndependence.lean`); its allow-list is the list of items the spec shares with the model
  (README (b′)).
