# Semantic MIPS

A small-step operational semantics of a pre-Release-6 MIPS32 processor, written in Lean 4, with an
assembler, a specification and proofs, two differential oracles (MARS 4.5; `qemu-system-mips` with
`llvm-mc`), and a gate script that runs all of them.

Extracted from [VibeCheck](https://github.com/rShyvers/VibeCheck) (a
hackathon project that builds a consumer product on top of this semantics)
so the semantics can be read, built, and reviewed on their own, with no
dependency on anything else in that project.

## What this is

- `Semantics/Step.lean`: `step : State → State` is **one instruction time** of the processor (an enabled interrupt
  is taken first; after `wait` the processor stays in standby until an interrupt request; otherwise fetch from
  memory through the Fixed Mapping MMU of `State.lean`, strict decode, execute, commit; then the timer) and
  nothing else: it never halts, and every exception is a state transition.
  `run : State → Nat → State` is `step` iterated `n` times.
- `Semantics/Env.lean`: the environment, **explicitly outside the architecture**: the loader `load : Program →
  State` (writes the assembled image into physical memory, each word at the physical address of its virtual
  address), the MARS-style `syscall` services (1, 4, 10, 11) and the
  conventions for stopping a run (`runHosted`). `MipsRun` and the harnesses use the hosted run.
- `Semantics/Instruction.lean`: the `Instruction` type (183 constructors), `decode` (strict) and `encode`.
- `Semantics/Asm.lean`: an assembler from source text to a `Program` (labels, directives, idioms, range checks).
- `Semantics/FpOps.lean`: the floating-point unit, defined on bit patterns without host floats.
- `Semantics/Specs/`, `Semantics/Statements.lean`: the specification and its proofs (see below for exactly what
  they establish).
- `Semantics/Manual/`: an **independent transcription of the manuals** (the Operation pseudocode of every
  instruction page, exception processing, interrupts, the timer, reset, the instruction diagrams), written
  without naming any definition of the model (`scripts/manual_independence.py` checks this), and
  `Semantics/Refine/`: the proof that `step` refines it (`step_eq_manual`, below; `docs/MANUAL-SPEC.md`).
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

**(b) The trusted surface for `lake comparator`.** `Semantics/Statements.lean` (1857 lines) states **159 theorems**
with their proofs elided. `Semantics/StatementsProofs.lean` states the same theorems in the same order and proves
each by the real theorem of the same name in `Semantics/Specs/` (the last 16: in `Semantics/Refine/`, `modelImpl_valid` in `Semantics/Manual/Choices.lean`). `lake comparator` (config: `comparator.json`)
checks, for each name, that the solution proves the *same statement* as the challenge, uses no axiom outside the
three above, and passes the kernel. It does not check that a statement is the right one. To review the project you
read `Statements.lean`, plus the definitions that it mentions: the model files (`Word`, `Types`, `State`,
`Instruction`, `FpOps`, `Step`, and `Env` for the hosted-run statements), the statement vocabulary
`Semantics/Specs/Defs.lean` and `WellFormed.lean`, and, for the 16 refinement statements, the manual specification
`Semantics/Manual/*` and `Semantics/Refine/Defs.lean` (`Refine.abs`, `Refine.Inv`). The 159 statements are a
selection: every global theorem below and at least one per-instruction statement per family. The arrangement and
its limits are in `docs/PROOF-NOTES.md`.

**(b′) The independent correctness result: `step` refines a transcription of the manual.** `Semantics/Manual/`
transcribes the manuals' pseudocode (each Operation copied from its instruction page and cited, the exception,
interrupt, timer and reset processing of Vol III, the instruction diagrams as `Manual.enc`) into an executable
specification `Manual.InstructionTime`, written independently of the model: it names no definition of
`Step.lean`/`State.lean` and shares with the model only the words, the `Instruction` names and the IEEE rounding core
of `FpOps.lean` (gate step 1 checks the imports and names, `scripts/manual_independence.py`). The theorem

```lean
theorem step_eq_manual (s : State) (hs : Refine.Inv s) :
    Manual.InstructionTime Manual.modelImpl Manual.modelOracle decode (Refine.abs s) =
      some (Refine.abs (step s))
```

says that from every state of the invariant `Refine.Inv`, one `step` is exactly one instruction time of the manual,
seen through the projection `Refine.abs`, with the manual's UNDEFINED/UNPREDICTABLE choices resolved as the model
pins them (`Manual.modelOracle`) and the manual's implementation constants as the model's (`Manual.modelImpl`). It
covers every path: interrupt, `wait` standby, the nullified delay slot of a branch-likely, fetch errors,
undecodable words, **all 183 instructions** (one `Refine.<ctor>_refines` each, collected by `allInstrRefines`), the
delay slot's `I+1` effects and the timer; `resetState_refines_manual` and `resetException_refines_manual` cover Reset.
With it, on the trusted surface: `step_refines_manual` (`step` is a `Manual.Step`, a behaviour the manual allows for
*some* valid resolution of its choices), `modelOracle_valid` (the model's choices are valid), `run_refines_manual`
(`n` steps), `step_unique_of_choiceFree` and `manual_step_deterministic` (where the manual makes no choice,
`step` is the only behaviour it allows), `decoderSound_decode` (the model's `decode` is sound for the manual's
diagrams), and the invariant's establishment and preservation (`inv_resetState`, `inv_hostedStart`, `inv_load`,
`step_preserves_inv`). So a mistake in `Step.lean` survives only if the same mistake is in the independent
transcription, or in what is trusted below. Limits, stated plainly:
- `Manual.ChoiceFree` decides exactly where the manual leaves a choice that can change the result: `false` at an
  interrupt and at every exception other than Coprocessor Unusable (`Cause.CE` "is loaded, but not
  defined"), at a CTI in a delay slot, at a word with an UNPREDICTABLE field whose coprocessor is
  usable, and where the Operation reaches an oracle choice (`Manual.ConsultsOracle`: a load or store
  while `LLbit = 1`, `DIV`/`DIVU` by zero, `MUL`, an odd FPR used as a double on the path taken, a quiet
  NaN operand of `ABS`/`NEG`/`CVT.D.S`/`CVT.S.D` and a quiet-NaN sum in `NMADD`/`NMSUB`, `CFC1` of a missing
  register into `rt ≠ 0`, the UNPREDICTABLE arms of `CTC1`/`EXT`/`INS`, `rs = 31` links, `JALR rs = rd`,
  an MTC0/MFC0 of a missing register, an `EBase` write with `BEV = 0`). Soundness (`ChoiceFree` ⇒ every
  valid oracle gives the same instruction time) is proved for all 183 instructions
  (`Refine/ChoicePoints.lean`, `manual_step_deterministic`). Exactness (`ChoiceFree modelImpl dec a = false` ⇒
  two valid oracles give different instruction times) is proved for every case and every row since wave 9
  (`choiceFree_exact`, on the trusted surface; `Refine/ChoiceExact.lean`, the rows in
  `Refine/ChoiceRows*.lean`), so `ChoiceFree modelImpl dec a = true` holds exactly where the manual's
  instruction time is determined (`Refine.choiceFree_iff`). Proving it made three rows exact that were
  conservative before: `MFHC1` into `rt = 0`, `C.cond.D` whose even operand decides the comparison alone
  (`Manual.CmpAbsorbs`), and a corner of `MADD.D`/`MSUB.D` (`Manual.MaddAbsorbs`). Exactness is stated for the
  model's implementation constants `modelImpl` (for another `Impl` a `RECIP`/`RSQRT` approximation could hide
  the value read from an odd register); soundness holds for every `Impl`.
- `Manual.Oracle.Valid` formalizes the three restrictions on UNPREDICTABLE operations of MD00086 Vol II-A
  Rev 6.06 §1.2.1 (p.3-4): no dependence on the state inaccessible in the current mode (non-interference,
  `NIValue`/`NIOutcome`), no change to that state (`UnpredictableLimits`), no entry into the lower power
  mode (a one-step reading of "must not halt or hang"); the one restriction on UNDEFINED operations
  (§1.2.2, p.4); and quiet-NaN results for the QNaN choices of `CVT` (MD00082 §6.3.1.5, p.82). Not
  formalized: "when possible, this QNaN result is one of the operand QNaN values" (p.82), and
  `causeCE`/`storeClearsLL`/`loadClearsLL`, which the manual leaves open without these restrictions.
- `Manual.Impl.Valid` (`modelImpl_valid`) formalizes `RECIP.fmt`'s bound against the IEEE-mandated
  representation (1 ULP of the IEEE core's correctly rounded `1.0 / fs`, RECIP.fmt p.336). Not formalized:
  `RECIP.fmt`'s bound against the exact real result (it follows from the 0-ULP result only if the core's
  division is correctly rounded, which the core is trusted for, not proved), and `RSQRT.fmt`'s 2-ULP bound
  (p.343). For `RSQRT` the model computes `SQRT.fmt` then `DIV.fmt` (two roundings); a proof that this stays
  within 2 ULP of `1/sqrt(x)` needs an error bound for the core's rounding (`Mips.Fp.Format.roundCore`) and
  for its integer square root, which the repository does not have; wave 9 did not prove it (`docs/MANUAL-SPEC.md` I.7).
- The environment layer (`Env.lean`: loader, hosted services, stopping conventions) is outside `step` and outside
  the theorem; `inv_load` only says the loader's start state satisfies the invariant.

**(c) The per-instruction `_spec_raw` theorems restate the implementation.** There is one for each of the 183
constructors (`python3 scripts/trace.py`). 179 of the 183 `_spec_raw` theorems are proved by unfolding `step` and closing with `rfl`
(`step_spec`/`fp_step_spec` in `Semantics/Specs/Tactics.lean`; `break_spec_raw` and `syscall_spec_raw` have explicit
proofs; `ext_spec_raw` and `ins_spec_raw` are derived from `ext_spec_fields`/`ins_spec_fields`, which are, with the
`decode` field ranges of `decode_wellFormed`; `sll`/`srl`/`sra`/`rotr` rewrite `shamt` to `shamt % 32` first), and each states what `step` computes for that
instruction in terms of the model's own helper functions (`readReg`, `writeReg`, `signExt16`, ...; the `...Spec`
names in `Defs.lean` are abbreviations for the real definitions, not independent copies). Each has the form
`step s = timerTick (…)`: `step` is the instruction (`execute`) followed by the timer (`timerTick`, which only
advances `Count` and sets `Cause.TI`), so the instruction's own effect is the argument of `timerTick`. Since
interrupts exist (wave 6) each of them assumes `hexec : executesInstr s = true` — no interrupt is taken in this
step and the processor is not in standby — because otherwise the step is the Interrupt exception or a standby
step instead (`Specs/Interrupt.lean`); that hypothesis is a weakening of the earlier statements, forced by the model. They pin the behaviour
against regression and make each instruction's semantics readable in isolation. **They are not independent of the
implementation**: a mistake in `Step.lean` that is also a mistake in the reader's understanding of the manual
survives them. The evidence that the semantics matches the architecture is the refinement theorem in (b′), the manual
review recorded in `docs/AUDIT.md` and `SPEC-NOTES.md`, and the differential tests in (e).

The results that are genuinely global, or independent of how an individual instruction is written:

| Result | Where | In the trusted surface |
|---|---|---|
| `step` refines the independent manual transcription (every path, all 183 instructions); `run` likewise; the model's choices are valid; uniqueness at choice-free states; an interrupt is a real choice; `ChoiceFree` is exact (every state it rejects has two valid oracles that differ); Reset; the invariant | `Refine/Step.lean`, `Refine/Determinism.lean`, `Refine/ChoicePoints.lean`, `Refine/ChoiceExact.lean`, `Refine/Decode.lean`, `Manual/Choices.lean` | `step_eq_manual`, `step_refines_manual`, `run_refines_manual`, `step_unique_of_choiceFree`, `modelOracle_valid`, `manual_step_deterministic`, `interrupt_choice_exists`, `choiceFree_exact`, `modelImpl_valid`, `decoderSound_decode`, `resetException_refines_manual`, `resetState_refines_manual`, `step_preserves_inv`, `inv_resetState`, `inv_hostedStart`, `inv_load` |
| `decode (encode i) = some i` for every constructor, under `WellFormed` | `Specs/DecodeSpec.lean` | `decode_encode` |
| `$zero` is unchanged by every `step`, every `run` and every hosted run; a write to `$zero` is never observable | `Specs/Invariants.lean`, `Specs/Hosted.lean` | `step_preserves_zero_register`, `run_preserves_zero_register`, `run_initialState_zero_register`, `zero_write_not_observable`, `runHosted_preserves_zero_register` |
| register files keep size 32 under `step`; `run` from `initialState` is well-formed | `Specs/RegFileSize.lean` | `step_preserves_wellFormed`, `run_initialState_wellFormed` |
| exception entry: vector, `EXL`, pending branch abandoned, `LLbit` cleared, `EPC`/`Cause.BD` with and without delay slot, `ExcCode`, `CE` | `Specs/Exception.lean` | `exceptionEntry_always`, `_exl0_not_in_delay_slot`, `_exl0_in_delay_slot`, `_exl1`, `_excCode` (`_ce` is in `Exception.lean` only) |
| fetch from memory; fetch/decode failure: misaligned `pc`, undecodable word, Reserved Instruction, Coprocessor Unusable for an undecodable COP0/CACHE word outside Kernel Mode | `Specs/Fetch.lean` | `step_fetches_from_memory`, `step_misaligned_pc`, `step_undecodable`, `step_reserved_instruction`, `step_reserved_cop0_unusable` |
| self-modifying code: a store to the next instruction is what executes next | `Specs/SelfModifying.lean` | `sw_next_instruction_is_fetched`, `store_changes_next_instruction` |
| address translation (Fixed Mapping MMU): each segment's mapping incl. `ERL = 1`; kseg0/kseg1 aliasing; from User Mode a kernel address is an Address Error (fetch, load, store) and changes no memory | `Specs/Mmu.lean` | `fixedMappingPA_kuseg_erl0`, `_kuseg_erl1`, `_kseg0`, `_kseg1`, `_kseg23`, `_kseg0_kseg1_alias`, `translate_user_kernel_address`, `translate_erl1_kuseg_identity`, `step_fetch_user_kernel_address`, `lw_user_kernel_address`, `sw_user_kernel_address`, `kseg1_store_visible_through_kseg0` |
| loader correctness: after loading, a fetch or load of an image address returns the image word | `Specs/Loader.lean` | `load_readMemWord`, `load_step_fetches_image`, `loadAtReset_readMemWord_kseg` |
| general delay-slot theorem; a control transfer in a delay slot raises Reserved Instruction (pin) | `Specs/DelaySlot.lean` | `delay_slot_commits_target`; `branch_in_delay_slot_reserved_instruction` |
| the hosted run is `step` whenever it neither stops nor performs a service; the services | `Specs/Hosted.lean` | `hostStep_eq_step`, `runHosted_agrees_with_run`, `hosted_print_int`, `hosted_exit` |
| Coprocessor Unusable | `Specs/FpuCommon.lean`, `Specs/Cp0.lean` | `fp_coprocessor_unusable`, `cp0_instruction_user_mode_unusable` |
| operating modes: User Mode is `UM = 1`, `EXL = ERL = 0`; CP0 unusable exactly in User Mode with `CU0 = 0`; exception entry enters Kernel Mode (UM kept); `eret` returns to User Mode | `Specs/Mode.lean` | `userMode_iff`, `cp0Usable_false_iff`, `exceptionEntry_enters_kernel_mode`, `exception_from_user_mode_enters_kernel_mode`, `eret_to_user_mode` |
| timer: `Count` + 1 per step unless `Cause.DC = 1` or the instruction writes `Count`/`Compare`/`Cause` (proved over every constructor); `Count = Compare` sets `Cause.TI`; a `Compare` write clears it; `Cause` reads `TI` and `IP7`; `rdhwr` values and access rule (Kernel Mode or `CU0`, or the `HWREna` bit; Reserved Instruction otherwise) | `Specs/Timer.lean` | `step_count_advances`, `step_count_stopped`, `step_timer_match_sets_ti`, `step_timerInt`, `mtc0_count_spec`, `mtc0_compare_clears_ti`, `causeValue_timer`, `rdhwr_spec_raw`, `hwrValue_*`, `rdhwr_reserved_unimplemented`, `rdhwr_reserved_not_enabled`, `rdhwr_allowed`, `hwrena_write_masked`, `resetException_timer` |
| interrupts: taken exactly when `IE = 1`, `EXL = ERL = 0` and some `Cause.IP & Status.IM` is set, before the instruction at `pc`; entry (`ExcCode` 0, `EPC`/`BD`), vector `0x180`/`0x200` by `Cause.IV`; software, timer and hardware-line requests; the lines are inputs no step writes; standby after `wait`; `IntCtl`/`SRSCtl` values; `rdpgpr`/`wrpgpr` | `Specs/Interrupt.lean`, `Specs/Cp0.lean` | `step_interrupt`, `interruptTaken_iff`, `no_interrupt_ie0`/`_exl`/`_erl`/`_masked`, `takeInterrupt_not_in_delay_slot`, `takeInterrupt_in_delay_slot`, `interruptVector_iv0`/`_iv1_bev0`/`_iv1_bev1`, `mtc0_cause_requests_software_interrupt`, `timer_requests_interrupt`, `step_hwInt`, `wait_spec_raw`, `step_standby_stays`/`_restarts`/`_interrupt`, `intCtlValue_fields`, `srsCtlValue_fields`, `mfc0_srsctl_spec`, `rdpgpr_spec_raw`, `wrpgpr_spec_raw` |
| Reset exception and reset state; the hosted start state is reset followed by the environment's boot convention (and equals `initialState textBase`) | `Specs/Reset.lean` | `resetException_spec`, `resetState_spec`, `hostedStart_is_reset_then_boot` |
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
  termination are compared. The last full gate run (`.gate/last-run.json`, step 7) reports 159 tests (`tests/oracle`
  plus the `tests/asm` programs the harness can run): 142 pass, 17 are **declared deviations where QEMU departs
  from the manual** (the manual wins), 0 known model bugs, 5 skipped (unsupported by the harness). The deviations
  carry their citations in the tests' own `# oracle: expect-deviation` directives (`SPEC-NOTES.md` §10 has the
  table): misaligned `sc` (MD00086 Vol II-A Rev 6.06, SC, p.349); misaligned `lwxc1`/`ldxc1`/`swxc1`/`sdxc1`,
  QEMU performs the access (LWXC1 p.254, LDXC1 p.218, SWXC1 p.406, SDXC1 p.364); `FCSR.FS` flush leaves
  Underflow/Inexact clear (MD00082 Vol I-A Rev 6.01 §6.7.2.4, p.102); `abs`/`neg` of a NaN does not signal
  Invalid (MD00086 ABS.fmt p.32, NEG.fmt p.307); Inexact set with an enabled Overflow trap (MD00082 §6.7.2.6,
  p.102); `madd`/`msub`/`nmadd`/`nmsub` fused by QEMU where the manual says "as if separate floating-point"
  operations "were executed" (MADD.fmt p.256, MSUB p.287, NMADD p.308, NMSUB p.310; seven tests); `rdhwr 29` in
  Kernel Mode returns a value although QEMU's Config3 reads 0, so UserLocal is not implemented (MD00086 RDHWR
  p.333; MD00090 Vol III Rev 6.02 §9.11, p.143); and the legacy NaN of `tests/asm/fp_legacy_nan` (declared in
  `scripts/oracle.py`).
  Not covered: EBase relocation, `Status.ERL` writes. Interrupts and `wait` are covered by the `irq_*` programs
  (bare, with their own `.ktext` handlers).
- *LLVM encoding oracle* (`llvm-mc -triple=mips-unknown-elf -mcpu=mips32r2`): the assembler's output is compared
  word for word on 609 forms (`tests/oracle/encodings.list`): 592 identical, 17 declared differences (our
  `li`/`la`/`move`/`abs` expansions follow MARS/SPIM).

**(f) What is trusted.** Lean and its kernel; the three standard axioms; the manuals *as read by the authors*
(nothing machine-checks the reading); the statements in `Statements.lean` and the definitions they mention (the
model itself). For the refinement result (b′) that is precisely: the `Semantics/Manual/*` definitions (the
transcription; each Operation cites its page), the choices `Manual.modelImpl`/`Manual.modelOracle` (each a
documented pin in `SPEC-NOTES.md`, and `modelOracle_valid` checks them against the manual's limits), `Refine.abs` (a
field-by-field projection) and `Refine.Inv` (established at reset and load and preserved by `step`, so not vacuous),
and the IEEE rounding core of `FpOps.lean` (`Mips.Fp.f32Add` …, wrapped as `Manual.IEEE.*`), which both sides share,
so a rounding bug there would not be caught by the refinement (see (d)); not their proofs (`Semantics/Refine/*`,
kernel-replayed). Also trusted: the assembler, which is **tested but not proved** (`Semantics/Tests/AsmTests.lean`, the LLVM oracle,
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
| R-type jump register | 4 | 4 | 2 | 4 | jr, jalr, jr.hb, jalr.hb |
| R-type SPECIAL2 bit-count | 2 | 2 | 2 | 2 | clo, clz |
| R-type GPR multiply, SPECIAL2 | 1 | 1 | 1 | 1 | mul |
| R-type multiply-accumulate, SPECIAL2 | 4 | 4 | 4 | 4 | madd, maddu, msub, msubu |
| R-type SPECIAL3 BSHFL sign-extend | 3 | 3 | 0 | 3 | seb, seh, wsbh |
| R-type SPECIAL3 bitfield extract/insert | 2 | 2 | 0 | 2 | ext, ins |
| SPECIAL3 RDHWR | 1 | 1 | 0 | 1 | rdhwr |
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
| Coprocessor 0 | 8 | 8 | 0 | 8 | mfc0, mtc0, di, ei, eret, wait, rdpgpr, wrpgpr |
| Coprocessor 1 | 15 | 15 | 6 | 15 | mfc1, mtc1, mfhc1, mthc1, cfc1, ctc1, lwc1, swc1, ldc1, sdc1, lwxc1, ldxc1, swxc1, sdxc1, prefx |
| Arithmetic, single | 18 | 18 | 16 | 18 | add.s, sub.s, mul.s, div.s, sqrt.s, abs.s, mov.s, neg.s, recip.s, rsqrt.s, round.w.s, trunc.w.s, ceil.w.s, floor.w.s, cvt.w.s, cvt.d.s, cvt.s.w, cvt.d.w |
| Arithmetic, double | 16 | 16 | 10 | 16 | add.d, sub.d, mul.d, div.d, sqrt.d, abs.d, mov.d, neg.d, recip.d, rsqrt.d, round.w.d, trunc.w.d, ceil.w.d, floor.w.d, cvt.w.d, cvt.s.d |
| Compare | 2 | 2 | 2 | 2 | c.cond.s, c.cond.d |
| Conditional moves | 10 | 10 | 6 | 10 | movf.s, movt.s, movf.d, movt.d, movn.s, movz.s, movn.d, movz.d, movf, movt |
| Multiply-add family | 8 | 8 | 0 | 8 | madd.s, msub.s, nmadd.s, nmsub.s, madd.d, msub.d, nmadd.d, nmsub.d |
| FP branches | 4 | 4 | 2 | 4 | bc1f, bc1t, bc1fl, bc1tl |
| **Total** | **183** | **183** | **119** | **182** | |

Columns count constructors of `Instruction`. "Spec theorem": has a `<ctor>_spec_raw`/`_spec` theorem. "MARS corpus" / "QEMU oracle": the mnemonic occurs as an instruction in a `tests/corpus/*.asm` / `tests/oracle/*.asm` program (a text scan; it shows the instruction is exercised, not that every behaviour is).
<!-- END GENERATED -->

## What is not modeled

Nothing here is implemented, and an access raises Reserved Instruction (or Coprocessor Unusable for COP2 words).
Details, manual citations and priorities are in `docs/spec/MIPS-COVERAGE-GAPS.md`.

- Instructions: `cache`, `tlbp`, `tlbr`, `tlbwi`, `tlbwr`, `sdbbp`, `deret`, the
  coprocessor-2 family (`cop2`, `mfc2`, `mtc2`, `cfc2`, `ctc2`, `lwc2`, `swc2`, `ldc2`, `sdc2`, `bc2f`/`bc2t`/
  `bc2fl`/`bc2tl`), `luxc1`, `suxc1`, the L format (`cvt.l`, `round.l`, `trunc.l`, `ceil.l`, `floor.l`,
  `cvt.s.l`, `cvt.d.l`) and paired-single (`*.ps`, `alnv.ps`, `cvt.ps.s`, `cvt.s.pl`/`pu`, `pll`/`plu`/`pul`/`puu`).
  `pause` and `nal` assemble and decode as `sll $0,$0,5` and `bltzal $0` (`PAUSE` executes as the NOP the manual permits).
- State: vectored (VI) and external-controller (EIC) interrupt modes (interrupt compatibility mode is modeled, with
  `IntCtl` and `SRSCtl` as constants: `IPTI = 7`, `VS = 0`, `HSS = 0`), `SRSMap`, `UserLocal` (so `rdhwr 29`),
  shadow register sets beyond the normal GPRs, the TLB (the
  MMU is the Fixed Mapping MMU, `Config.MT = 3`, with kseg0/kseg1 aliasing and the User-Mode Address Errors;
  SPEC-NOTES §9 item 27), caches, `WatchLo`/`WatchHi`, EJTAG,
  coprocessor 2, `Config2`..`Config5`.
- The manuals themselves are inconsistent about the L format with `FR = 0` (`FIR.L = 1` is required, the L-format
  instructions are UNPREDICTABLE with `FR = 0`); the model reports `FIR.L = 1` and leaves the L format undecoded (SPEC-NOTES §9 item 13).

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
comparator.json                the 159 trusted theorem names, challenge and solution modules
Semantics/Word, Types, State, Instruction, Asm, FpOps, Step .lean   the model (definitions only)
Semantics/Env.lean             the environment (loader, hosted services, stopping conventions): not the architecture
Semantics/FpOpsFacts.lean, FpCompareFacts.lean   kernel-checked facts about FpOps
Semantics/Specs/               the specification: Defs, WellFormed (vocabulary); Lemmas, Tactics, Fixtures (plumbing);
                               DecodeSpec, Exception, Fetch, SelfModifying, DelaySlot, Invariants, RegFileSize,
                               Mode, Reset, Mmu, Loader, Hosted (global theorems);
                               one file per instruction family (Arith, Shift, MulDiv, ..., FpuArith, ...); StepSpec (index)
Semantics/Manual/              the independent transcription of the manuals (Arch, Pseudocode, CP0, Memory, FPU,
                               Exceptions, Interrupts, Timer, Reset, Encoding, Ops/<Family>, Operation, Cycle, Relation)
Semantics/Refine/              the refinement of Manual by step: Defs (abs, Inv), bridges, one file per family
                               (<ctor>_refines), Cycle, Decode, Invariant, Instr (allInstrRefines), Step, Determinism
Semantics/Statements.lean      the trusted surface (159 statements, proofs elided)
Semantics/StatementsProofs.lean  the same statements, proved from Specs and Refine
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
2. The model (4344 lines in all): `Semantics/Word.lean` (32), `Types.lean` (240), `State.lean` (148),
   `Instruction.lean` (1370), `FpOps.lean` (1172), `Step.lean` (1382). `DESIGN.md` is the map. The environment
   around it (not the architecture): `Env.lean` (195).
3. The statements: `Semantics/Specs/Defs.lean` (109), `WellFormed.lean` (194), then `Semantics/Statements.lean` (1857).
   For the refinement statements (its last section): `docs/MANUAL-SPEC.md`, `Semantics/Manual/Cycle.lean` and
   `Relation.lean` (the instruction time and the relation), `Manual/Ops/*` (one Operation per manual page),
   `Manual/Choices.lean` (the pins), `Semantics/Refine/Defs.lean` (`abs`, `Inv`).
4. For any instruction family: `Semantics/Specs/<Family>.lean`; the index and table is `Specs/StepSpec.lean` (114).
5. `docs/TRACE.md` (486 lines, generated): one row per instruction, from manual page to tests.
6. `docs/spec/SPEC-NOTES.md`: every pin and divergence; `docs/spec/MIPS-COVERAGE-GAPS.md`: what is missing;
   `docs/AUDIT.md`: what was checked against the manuals.
7. Not required for trust: `Specs/Lemmas.lean`, the proof-device parts of `DelaySlot`, `Invariants`, `RegFileSize`,
   `FpOpsFacts`, `FpCompareFacts` and `Tactics`; the kernel replays them.

## MipsRun

`lake exe MipsRun [--max-steps N] [--bare] [--reset] [prog.asm]` assembles a program (file or stdin), loads it (`Env.load`)
and runs it hosted (`Env.runHosted`; default bound 1000000 steps), printing one JSON object. The hosted run
performs the MARS-style `syscall` services 1/4/10/11 and stops by the environment's conventions (exit, an
exception vector the loaded image does not cover, `pc` outside the image); `--bare` performs no service, so every
`syscall` is the architectural System Call exception (the stopping conventions still apply). The default start state
is the architectural reset state followed by the environment's boot convention (`Env.hostedStart`: `pc = 0x0040_0000`,
`Status = CU1`, `$sp = 0x7FFF_EFFC`); `--reset` starts from the reset state itself (`pc = 0xBFC0_0000`,
`Status.BEV = ERL = 1`), so the program must provide boot code at the reset vector (`.ktext 0xBFC00000`). Exit code 0:
assembled and ran to a stop or the step limit; 1: assembly failed (`"assembled": false`, `"error"` set, other
fields `null`); 2: usage or I/O error (no JSON).

Fields (success): `assembled`, `halted`, `halt_reason`, `steps`, `output`, `registers` (by ABI name), `error`
(`null`); then `halt` (`{"kind": ...}`: `exit`, `unhandled_exception` with `code`/`epc`/`badvaddr`, `no_instruction`
with `pc`, or `limit`), `initial` (the loader's start state, before the image is written) and `final` (each: `pc`, `gpr`, `hi`, `lo`,
`fpr` as raw 32-bit values, `fcsr`, `fp_cond_flag` (= FCSR bit 23, kept for compatibility), `ll_bit`, `ll_addr`,
`pending_branch`, `cp0` with `status`, `cause`, `epc`, `badvaddr`, `errorepc`, `ebase`), `fcsr_mask`, `image`
(`[address, word]` for every assembled word, by **virtual** address), `memory` (every nonzero aligned word of the
final physical memory, reported at its virtual address `Env.canonicalVAddr`: kuseg for the loaded text/data/stack,
kseg0 for the low 512 MB, identity for kseg2/kseg3; a word visible through both kseg0 and kseg1 appears once, under
kseg0) and `physical_memory` (the same words by physical address). `pc`, registers, EPC and BadVAddr are virtual.

**The `halt_reason` strings changed from the VibeCheck-era ones** (`illegal_instruction:0x...`,
`address_error:0x...`, `arithmetic_overflow`, `branch_in_delay_slot`). Overflow, address errors, reserved
instructions, `break`, traps and unknown syscalls are now architectural exceptions, so the strings are `exit`,
`unhandled_exception:<name>:epc=0x<EPC>` (address errors append `:badvaddr=0x<BadVAddr>`; `<name>` is
`address_error_load`, `address_error_store`, `syscall`, `breakpoint`, `reserved_instruction`, `coprocessor_unusable`,
`arithmetic_overflow`, `trap` or `exccode_N`) and `no_instruction:0x<pc>`; `halt_reason` is `null` when the step
limit is reached. `branch_in_delay_slot` no longer occurs: a control transfer in a delay slot is the Reserved
Instruction exception (`unhandled_exception:reserved_instruction:...` when no handler is loaded).

## License / provenance

MARS 4.5 (`vendor/mars/Mars4_5.jar`) is a third-party simulator, vendored
here only as a differential-testing oracle; see its own license. Everything
else in this repository was written for this project.
