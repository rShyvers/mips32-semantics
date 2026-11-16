# MIPS32 Release 6 Semantics: full overview

This is the long-form overview that was the code branch's README up to commit fa69c20; the code branch now carries a short README. Paths are relative to the code checkout with this branch mounted at `docs/`.

A small-step operational semantics of a **MIPS32 Release 6** processor (the final MIPS32), written in Lean 4, with an
assembler, a specification and proofs, two differential oracles (QEMU `qemu-system-mipsel -cpu mips32r6-generic` with
`llvm-mc -mcpu=mips32r6`, and, for the corpus programs that are valid Release 6, MARS 4.5), and a gate script that
runs all of them. The earlier Release 2 model (big-endian, 32-bit FPU, legacy NaN, 179 constructors at its last
count) was replaced in place; it is kept only at the git tag `mips32r2-final` of the code repository. Nothing below
describes it except where a passage says so.

Extracted from [mips32-semantics-demo](https://github.com/rShyvers/mips32-semantics-demo) (formerly VibeCheck) (a
hackathon project that builds a consumer product on top of this semantics)
so the semantics can be read, built, and reviewed on their own, with no
dependency on anything else in that project.

## What this is

- `Semantics/Step.lean`: `step : State → State` is **one instruction time** of the processor (an enabled interrupt
  is taken first; after `wait` the processor stays in standby until an interrupt request; otherwise fetch from
  memory through the Fixed Mapping MMU of `State.lean`, strict decode, execute, commit; then the timer) and
  nothing else: it never halts, and every exception is a state transition. `step = timerTick ∘ stepCore`.
  `run : State → Nat → State` is `step` iterated `n` times. What each instruction does is in
  `Semantics/Exec/<Family>.lean` (one file and one table per family; `execBody` = the first table that handles the
  instruction, `docs/DESIGN.md` §4).
- `Semantics/Env.lean`: the environment, **explicitly outside the architecture**: the loader `load : Program →
  State` (writes the assembled image into physical memory, each word at the physical address of its virtual
  address), the MARS-style `syscall` services (1, 4, 10, 11) and the
  conventions for stopping a run (`runHosted`). `MipsRun` and the harnesses use the hosted run.
- `Semantics/Types.lean` and `Semantics/Instruction.lean`: `Release`/`Profile` (one release, `r6`; byte order
  little-endian), the `Instruction` type (**203 constructors**), `decode` (strict; `decode = decodeFor
  profile.release`, one decoder table per release) and `encode`.
- `Semantics/Asm.lean` and `Semantics/Asm/*`: an assembler from source text to a `Program` (one encoder table per
  family; labels, directives, idioms, range checks). Tested, not proved.
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

The target is **MIPS32 Release 6** (owner decision 2026-11-16), as one profile (`profile : Profile =
{ release := .r6, bigEndianMem := false }`, `Semantics/Types.lean`):

- **Little-endian only.** `Config5.DEC = 0` ("Only Little-Endian mode supported. Any implementation must support
  Little-endian mode", MD00090 Vol III Rev 6.02 §9.50, Table 9.69, p.261), `Config.BE = 0`. The byte order sits behind
  one profile constant, `bigEndianMem`.
- **Delay slots and compact branches.** One branch delay slot for the branches and jumps that have one; the Release 6
  compact branches and compact jumps have none, with a *forbidden slot* after a conditional compact branch that is not
  taken (MD00082 Vol I-A Rev 6.01 §5.3.2.1-5.3.2.2, p.62). No branch-likely instructions, so no instruction is nullified.
  A control transfer in a delay slot or forbidden slot raises Reserved Instruction.
- **No `HI`/`LO`.** The multiply and divide family is the Release 6 `MUL`/`MUH`/`MULU`/`MUHU`/`DIV`/`MOD`/`DIVU`/`MODU`
  (three register operands). The Release 2 `MULT`/`MADD`/`MFHI`/..., `MOVN`/`MOVZ`, `ADDI`, `LWL`/`LWR`/`SWL`/`SWR`,
  the trap-immediates and every other encoding that Release 6 removes ("6R"/"6Rm", MD00086 Vol II-A Rev 6.06 Table A.1,
  p.451) do not decode and raise Reserved Instruction.
- **64-bit FPU** (`Status.FR = 1`, read-only), IEEE 754-2008 NaN (`FIR.Has2008 = 1`, `FCSR.NAN2008 = ABS2008 = 1`),
  the Release 6 FP instructions (`CMP.cond.fmt`, `SEL`, `SELEQZ`/`SELNEZ`, `MIN`/`MAX`/`MINA`/`MAXA`, `MADDF`/`MSUBF`,
  `RINT`, `CLASS`, `BC1EQZ`/`BC1NEZ`), the L format. No paired-single, no `COP1X`, no FP condition codes.
- **Misaligned load/store = Address Error** (permitted: MD00082 Vol I-A Rev 6.01 Appendix B.2, p.128); `LL`/`SC`
  always. Fixed Mapping MMU (`Config.MT = 3`, MD00090 Vol III Rev 6.02 Appendix A.1, p.313-317), kseg0/kseg1 aliasing.
- **No optional modules**: MSA, microMIPS, VZ, MT, DSP, EVA, XPA, MCU, CRC, GINV, VP (`DVP`/`EVP` are the NOP the manual
  gives for `Config5.VP = 0`), EJTAG; their configuration bits read 0.
- **Coprocessor 0** is a table keyed by `(rd, sel)` (`cp0Layout`, `Semantics/Exec/Cp0.lean`); a register the table does not
  name reads 0 and ignores writes. `Status.CU0` no longer exists: bit 28 is `RW`, and Coprocessor 0 is usable in Kernel Mode only.

The latest manual revisions are normative: **MD00086 Vol II-A Rev 6.06**, **MD00090 Vol III Rev 6.02**,
**MD00082 Vol I-A Rev 6.01** (`manuals/`). Where the manual and an emulator disagree, the manual
wins and the difference is recorded (`docs/spec/SPEC-NOTES.md`); QEMU and LLVM are the oracles, MARS (which cannot run
Release 6) only checks the corpus programs that are valid Release 6. Where the manual says UNPREDICTABLE the model makes a choice and records it as a pin in
`SPEC-NOTES.md`; a pin is not an architectural statement. Emulator-compatibility toggles may be added later; none exist.
Earlier releases (R5, R3, R2, R1) are to be added later, backwards, as further profiles: the release-specific pieces
are already keyed (`Release`, a decoder table per release, `cp0Layout`) and nothing of another release is implemented.
MIPS64, DSP, MSA, microMIPS and MIPS16e are out of scope.

## What is proved, what is tested, what is trusted

Read this section before the numbers elsewhere. It says what each kind of evidence does and does not establish.

**(a) Kernel-checked.** `lake check` replays the library `Checked` (`Checked.lean`: the model, all of
`Semantics/Specs`, `StatementsProofs`, the facts files and the tests) in the kernel and the gate requires that the
axioms used are a subset of `propext`, `Classical.choice`, `Quot.sound`. The gate's step 1 rejects `sorry`, `admit`,
`axiom`, `native_decide`, `bv_decide`, `partial def`, `unsafe`, `@[implemented_by]` and `@[extern]` in the code of
every file under `Semantics/` (comments and strings stripped); the one allow-listed `sorry` is in
`Semantics/Statements.lean` (below), which nothing in `Checked` imports. So there is no `sorry` in anything
`Checked` imports.

**(b) The trusted surface for `lake comparator`.** `Semantics/Statements.lean` (2432 lines) states **221 theorems**
with their proofs elided. `Semantics/StatementsProofs.lean` states the same theorems in the same order and proves
each by the real theorem of the same name in `Semantics/Specs/` (the 21 refinement statements: in `Semantics/Refine/`, the five decoder statements through `Refine.decode_*` and `Refine.rejected_consults`, `modelImpl_valid` in `Semantics/Refine/ImplValid.lean`; the 60 floating-point statements, the 16 of the rounding core, the 33 of the operations and the 11 of the Release 6 FP instructions: in `Semantics/FpOpsCorrect*.lean`). `lake comparator` (config: `comparator.json`)
checks, for each name, that the solution proves the *same statement* as the challenge, uses no axiom outside the
three above, and passes the kernel. It does not check that a statement is the right one. To review the project you
read `Statements.lean`, plus the definitions that it mentions: the model files (`Word`, `Types`, `State`,
`Instruction`, `FpOps`, `Step`, and `Env` for the hosted-run statements), the statement vocabulary
`Semantics/Specs/Defs.lean` and `WellFormed.lean`, and, for the 21 refinement statements, the manual specification
`Semantics/Manual/*` and `Semantics/Refine/Defs.lean` (`Refine.abs`, `Refine.Inv`), and, for the 60 floating-point
statements, the IEEE 754 and FPU reference `Semantics/FpOpsSpec.lean` (see (d)). The 221 statements are a
selection: every global theorem below and at least one per-instruction statement per family. The arrangement and
its limits are in `docs/PROOF-NOTES.md`.

**(b′) The independent correctness result: `step` refines a transcription of the manual.** `Semantics/Manual/`
transcribes the manuals' pseudocode (each Operation copied from its instruction page and cited, the exception,
interrupt, timer and reset processing of Vol III, the instruction diagrams as `Manual.enc`) into an executable
specification `Manual.InstructionTime`, written independently of the model: it names no definition of
`Step.lean`/`State.lean`. It shares with the model exactly the items the environment-level allow-list of
`scripts/ManualIndependence.lean` declares (gate step 1: the import/name scan `scripts/manual_independence.py` and
the walk over the elaborated environment `scripts/manual_deps.py`): the words (`W32`, `VAddr`, `PAddr`); the
`Instruction` type, as names and fields only (not `decode`, `encode` or the CP0 register table); and from `FpOps.lean`
(the `Mips.Fp.*` names) the IEEE core: the correctly rounded `f32`/`f64` `Add`, `Sub`, `Mul`, `Div`, `Sqrt`,
`f32Relation`/`f64Relation` and the conversions `f32ToF64`, `f64ToF32`, `f32ToW32`, `f64ToW32`, `w32ToF32`, `w32ToF64F`, the longword (L format) conversions `f32ToW64`, `f64ToW64`, `w64ToF32`, `w64ToF64`, and the Release 6 `f32Fma`/`f64Fma` (fused), `f32MinMax`/`f64MinMax`, `f32Class`/`f64Class`, `f32Rint`/`f64Rint`;
the formats (`Format`, `binary32`, `binary64`, `isFinite`, `orderKey`) and `FpRel`; the NaN classifiers `isQNaN32/64`,
`isSNaN32/64` and the default NaNs `defaultQNaN32/64`; and the FCSR helpers `Env` (`RN`, `flush`, `rm`), `Flags`
(`none`, `invalidOnly`, `or`, `toBits`, the five field projections) and the two FCSR-to-environment decoders
`RoundingMode.ofBits` and `Flags.ofBits`. Not shared: `fpUpdate`, `envOf`, the model's sign operations, the
`Format.is*` classifiers (the spec classifies encodings by its own Table 6.2 transcription; the allow-list in `scripts/ManualIndependence.lean` is the authority for the exact set). The two decoders are
shared, not independently transcribed: they are correct by MD00082 Vol I-A Rev 6.01 Table 6.8 (FCSR fields, p.94-95), Table 6.9
(Cause/Enables/Flags bit order I, U, O, Z, V, p.95) and Table 6.10 (RM encodings, p.95), as read by the authors, and
nothing machine-checks that reading. The rounding core is itself proved correct against the IEEE 754
definition the manual references (see (d)). The specification decodes instruction words with its own
decoder `Manual.Decode`/`Manual.decodeDiagram`, built from the diagrams `Manual.enc`, not with the model's `decode`.
The theorem

```lean
theorem step_eq_manual (s : State) (hs : Refine.Inv s) :
    Manual.InstructionTime Manual.modelImpl Manual.modelOracle decode (Refine.abs s) =
      some (Refine.abs (step s))
```

says that from every state of the invariant `Refine.Inv`, one `step` is exactly one instruction time of the manual,
seen through the projection `Refine.abs`, with the manual's UNDEFINED/UNPREDICTABLE choices resolved as the model
pins them (`Manual.modelOracle`) and the manual's implementation constants as the model's (`Manual.modelImpl`). It
covers every path: interrupt, `wait` standby, the forbidden slot of a compact branch, fetch errors,
undecodable words, **all 203 instructions** (one `Refine.<ctor>_refines` each, collected by `allInstrRefines`), the
delay slot's `I+1` effects and the timer; `resetState_refines_manual` and `resetException_refines_manual` cover Reset.
With it, on the trusted surface: `step_refines_manual` (`step` is a `Manual.Step`, a behaviour the manual allows for
*some* valid resolution of its choices), `modelOracle_valid` (the model's choices are valid), `run_refines_manual`
(`n` steps), `step_unique_of_choiceFree` and `manual_step_deterministic` (where the manual makes no choice,
`step` is the only behaviour it allows), all four stated with the spec's own decoder `Manual.decodeDiagram` (no hypothesis
about the model's `decode`), `decoderSound_decode` (the model's `decode` is sound for the manual's diagrams),
`decoderSound_decodeDiagram` and `decode_diagram_sound`/`decode_diagram_complete` (the spec's decoder accepts exactly the
diagram words), the agreement of the model's `decode` with it (`decode_agrees_manual`: where `decode` accepts, the spec's
decoder gives the same instruction; `decode_none_manual`: where `decode` rejects a diagram word, the Operation reaches
an oracle choice, i.e. EXT/INS out of range), and the invariant's establishment and preservation (`inv_resetState`, `inv_hostedStart`, `inv_load`,
`step_preserves_inv`). So a mistake in `Step.lean` survives only if the same mistake is in the independent
transcription, or in what is trusted below. Limits, stated plainly:
- `Manual.ChoiceFree` decides exactly where the manual leaves a choice that can change the result: `false` at an
  interrupt and at every exception other than Coprocessor Unusable (`Cause.CE` "is loaded, but not
  defined"), at a CTI in a delay slot, at a word with an UNPREDICTABLE field whose coprocessor is
  usable, and where the Operation reaches an oracle choice (`Manual.ConsultsOracle`: a load or store
  while `LLbit = 1`, `DIV`/`MOD`/`DIVU`/`MODU` by zero into `rd ≠ 0`, a 32-bit result stored into a 64-bit FPR
  (the upper half is UNPREDICTABLE, pinned to unchanged), a quiet NaN operand of `CVT.D.S`, the UNPREDICTABLE
  arms of `CTC1`/`EXT`/`INS`, a link register `31` in the compact-branch-and-link forms, `JALR rs = rd`,
  an `EBase` write with `BEV = 0`). Soundness (`ChoiceFree` ⇒ every
  valid oracle gives the same instruction time) is proved for all 203 instructions
  (`Refine/ChoicePoints.lean`, `manual_step_deterministic`). Exactness (`ChoiceFree modelImpl dec a = false` ⇒
  two valid oracles give different instruction times) is proved for every case and every row
  (`choiceFree_exact`, on the trusted surface; `Refine/ChoiceExact.lean`, the rows in
  `Refine/ChoiceRows*.lean`), so `ChoiceFree modelImpl dec a = true` holds exactly where the manual's
  instruction time is determined (`Refine.choiceFree_iff`). Exactness is stated for the
  model's implementation constants `modelImpl` (for another `Impl` a `RECIP`/`RSQRT` approximation could hide
  the value read from an odd register); soundness holds for every `Impl`.
- `Manual.Oracle.Valid` formalizes the three restrictions on UNPREDICTABLE operations of MD00086 Vol II-A
  Rev 6.06 §1.2.1 (p.3-4): no dependence on the state inaccessible in the current mode (non-interference,
  `NIValue`/`NIOutcome`), no change to that state (`UnpredictableLimits`), no entry into the lower power
  mode (a one-step reading of "must not halt or hang"); the one restriction on UNDEFINED operations
  (§1.2.2, p.4); and quiet-NaN results for the QNaN choices of `CVT` (MD00082 §6.3.1.5, p.82). Not
  formalized: "when possible, this QNaN result is one of the operand QNaN values" (p.82), and
  `causeCE`/`storeClearsLL`/`loadClearsLL`, which the manual leaves open without these restrictions.
- `Manual.Impl.Valid` (`modelImpl_valid`, `Manual/Accuracy.lean`) formalizes the accuracy the pages require of
  `RECIP.fmt` (p.336) and `RSQRT.fmt` (p.343): `RECIP` within 1 ULP of the IEEE-mandated representation (order-key
  distance to the core's `1.0 / fs`) and within 1 ULP of the exact `1/fs` (`Impl.RecipExact`), `RSQRT` within 2 ULP
  of the exact `1/√fs` (`Impl.RsqrtAccurate`, stated by squares since `1/√fs` need not be rational). The ULP is the
  one of the exact result's binade (`Manual.ULP`, the denormalized unit below `2^E_min`). Restrictions, stated
  plainly: the exact-result bounds assume no flushing (FCSR.FS = 0; with FS = 1 a tiny result may become zero, which
  no ULP bound survives) and, for `RECIP`, an exact `1/fs` at most the largest finite number (beyond it the
  IEEE-mandated representation itself overflows); they constrain finite results only. `Impl.Valid` also
  contains `Impl.RecipFlags` (`RecipFlagsOK`): for every environment and operand, a quiet NaN signals nothing, a
  signaling NaN signals Invalid Operation and not Division by Zero, a zero signals Division by Zero and not Invalid,
  and any other (non-NaN, nonzero) operand does not signal Division by Zero and signals Invalid exactly for `RSQRT` of a
  negative operand (that last clause is not required of a subnormal operand when FS = 1, which may be flushed). Left free: Overflow, Underflow, Inexact (they belong
  to the approximate result) and the QNaN returned for a NaN operand. For the model (`RECIP` =
  `DIV.fmt` of 1.0, `RSQRT` = `SQRT.fmt` then `DIV.fmt`) they are proved from the correctness of the core
  (`Semantics/FpOpsCorrectRecip.lean`, `FpOpsCorrectRsqrt.lean`, in every rounding mode).
- The environment layer (`Env.lean`: loader, hosted services, stopping conventions) is outside `step` and outside
  the theorem; `inv_load` only says the loader's start state satisfies the invariant.

**(c) The per-instruction `_spec_raw` theorems restate the implementation.** There is one for each of the 203
constructors (`python3 scripts/trace.py` reports 748 spec theorems in all of `Semantics/Specs`, none with `sorry`). Almost all are proved by unfolding `step` and closing with `rfl`
(`step_spec`/`fp_step_spec`/`cp0_step_spec` in `Semantics/Specs/Tactics.lean`); a few have explicit
proofs (`break_spec_raw`, `syscall_spec_raw`; `ext_spec_raw` and `ins_spec_raw` are derived from `ext_spec_fields`/`ins_spec_fields` and the
`decode` field ranges of `decode_wellFormed`; `sll`/`srl`/`sra`/`rotr` rewrite `shamt` to `shamt % 32` first), and each states what `step` computes for that
instruction in terms of the model's own helper functions (`readReg`, `writeReg`, `signExt16`, ...; the `...Spec`
names in `Defs.lean` are abbreviations for the real definitions, not independent copies). Each has the form
`step s = timerTick (…)`: `step` is the instruction (`execute`) followed by the timer (`timerTick`, which only
advances `Count` and sets `Cause.TI`), so the instruction's own effect is the argument of `timerTick`. Because
interrupts exist each of them assumes `hexec : executesInstr s = true` — no interrupt is taken in this
step and the processor is not in standby — because otherwise the step is the Interrupt exception or a standby
step instead (`Specs/Interrupt.lean`); that hypothesis is forced by the model. They pin the behaviour
against regression and make each instruction's semantics readable in isolation. **They are not independent of the
implementation**: a mistake in `Step.lean` that is also a mistake in the reader's understanding of the manual
survives them. The evidence that the semantics matches the architecture is the refinement theorem in (b′), the manual
review recorded in `docs/AUDIT.md` and `SPEC-NOTES.md`, and the differential tests in (e).

The results that are genuinely global, or independent of how an individual instruction is written:

| Result | Where | In the trusted surface |
|---|---|---|
| `step` refines the independent manual transcription (every path, all 203 instructions); `run` likewise; the model's choices are valid; uniqueness at choice-free states; an interrupt is a real choice; `ChoiceFree` is exact (every state it rejects has two valid oracles that differ); Reset; the invariant | `Refine/Step.lean`, `Refine/Determinism.lean`, `Refine/ChoicePoints.lean`, `Refine/ChoiceExact.lean`, `Refine/Decode.lean`, `Manual/Choices.lean`, `Refine/ImplValid.lean` | `step_eq_manual`, `step_refines_manual`, `run_refines_manual`, `step_unique_of_choiceFree`, `modelOracle_valid`, `manual_step_deterministic`, `interrupt_choice_exists`, `choiceFree_exact`, `modelImpl_valid`, `decoderSound_decode`, `resetException_refines_manual`, `resetState_refines_manual`, `step_preserves_inv`, `inv_resetState`, `inv_hostedStart`, `inv_load` |
| the IEEE rounding core is correct: `roundCore` delivers the correctly rounded value (each mode, ties to even), overflow and its Table 6.14 result, the sign, inexact, tininess after rounding; flush to zero; `ADD`/`SUB`/`MUL`/`DIV`/`SQRT` (`.S`, `.D`) are correctly rounded; `Format.value` (Table 6.2) is the core's `toExact` | `FpOpsSpec.lean` (definitions), `FpOpsCorrect*.lean` | `value_eq_toExact`, `roundCore_correct_binary32`/`_binary64`, `roundSpec_representable`, `roundCore_flush_tiny`/`_normal`, `f32Add_correct` … `f32Sqrt_correct`, `f64Add_correct` … `f64Sqrt_correct` |
| every FP operation `step` uses meets a reference written from the manual on **all** operands and every FCSR environment: special operands and the NaN rule, ∞ arithmetic, invalid operations, division by zero, signed zeros, flush to zero (`ADD`/`SUB`/`MUL`/`DIV`/`SQRT`), the conversions (`CVT.S.D`/`CVT.D.S`, the word and longword conversions to and from `.S`/`.D`, and `CVT`/`ROUND`/`TRUNC`/`CEIL`/`FLOOR` to `.W`/`.L` correctly rounded to an integer), `C.cond.fmt`-style comparison tables (`condTable`) and the Release 6 `CMP.cond.fmt` (`cmpTable`), `ABS`/`NEG` (with `ABS2008 = 1`), the FCSR update (Cause/trap/Flags, §6.7.1 and CheckFPException), and the Release 6 `MADDF`/`MSUBF` (fused, `FmaSpec`), `MIN`/`MAX`/`MINA`/`MAXA` (`MinMaxSpec`), `CLASS` (`ClassSpec`) and `RINT` (`RintSpec`) | `FpOpsSpec.lean` (definitions), `FpOpsCorrect*.lean` | `f32Add_spec` … `f64Sqrt_spec`, `f64ToF32_spec`, `f32ToF64_spec`, `w32ToF32_spec`, `w32ToF64_spec`, `f32ToW32_spec`, `f64ToW32_spec`, `f32ToW64_spec`, `f64ToW64_spec`, `w64ToF32_spec`, `w64ToF64_spec`, `condTable_formula`, `f32Compare_spec`, `f64Compare_spec`, `cmpTable_formula`, `f32Cmp_spec`, `f64Cmp_spec`, `f32Abs_spec` … `f64Neg_spec`, `fpUpdate_spec`, `fcsrSpec_unique`, `f32Fma_spec`, `f64Fma_spec`, `f32MinMax_spec`, `f64MinMax_spec`, `f32Class_spec`, `f64Class_spec`, `f32Rint_spec`, `f64Rint_spec`, `newQNaN_binary32`/`_binary64`, `nanResult_first`, `nanResult_first_snan` |
| `decode (encode i) = some i` for every constructor, under `WellFormed` | `Specs/DecodeSpec.lean` | `decode_encode` |
| `$zero` is unchanged by every `step`, every `run` and every hosted run; a write to `$zero` is never observable | `Specs/Invariants.lean`, `Specs/Hosted.lean` | `step_preserves_zero_register`, `run_preserves_zero_register`, `run_initialState_zero_register`, `zero_write_not_observable`, `runHosted_preserves_zero_register` |
| register files keep size 32 under `step`; `run` from `initialState` is well-formed | `Specs/RegFileSize.lean` | `step_preserves_wellFormed`, `run_initialState_wellFormed` |
| exception entry: vector, `EXL`, pending branch abandoned, `LLbit` cleared, `EPC`/`Cause.BD` with and without delay slot, `ExcCode`, `CE` | `Specs/Exception.lean` (the Release 6 `BadInstr`/`BadInstrP` capture too) | `exceptionEntry_always`, `exceptionEntry_badInstr`, `takeInterrupt_badInstr_unchanged`, `_exl0_not_in_delay_slot`, `_exl0_in_delay_slot`, `_exl1`, `_excCode` (`_ce` is in `Exception.lean` only) |
| fetch from memory; fetch/decode failure: misaligned `pc`, undecodable word, Reserved Instruction, Coprocessor Unusable for an undecodable COP0/CACHE word outside Kernel Mode | `Specs/Fetch.lean` | `step_fetches_from_memory`, `step_misaligned_pc`, `step_undecodable`, `step_reserved_instruction`, `step_reserved_cop0_unusable` |
| self-modifying code: a store to the next instruction is what executes next | `Specs/SelfModifying.lean` | `sw_next_instruction_is_fetched`, `store_changes_next_instruction` |
| address translation (Fixed Mapping MMU): each segment's mapping incl. `ERL = 1`; kseg0/kseg1 aliasing; from User Mode a kernel address is an Address Error (fetch, load, store) and changes no memory | `Specs/Mmu.lean` | `fixedMappingPA_kuseg_erl0`, `_kuseg_erl1`, `_kseg0`, `_kseg1`, `_kseg23`, `_kseg0_kseg1_alias`, `translate_user_kernel_address`, `translate_erl1_kuseg_identity`, `step_fetch_user_kernel_address`, `lw_user_kernel_address`, `sw_user_kernel_address`, `kseg1_store_visible_through_kseg0` |
| loader correctness: after loading, a fetch or load of an image address returns the image word | `Specs/Loader.lean` | `load_readMemWord`, `load_step_fetches_image`, `loadAtReset_readMemWord_kseg` |
| general delay-slot theorem; a control transfer in a delay slot raises Reserved Instruction (Release 6 requires it); a control transfer in the forbidden slot of a not-taken compact branch likewise (`EPC` = the branch, `BD = 1`) | `Specs/DelaySlot.lean`, `Specs/CompactBranch.lean` | `delay_slot_commits_target`; `branch_in_delay_slot_reserved_instruction`; `forbidden_slot_cti_reserved`, `beqc_spec_raw` |
| the hosted run is `step` whenever it neither stops nor performs a service; the services | `Specs/Hosted.lean` | `hostStep_eq_step`, `runHosted_agrees_with_run`, `hosted_print_int`, `hosted_exit` |
| Coprocessor Unusable | `Specs/FpuCommon.lean`, `Specs/Cp0.lean` | `fp_coprocessor_unusable`, `cp0_instruction_user_mode_unusable` |
| operating modes: User Mode is `UM = 1`, `EXL = ERL = 0`; CP0 unusable exactly in User Mode (Release 6 has no `Status.CU0`; bit 28 is `RW`); exception entry enters Kernel Mode (UM kept); `eret` returns to User Mode | `Specs/Mode.lean` | `userMode_iff`, `cp0Usable_false_iff`, `exceptionEntry_enters_kernel_mode`, `exception_from_user_mode_enters_kernel_mode`, `eret_to_user_mode` |
| timer: `Count` + 1 per step unless `Cause.DC = 1` or the instruction writes `Count`/`Compare`/`Cause` (proved over every constructor); `Count = Compare` sets `Cause.TI`; a `Compare` write clears it; `Cause` reads `TI` and `IP7`; `rdhwr` values and access rule (Kernel Mode or `CU0`, or the `HWREna` bit; Reserved Instruction otherwise) | `Specs/Timer.lean` | `step_count_advances`, `step_count_stopped`, `step_timer_match_sets_ti`, `step_timerInt`, `mtc0_count_spec`, `mtc0_compare_clears_ti`, `causeValue_timer`, `rdhwr_spec_raw`, `hwrValue_*`, `rdhwr_reserved_unimplemented`, `rdhwr_reserved_not_enabled`, `rdhwr_allowed`, `hwrena_write_masked`, `resetException_timer` |
| interrupts: taken exactly when `IE = 1`, `EXL = ERL = 0` and some `Cause.IP & Status.IM` is set, before the instruction at `pc`; entry (`ExcCode` 0, `EPC`/`BD`), vector `0x180`/`0x200` by `Cause.IV`; software, timer and hardware-line requests; the lines are inputs no step writes; standby after `wait`; `IntCtl`/`SRSCtl` values; `rdpgpr`/`wrpgpr` | `Specs/Interrupt.lean`, `Specs/Cp0.lean` | `step_interrupt`, `interruptTaken_iff`, `no_interrupt_ie0`/`_exl`/`_erl`/`_masked`, `takeInterrupt_not_in_delay_slot`, `takeInterrupt_in_delay_slot`, `interruptVector_iv0`/`_iv1_bev0`/`_iv1_bev1`, `mtc0_cause_requests_software_interrupt`, `timer_requests_interrupt`, `step_hwInt`, `wait_spec_raw`, `step_standby_stays`/`_restarts`/`_interrupt`, `intCtlValue_fields`, `srsCtlValue_fields`, `mfc0_srsctl_spec`, `rdpgpr_spec_raw`, `wrpgpr_spec_raw` |
| Reset exception and reset state; the hosted start state is reset followed by the environment's boot convention (and equals `initialState textBase`) | `Specs/Reset.lean` | `resetException_spec`, `resetState_spec`, `hostedStart_is_reset_then_boot` |
| FP trap: an enabled FP exception takes ExcCode 15 and writes no FP register | `Specs/FpuCommon.lean` | `fpCompletesS_trap` (single-precision finish helper; the double analogue `fpCompletesD_trap` is in `FpuCommon.lean`) |
| FCSR round trip through `ctc1`/`cfc1` (the writable fields; `FCSR.NAN2008`/`ABS2008` read 1) | `Specs/FpuControl.lean` | `fcsr_ctc1_cfc1_roundtrip` |
| Release 6 privileged additions: `eretnc` leaves `LLbit`; `sigrie` raises Reserved Instruction; `cache` is a no-op with no caches; `mfc0` of a register the `cp0Layout` table does not name reads 0 and `mtc0` ignores the write | `Specs/Cp0.lean`, `Specs/Trap.lean` | `eretnc_spec_raw`, `sigrie_spec_raw`, `cache_spec_raw`, `mfc0_unimplemented_reads_zero`, `mtc0_unimplemented_ignored` |
| FP compare: what the result bit means for all operands is kernel-checked (`Semantics/FpCompareFacts.lean`), not a separate statement; the statements are `f32Compare_spec`/`f32Cmp_spec` above | `Semantics/FpCompareFacts.lean` | none of its own |

The delay-slot theorem `delay_slot_commits_target` has a side condition: the instruction at `pc` is not branch-like
(`isBranchLike instr = false`), `s.pc + 4` is not the exception vector, it completes normally outside a delay slot
with `pc + 4`, and then in a delay slot with pending target `t` it yields the same state with `pc := t`.

**(d) Floating point.** The FPU is the Release 6 one: 64-bit FPRs (`Status.FR = 1`), `FIR = 0x00F3_0000`
(`Has2008`, `F64`, `L`, `W`, `D`, `S`), `FCSR.NAN2008 = ABS2008 = 1`. Arithmetic is exact rational arithmetic followed by one rounding (add, subtract, multiply
exactly; divide and square root to `prec + 2` bits with a sticky bit; then `Format.roundCore`), defined on bit
patterns with no host floats in any definition. **The rounding core is proved correct** against the
IEEE 754 definition the manual references, written independently of the core in `Semantics/FpOpsSpec.lean`:
`Format.value` (the value of an encoding, MD00082 Vol I-A Rev 6.01 Table 6.2, p.80-81), `CorrectlyRounded` (the
largest/least/nearest representable value, ties to the even one, Table 6.10, p.95, over an explicit set of
representable values), and `Format.RoundSpec` (overflow per §6.7.2.5 with the Table 6.14 result, p.100-102; inexact
per §6.7.2.6; tininess after rounding per §6.7.2.3, p.101, "The MIPS architecture specifies that tininess be
detected after rounding"). An exact result is a `Cut` (its comparisons with the rationals), so `√x` is stated
exactly. Proved (`Semantics/FpOpsCorrect*.lean`, kernel-checked, no Mathlib): for every nonzero exact value and every
format with at least two exponent and two fraction bits, `roundCore f rm false` meets `RoundSpec`
(`roundCore_correct`; for binary32/64 on the trusted surface), and without overflow its value is correctly rounded to
the format's finite values; an exact zero gives the zero of its sign; with FCSR.FS = 1, a value tiny before rounding
becomes zero, tiny and inexact, any other is rounded as with FS = 0 (`roundCore_flush_*`); `Exact.add`/`Exact.mul`
are exact, `Exact.div`/`Exact.sqrt` (with `isqrt`) agree with the true quotient / root on every grid the rounding uses
(the sticky-bit argument); hence `f32Add` … `f64Sqrt` are correctly rounded for finite operands with a nonzero exact
result (no flushing). **The rest of each FP operation is proved too**, against reference
definitions in `Semantics/FpOpsSpec.lean` (definitions only, each citing MD00082 Vol I-A Rev 6.01 ch.6 read
for Release 6 (`FIR.Has2008 = 1`), or the MD00086 Vol II-A Rev 6.06 instruction page): what an encoding denotes
(`Format.datum`: NaN, ±∞, a finite value with its sign, Table 6.2; with `NAN2008 = 1` a NaN is signaling iff the
fraction's high bit is 0), the new
QNaN of Table 6.3 (`newQNaN`, checked to be `0x7fc00000` / `0x7ff8000000000000`), the NaN rule (`NaNResult`: Invalid
iff an SNaN operand, the result a QNaN that is an operand QNaN when there is one, else the new QNaN, §6.3.1.4-5), the
exceptions a rounding signals (`Signaled`, §6.7.2.3/5/6) and rounding under the whole FCSR including flush to zero
(`RoundEnvSpec`, §6.7.2.4; with `FS = 1` every subnormal input is replaced with zero, `FlushedIn`, Table 6.8 p.93, and
that flush signals Inexact except in comparisons, §6.7.2.4 p.102), and one definition per operation over every operand (`AddSpec`, `MulSpec`, `DivSpec`,
`SqrtSpec`: invalid operations §6.7.2.1, division by zero §6.7.2.2, ∞ arithmetic §6.3.1.3, signed zeros;
`ConvertSpec`, `WidenSpec`, `FromIntSpec`, `ExactSpec`; `ToWordSpec`/`ToLongSpec`: correct rounding to an integer per mode,
with Invalid for NaN/∞/out of range; `CompareSpec` with `condTable` and `CmpSpec` with `cmpTable` (the Release 6
`CMP.cond.fmt`, Table A.17 conditions); `SignOpSpec` for `ABS`/`NEG`: with `ABS2008 = 1` they are non-arithmetic, only
the sign bit changes, no exception; `FmaSpec` for the fused `MADDF`/`MSUBF`; `MinMaxSpec`; `ClassSpec`; `RintSpec`),
and the FCSR update (`FcsrSpec`: Cause, CheckFPException, Flags, §6.7.1). Proved (`FpOpsCorrectSpecial` …
`FpOpsCorrectIEEE`, `FpOpsCorrectFma`, `FpOpsCorrectR6`): `f32Add` … `f64Sqrt`, the format and word/longword conversions, `f32Compare`/`f64Compare`, `f32Cmp`/`f64Cmp`, `f32Abs` … `f64Neg`,
`f32Fma`/`f64Fma`, `f32MinMax`/`f64MinMax`, `f32Class`/`f64Class`, `f32Rint`/`f64Rint` meet their definitions for **every** operand bit pattern and every
FCSR environment (rounding mode, Enables, FS); `fpUpdate` meets `FcsrSpec`, which determines the new FCSR and the
trap uniquely. Where the
manual leaves a choice, a definition either allows every choice (which operand QNaN is returned: the model's is the
first, `nanResult_first`; the QNaN of a format conversion) or fixes the model's
reading, named as a pin (SPEC-NOTES): the signs
of exact zero results, where the manuals are silent and the model follows IEEE 754 (the 1985 standard the MIPS manual names; verified against IEEE Std 754-2019 §6.3 p.50, a licensed, local-only copy). `RECIP`/`RSQRT` are the
implementation-dependent `1/x` and `1/√x` (`DIV`, `SQRT` then `DIV`; their accuracy bounds are in (b′)). Differential `#guard` tests against Lean's `Float32`/`Float`
(`Semantics/Tests/FpOpsTests.lean`) and the QEMU oracle remain.

**(e) Differential evidence.**
- *QEMU* (`qemu-system-mipsel -M malta -cpu mips32r6-generic`, `tests/oracle`, `scripts/oracle.py`): the same machine code at the
  same addresses runs on QEMU and on the model, and registers, FPRs, FCSR, CP0 state, memory, output and
  termination are compared. The last full gate run (`.gate/last-run.json`, step 7) reports **184 tests** (the
  `tests/oracle` programs plus the `tests/asm` programs the harness can run): 164 pass, 20 are **declared deviations where QEMU departs
  from the manual** (the manual wins), 0 known model bugs, 5 skipped (unsupported by the harness); all 203
  constructors are executed by a `tests/oracle` program (`COVERAGE: 203/203`, which the gate requires). The deviations carry their citations in the tests' own
  `# oracle: expect-deviation` directives (`SPEC-NOTES.md` has the table); in groups: `CFC1`/`CTC1` of a register that
  does not exist (QEMU does not raise Reserved Instruction; MD00086 Vol II-A Rev 6.06, CFC1 p.129-130, CTC1 p.149-150);
  misaligned `sc` (SC p.349); `FCSR.FS = 1` flushing (QEMU does not flush inputs and leaves Underflow/Inexact clear;
  MD00082 Vol I-A Rev 6.01 §6.7.2.4, p.102); `MIN`/`MAX`/`MINA`/`MAXA` of a signaling NaN (QEMU quiets the result;
  MD00086 p.263, Table 4.1 p.265); an enabled Underflow trap for an exact tiny result (§6.7.2.3, p.101) and Inexact with an enabled
  Overflow trap (§6.7.2.6, p.102); `BOVC`/`BNVC` with `rs = rt = 0` (QEMU links `$31`; MD00086 p.107); an exception in the delay slot of a
  statically never-taken branch reports `BD = 0` in QEMU (MD00090 Vol III Rev 6.02 §9.36 p.209, §9.38 p.217); `LLAddr` bit 0 (`LLB`; MD00090 Table 9.72, p.270);
  `rdhwr` with an undefined `sel` or of an unimplemented register (MD00086 RDHWR p.333; MD00090 Table 9.40, p.176); and COP2
  with `Status.CU2 = 0` (the model raises Coprocessor Unusable, QEMU Reserved Instruction; MD00090 §6.2.22, p.100).
  Interrupts and `wait` are covered by the `irq_*` programs
  (bare, with their own `.ktext` handlers); a program may use `# oracle: bare` with a handler of its own.
- *LLVM encoding oracle* (`llvm-mc -triple=mipsel-unknown-elf -mcpu=mips32r6`): the assembler's output is compared
  word for word on 687 forms (`tests/oracle/encodings.list`): 648 identical, 39 declared differences (our
  `li`/`la`/`move`/`abs` expansions follow MARS/SPIM; the declarations are `ENC_DECLARED` in `scripts/oracle.py`). A few forms `llvm-mc` 21 cannot
  assemble for `mips32r6` (`wait`, `rdpgpr`/`wrpgpr`, some `cmp.<cond>` predicates) are compared with words built by hand from the manual's diagrams (`ENC_MANUAL`).
- *MARS 4.5* (`tests/corpus`, 29 programs, `DiffHarness`): MARS cannot run Release 6, so it is a differential oracle only
  for corpus programs that are valid Release 6; the model and the real simulator agree on every one of the 29. MARS has no FCSR/FP exceptions
  and lacks several instructions, so the corpus uses patterns both agree on (`SPEC-NOTES.md`). Where MARS and the architecture
  disagree the architecture wins and the divergence is recorded.
- *Equivalence corpus* (`tests/equiv`, `EquivHarness`, 7 cases) and, in the same harness, the manual-spec check:
  `Manual.InstructionTime` against `step` through `Refine.abs` on every state of every corpus and oracle program.

**(f) What is trusted.** Lean and its kernel; the three standard axioms; the manuals *as read by the authors*
(nothing machine-checks the reading); the statements in `Statements.lean` and the definitions they mention (the
model itself). For the refinement result (b′) that is precisely: the `Semantics/Manual/*` definitions (the
transcription; each Operation cites its page), the choices `Manual.modelImpl`/`Manual.modelOracle` (each a
documented pin in `SPEC-NOTES.md`, and `modelOracle_valid` checks them against the manual's limits), `Refine.abs` (a
field-by-field projection) and `Refine.Inv` (`Good`, `FcsrReservedZero`, `StatusImplemented`; established at reset and load and preserved by `step`, so not vacuous; `cfc1_refines`/`ctc1_refines` need `FcsrReservedZero` from it),
and the items of `FpOps.lean` both sides share (the allow-list in (b′): the IEEE rounding core `Mips.Fp.f32Add` …, wrapped as `Manual.IEEE.*`, the formats, NaN classifiers and default NaNs, and the FCSR helpers `Env`, `Flags`, `RoundingMode.ofBits`, `Flags.ofBits`; the two decoders are correct by Tables 6.8-6.10 but shared, so a misreading of those tables would be on both sides). The model's `decode` is not trusted for the refinement: the spec decodes with `Manual.decodeDiagram`, and `decode_agrees_manual`/`decode_none_manual` relate the two.
The rounding core and every FP operation `step` uses are **proved** against reference definitions (see (d)) for every operand,
so what remains trusted of floating point is **the definitions in `Semantics/FpOpsSpec.lean`**
(read them in full: they are the reading of the manual) **and the listed pins** (SPEC-NOTES: the first-QNaN choice, the QNaN of a format
conversion, the signs of exact zeros, the Inexact signaled by an input flush), plus the implementation-dependent `RECIP`/`RSQRT` (bounded in (b′)); not their proofs (`Semantics/Refine/*`,
kernel-replayed). Also trusted: the assembler, which is **tested but not proved** (`Semantics/Tests/AsmTests.lean`, the LLVM oracle,
the MARS corpus); the harnesses, `scripts/oracle.py` and the QEMU boot stub; and `docs/spec`, which is
human-written. Manual misprints the model had to read (for example the `B<cond>C` offset, the `CFC1` condition, the `MADDF` operand names, the
`MIN`/`MAX` function-field order) are recorded as readings in `SPEC-NOTES.md`.

**(g) UNPREDICTABLE pins and known divergences.** Every place where the manual leaves behaviour open and the model
picks one, and every deliberate difference from MARS or QEMU, is in `docs/spec/SPEC-NOTES.md`. `docs/spec/R6-COVERAGE.md` classifies
every page of the instruction set volume.

## Instruction coverage

Generated by `python3 scripts/trace.py --readme` from the sources (the same data as `docs/TRACE.md`); the gate
fails if this block is stale (`trace.py --check-readme`). The per-instruction table, with links to the decode and
encode clauses, the step arm, the spec theorems, the manual page and the tests, is `docs/TRACE.md`. The last gate run
reports 203 constructors, each with a decode and an encode clause, a step arm, a primary spec theorem, a refinement theorem
`Refine.<ctor>_refines` and a QEMU-oracle test; 83 have a MARS corpus test.

The per-family coverage table is generated into the code branch's `README.md`; the per-instruction matrix is `TRACE.md`.
All 263 instruction pages of MD00086 Vol II-A Rev 6.06 are classified in `docs/spec/R6-COVERAGE.md`: 137 implemented (the 203
constructors), 77 removed in Release 6, 36 of an optional module or feature that is absent, 6 TLB instructions (Reserved
Instruction under the Fixed Mapping MMU), 7 assembler idioms, **0 open gaps**.

## What is not modeled

Each item is a choice the profile makes, not a gap; the manual citations and the pins are in `docs/spec/MIPS-COVERAGE-GAPS.md`
and `docs/spec/SPEC-NOTES.md`.

- **Other releases.** Release 5, 3, 2 and 1 will be added later, backwards, as profiles. The Release 2 model is at tag `mips32r2-final`.
- **Big-endian** (`Config5.DEC = 0`; the byte order is one profile constant).
- **Optional modules**: MSA, microMIPS, VZ, MT, DSP, EVA, XPA, MCU, CRC, GINV, VP (`DVP`/`EVP` are NOPs with `Config5.VP = 0`), EJTAG
  (`SDBBP`/`DERET` do not decode). Their configuration bits read 0.
- **TLB.** The MMU is the Fixed Mapping MMU (`Config.MT = 3`, kseg0/kseg1 aliasing, the User-Mode Address Errors); the TLB registers read 0 and
  ignore writes, `TLBP`/`TLBR`/`TLBWI`/`TLBWR`/`TLBINV`/`TLBINVF` raise Reserved Instruction (MD00090 Vol III Rev 6.02 A.1.3, p.317). No Supervisor Mode.
- **Caches**: none; `CACHE` and the prefetches are no-ops (MD00086 Vol II-A Rev 6.06 CACHE, p.119).
- **Coprocessor 2** does not exist: its encodings raise Coprocessor Unusable with `CE = 2` (QEMU raises Reserved Instruction: a declared deviation).
- **Interrupt modes**: vectored (VI) and external-controller (EIC) modes (interrupt compatibility mode is modeled, with `IntCtl`
  and `SRSCtl` as constants: `IPTI = 7`, `VS = 0`, `HSS = 0`); shadow register sets beyond the normal GPRs; `SRSMap`.
- **CP0 registers outside the `cp0Layout` table** (watch, performance counters, EJTAG, cache tags, TLB registers, ...): they read 0 and
  ignore writes. Implemented as constants: `PRId`, `Config`..`Config5` (`Config2` = `0x8000_0000`, `Config3` = `0x8C00_3000`, `Config4` = `0x80FC_0000`,
  `Config5` = `0x0000_2010` with `SBRI` writable), `IntCtl`, `SRSCtl`.
- **Hardware interrupt lines and the platform** are the environment (`hwInt`), not the architecture.

## Building and the gate

One command runs everything: `scripts/gate.sh` (about 8 minutes; `--quick` runs steps 1, 8, 9, 10 only and is not
green). The steps (`scripts/README.md`): 1 forbidden constructs and manual-spec independence; 2 `lake build` of all targets with zero project
warnings; 3 `lake check` (kernel replay, axioms); 4 `lake comparator`; 5 DiffHarness vs MARS (the N corpus programs valid in Release 6);
6 EquivHarness (including `Manual.InstructionTime` against `step`); 7 oracle (`oracle.py selftest`, the QEMU `mips32r6-generic` behaviour suite with
the 203/203 constructor-coverage check, and the LLVM encoding comparison); 8 traceability (`trace.py --check`, the README table current);
9 manuals tool selftest (SKIP when the manual texts are absent; a SKIP in a full run makes the gate red); 10 hygiene. Only a fully green run writes the stamp
that `scripts/gate-commit.sh` requires. `docs/TRACE.md` is checked on this branch by `docs/check.sh`, not by the gate.

```sh
lake exe cache get      # fetch the mathlib build cache (Mathlib is a declared dependency; no module imports it)
scripts/gate.sh         # the full gate
lake build MipsRun && lake exe MipsRun prog.asm      # assemble and run one program, JSON out
```

Prerequisites: `elan` (the toolchain is pinned in `lean-toolchain`: `leanprover/lean4:v4.35.0`); a JRE (step 5 runs
`vendor/mars/Mars4_5.jar`); `qemu-system-mipsel` and LLVM (`llvm-mc`, `ld.lld`, `llvm-objdump`, `llvm-objcopy`;
point `ORACLE_LLVM_DIR` at them if they are not in `/usr/lib/llvm-21/bin` or on `PATH`) for step 7, which fails,
never skips, without them; Python 3 (standard library only). Individual targets: `lake build Semantics Checked
DiffHarness EquivHarness MipsRun`, `lake check`, `lake comparator`.

The manuals are not in the repository: they are copyrighted by MIPS Technologies, Inc., and their front matter
prohibits copying without written permission, so the PDFs and the extracted texts are `.gitignore`d. Fetch them
with `manuals/fetch.sh` (needs `curl` and `pdftotext`; it verifies `SHA256SUMS`) and look things up
with `manuals/mipsdoc.py` (`AGENTS.md` there). Without them step 9 is a SKIP and `docs/TRACE.md`
cannot be regenerated with its manual column.

## Repository layout

```
lakefile.toml, lean-toolchain, lake-manifest.json   Lean project files (targets: Semantics, Checked, DiffHarness, EquivHarness, MipsRun)
Checked.lean, Semantics.lean   library roots; Checked is what `lake check` replays
comparator.json                the 221 trusted theorem names, challenge and solution modules
Semantics/Word, Types, State, Instruction, FpOps, Step .lean   the model (definitions only); Types holds Release/Profile and State,
                               Instruction the decoder tables (`decodeFor`), Step the cycle (`step`, `execBody`, reset)
Semantics/Exec/               what each instruction does, one file and one table per family: Base (vocabulary: delay-slot exit, exception entry,
                               FP finish, CP0 values, timer, interrupts), IntArith, Shift, BitOps, Immediate, Memory, Atomic, Branch
                               (incl. compact branches, PC-relative), Jump, Trap, Syscall, System, Cp0 (the `cp0Layout` table), FpuMove,
                               FpuControl, FpuMemory, FpuArith, FpuConvert, FpuR6
Semantics/Asm.lean, Asm/      the assembler: Syntax, Expr, Float, Operands (combinators), one encoder table per family
                               (Int, Memory, Branch, System, Fpu), Pseudo (idioms), Table (union, removed mnemonics), Layout (passes)
Semantics/Env.lean             the environment (loader, hosted services, stopping conventions): not the architecture
Semantics/FpOpsFacts.lean, FpCompareFacts.lean   kernel-checked facts about FpOps
Semantics/FpOpsSpec.lean       the IEEE 754 / FPU reference the FP operations are proved against (definitions only)
Semantics/FpOpsCorrect*.lean   the proof that the rounding core and every FP operation (incl. the Release 6 ones: Fma, R6) meet it
Semantics/Specs/               the specification: Defs, WellFormed (vocabulary); Lemmas, Tactics, Fixtures (plumbing);
                               DecodeSpec, Exception, Fetch, SelfModifying, DelaySlot, Invariants, RegFileSize,
                               Mode, Reset, Mmu, Loader, Timer, Interrupt, Hosted (global theorems);
                               one file per instruction family (Arith, Shift, BitOps, Immediate, Memory, Atomic, Branch, CompactBranch,
                               Jump, PcRel, Trap, Syscall, Cp0, Fpu*, ...); StepSpec (index)
Semantics/Manual/              the independent transcription of the manuals (Arch, Pseudocode, CP0, Memory, FPU,
                               Exceptions, Interrupts, Timer, Reset, Encoding, Decode, Ops/<Family>, Operation, Cycle, Relation, Choices, Accuracy)
Semantics/Refine/              the refinement of Manual by step: Defs (abs, Inv), bridges, one file per family
                               (<ctor>_refines), Cycle, Decode*, Invariant, Instr (allInstrRefines), Step, Determinism, Choice*, ImplValid
Semantics/Statements.lean      the trusted surface (221 statements, proofs elided)
Semantics/StatementsProofs.lean  the same statements, proved from Specs and Refine
Semantics/Tests/               #guard / example tests for each definition file
DiffHarness.lean, EquivHarness.lean, MipsRun.lean   executables
tests/corpus/  tests/equiv/  tests/asm/   programs for DiffHarness (MARS) / EquivHarness (base-variant pairs; programs with checked output)
tests/oracle/                  QEMU oracle programs (*.asm with `# oracle:` directives), encodings.list, harness/boot.s, gen/gen_tests.py
scripts/                       gate.sh, gate-commit.sh, oracle.py, trace.py, manual_independence.py, manual_deps.py, README.md
docs/spec/                     INSTRUCTION-REF.md, SPEC-NOTES.md, R6-COVERAGE.md, MIPS-COVERAGE-GAPS.md, COMPLIANCE.md
manuals/                       lookup tool (mipsdoc.py, fetch.sh); PDFs and texts not committed
docs/PROOF-NOTES.md            reading order, the comparator arrangement, proof history
docs/MANUAL-SPEC.md            the design of the independent manual specification
docs/TRACE.md                  generated instruction traceability matrix
docs/AUDIT.md                  record of what was checked against the manuals
docs/DESIGN.md                 module map, State, the step pipeline, decoder tables, Exec tables, delay slots, exceptions, FP model
vendor/mars/                   the MARS 4.5 jar, used by DiffHarness only
```

## How to review this project

1. `docs/PROOF-NOTES.md`: reading order and the comparator arrangement.
2. The model: `Semantics/Word.lean` (38), `Types.lean` (490), `State.lean` (327), `Instruction.lean` (1458), `FpOps.lean` (1393),
   `Step.lean` (327) and the family tables `Semantics/Exec/*.lean` (about 1900 lines, `Exec/Base.lean` 653 of them). `docs/DESIGN.md` is the map.
   The environment around it (not the architecture): `Env.lean` (276).
3. The statements: `Semantics/Specs/Defs.lean` (116), `WellFormed.lean` (223), then `Semantics/Statements.lean` (2432).
   For the floating-point statements: `Semantics/FpOpsSpec.lean` (887 lines; the IEEE and FPU reference, read it in full).
   For the refinement statements (their section): `docs/MANUAL-SPEC.md`, `Semantics/Manual/Cycle.lean` and
   `Relation.lean` (the instruction time and the relation), `Manual/Ops/*` (one Operation per manual page),
   `Manual/Choices.lean` (the pins), `Semantics/Refine/Defs.lean` (`abs`, `Inv`).
4. For any instruction family: `Semantics/Specs/<Family>.lean`; the index and table is `Specs/StepSpec.lean`.
5. `docs/TRACE.md` (generated): one row per instruction, from manual page to tests.
6. `docs/spec/SPEC-NOTES.md`: every pin and divergence; `docs/spec/R6-COVERAGE.md`, `MIPS-COVERAGE-GAPS.md`: what is covered and what is left out;
   `docs/AUDIT.md`: what was checked against the manuals.
7. Not required for trust: `Specs/Lemmas.lean`, the proof-device parts of `DelaySlot`, `Invariants`, `RegFileSize`,
   `FpOpsFacts`, `FpCompareFacts` and `Tactics`; the kernel replays them.

## MipsRun

`lake exe MipsRun [--max-steps N] [--bare] [--reset] [--coverage] [prog.asm]` assembles a program (file or stdin; `--coverage` adds the field `executed`, the constructor names the run executed, for the oracle's coverage check), loads it (`Env.load`)
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
with `pc`, or `limit`), `initial` (the loader's start state, before the image is written) and `final` (each: `pc`, `gpr` (there is no `hi`/`lo`: Release 6 has no `HI`/`LO`),
`fpr64` as the raw 64-bit registers (`fpr` the low 32 bits of each), `fcsr`, `fp_cond_flag` (= FCSR bit 23, kept for compatibility), `ll_bit`, `ll_addr`,
`pending_branch`, `standby`, `hw_int`, `fir`, `fcr`, `kernel_mode`, `interrupt_requests`, `cp0` with `status`, `cause`, `epc`, `badvaddr`, `errorepc`, `ebase`, `count`, `compare`, `hwrena`, `intctl`, `srsctl`, `prid`, `config`, `config1`, and more; the field list is in `scripts/README.md`, "JSON render"), `fcsr_mask`, `image`
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
