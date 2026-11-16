# The independent manual specification (`Semantics/Manual/`) and the refinement of `step`

This is the design document of Wave 7. Part I records what was built and decided (kept current);
Part II is the guide for the 7B transcription agents; Part III is the approved plan as it was handed
over (its §5.2 recommendation was overridden by the owner, see I.2).

# Part I. As built (sub-wave 7A)

## I.1 Files

| File | Contents |
|---|---|
| `Manual/Arch.lean` | `Arch` (the manual's state, functions for register files and memory), `Delay` (an `I+1:` effect), `update` |
| `Manual/Choices.lean` | `Exception`, `Outcome`, `Impl`, `Impl.WF` (7R), `AbsNegNaN` (7R), `Oracle`, `IsPAUSE`, `modelImpl`, `modelOracle`, `modelImpl_WF` (7R) |
| `Manual/Pseudocode.lean` | `Ctx`, `Frame`, `Result`, `Pseudo` (+ `Monad`), `Pseudo.run/get/modify/impl/oracle`, `SignalException`, `I1`, `resolve`, `setPC`, `PC`, `readGPR`/`GPR`/`writeGPR`/`setGPR`, `HI`/`LO`/`setHI`/`setLO`, `reg`, `bits`, `bit`, `low`, `sign_extend`, `zero_extend`, `imm16`, `memory_address` |
| `Manual/CP0.lean` | Status/Cause field reads by bit (`StatusIE` … `StatusCU1`, `CauseIV`, `CauseDC`), `StatusWritable`, `CauseWritable`, `HWREnaWritable`, `KernelMode`, `UserMode`, `CP0Usable`, `IntCtlIPTI`, `CauseRead`, `EBaseRead`, `ConfigRead`, `IsCoprocessorRegisterImplemented`, `CPRWrite`, `CPRRead` |
| `Manual/Memory.lean` | `IorD`, `LorS`, `BYTE`/`HALFWORD`/`TRIPLEBYTE`/`WORD`, `BigEndianMem`, `ReverseEndian`, `BigEndianCPU`, `FixedMapping`, `CCAOf`, `AddressTranslation`, `MemElemAt`, `LoadMemory`, `laneByte`, `updMem`, `StoreMemory`, `InstructionFetch` |
| `Manual/FPU.lean` | `FCSR_RM/Enables/FS`, `IEEE.env`, `IEEE.addS` (the shared rounding core, proved correct since wave 10, I.8), `Fmt`, `ValueFPR32`, `StoreFPR32`, `CheckFPException`, `FPResult` |
| `Manual/Exceptions.lean` | `ExcCode`, `FaultingCoprocessorNumber`, `AdditionalState`, `vectorOffset`, `vectorBase`, `GeneralExceptionProcessing` |
| `Manual/Interrupts.lean` | `InterruptRequests`, `InterruptsEnabled`, `InterruptTaken`, `LowPowerTime` |
| `Manual/Timer.lean` | `TimerTick` |
| `Manual/Reset.lean` | `ResetException` |
| `Manual/Encoding.lean` | `fld`, `rFormat`, `iFormat`, `trapFormat`, `codeFormat`, `enc` (every constructor since 7B), `opcode`, `InCop0Space`, `InCop1Space`, `InCop2Space`, `fldOf`, `UnpredictableEncoding` (7R) |
| `Manual/Ops/*.lean` | the pilot Operations `Ops.ADD`, `Ops.LW`, `Ops.SW`, `Ops.LWL`, `Ops.BEQ`, `Ops.BEQL`, `Ops.ADD_S`, `Ops.MTC0` |
| `Manual/Operation.lean` | `Operation : Instruction → Option (Pseudo Unit)` (`none` = not transcribed yet) |
| `Manual/Cycle.lean` | `IsCTI`, `DecoderSound`, `Complete`, `Execute` (+ `Execute.runOperation`), `Undecodable`, `Unpredictable` (7R), `FetchExecute`, `InstructionTime` |
| `Refine/Defs.lean` (7D part 2) | definitions only, the refinement vocabulary of the trusted statements: `memOf`, `abs`, `Good`, `FcsrReservedZero`, `StatusImplemented`, `Inv` |
| `Refine/Abs.lean` | `abs_*` projections, `readGPR_abs`, `regIdx_eq_reg`, `abs_writeReg`, `abs_writeFpReg` |
| `Refine/Bridge.lean` | constants (`statusWritable_eq` …), single-bit reads, `abs_advance`, `complete_plain`, `cause_update`, `vector_eq`, `gep_eq`, `gep_take`, `Simple`, `modelCtx`, format lemmas, `branch_offset`, `offset16`, `cu1_abs`, `kernel_abs`, `cp0usable_abs`, `execute_run`, `execute_cti_slot`, `execute_cti_run`, ADD's 33-bit lemmas (`add33_low`, `add_ovf`) |
| `Refine/Fetch.lean` | `erl_abs`, `userMode_abs`, `denied_eq`, `fixedMapping_eq`, `addrTrans_run`, `word_of_bytes`, `base_of_aligned`, `fixedMappingPA_aligned`, `memElem_eq`, `misaligned_eq`, `readMemWord_eq`, `memOf_insert`, `laneByte_eq` |
| `Refine/{IntArith,Memory,Unaligned,Branch,BranchLikely,FpuArith,Cp0}.lean` | `add_refines`, `lw_refines`, `sw_refines`, `lwl_refines`, `beq_refines`, `beql_refines`, `addS_refines`, `mtc0_refines` |
| `Refine/BridgeIntAlu.lean` (7C S1) | `execute_plain`, `execInstr_body`, `refine_ok`/`refine_gpr`/`refine_exc`, encoding-space lemmas, `alu_space`/`alu_run`, value lemmas (shifts, multiply/divide, `manualCount`, `wsbh_eq`) |
| `Refine/{IntArith,Shift,MulDiv,BitOps,Immediate}.lean` (7C S1, merge) | the integer ALU `_refines`, including `ext_refines`/`ins_refines` (merge; `lowBitsMask_getLsbD`, `ext_eq`, `ins_eq`) |
| `Refine/BridgeControl.lean` (7C S3) | signed compares with zero, `jump_target`, `branch_refine` macro, COP0 opcode lemmas, `execute_cop0`, `execInstr_cop0`, `complete_writeReg`, `cprRead_*` |
| `Refine/{Branch,BranchLikely,Jump,Cp0,System}.lean` (7C S3, merge) | branches, branch-likely, `j`/`jal`/`jr`/`jalr`/`jrHb`/`jalrHb`, `mfc0`/`mtc0`/`di`/`ei`/`rdpgpr`/`wrpgpr`, `wait`/`rdhwr`/`eret` |
| `Refine/BridgeMem.lean` (7C S2) | `writeReg_pb`, `complete_nop`, `complete_writeReg_eq`, trap/`SYSCALL` encoding-space lemmas, the common end of a conditional trap |
| `Refine/{Memory,Atomic,Unaligned,Trap,Syscall}.lean` (7C S2, merged 7D part 2) | loads/stores, `sync`/`synci`/`pref`, `ll`/`sc`, `lwl`/`lwr`/`swl`/`swr`, the twelve traps, `break`, `syscall` |
| `Refine/BridgeFpu.lean` (7C S4a) | FPR/FCSR bridges, `FPResult` against `fpFinishS/D`, `ValueFPR64`/`StoreFPR64` under `modelOracle` |
| `Refine/{FpuArith,FpuConvert,FpuCompare}.lean` (7C S4a, merged 7D part 2) | FPU arithmetic (incl. the multiply-add family), conversions, `C.cond.fmt` |
| `Refine/BridgeFpuMove.lean` (7C S4b) | `cop1_execute`, `cop1_cti_execute`, `fpcc_run`, doubleword accesses, `CFC1`/`CTC1` bridges, `fcsrReservedZero_extract` |
| `Refine/{FpuMemory,FpuMove,FpuControl,FpuBranch}.lean` (7C S4b, merged 7D part 2) | FP loads/stores, moves and conditional moves, `cfc1`/`ctc1`, `bc1f`/`bc1t`/`bc1fl`/`bc1tl` |

`scripts/manual_independence.py` (gate step 1) enforces the independence rule (§6.3 of the plan):
`Semantics/Manual/*` imports only `Word`, `Types`, `Instruction`, `FpOps` and other `Manual` modules,
and names no definition of `Step.lean`/`State.lean`/`Types.lean` (except `W32`/`VAddr`/`PAddr`), no
`decode`/`encode`, no `*Mask`, no FCSR helper of `FpOps.lean` (`fpUpdate`, `envOf`, …).
Since wave 12b gate step 1 also runs `scripts/manual_deps.py`, which checks the same rule on the elaborated
environment (`scripts/ManualIndependence.lean`): every constant reached transitively from a `Manual.*` constant
(`getUsedConstants`; a theorem's statement only) is a `Manual.*` constant, a core Lean/Std/Mathlib constant,
`W32`/`VAddr`/`PAddr`, the `Instruction` type and what Lean generates for it, or one of the listed shared items
of `FpOps.lean` (the IEEE core, `RoundingMode.ofBits`, `Flags.*` including the field projections `Flags.invalid`/`divZero`/`overflow`/`underflow`/`inexact`, the `BitVec` NaN classifiers `isQNaN32`/`64`, `isSNaN32`/`64`; not the `Format.is*`/`signBit` classifiers: the spec classifies encodings by its own Table 6.2 transcription `Manual.FPIsNaN`, ..., `Manual/Accuracy.lean`). This catches what the
token scan cannot see (`open Mips in … Fp.envOf`, `Mips.Fp.f32Abs`, `isModeledCp0Reg`, `opcodeOf`).

**The spec's decoder (wave 12b).** `Manual.Decode` (`Semantics/Manual/Decode.lean`) decodes by the format
diagrams `Manual.enc`, not by the model's `decode`; the top theorems take `Manual.decodeDiagram`. On the trusted
surface: `decode_diagram_sound`/`decode_diagram_complete` (it decodes exactly the diagram words),
`decode_agrees_manual` (where `decode` accepts, it agrees), `decode_none_manual` (where `decode` rejects a
diagram word, the Operation reaches an oracle choice: MFC0/MTC0 of an absent CP0 register, EXT/INS out of
range), `decoderSound_decodeDiagram`. Proofs: `Refine/DecodeDiagram.lean`, `Refine/DecodeBridge.lean`.

## I.2 Decisions

1. **Branch-likely: faithful two instruction times (owner decision, overrides plan §5.2).** The model
   gained `State.nullified` (Task 0; SPEC-NOTES §9 item 1b). The spec's `Arch.Nullify` is the same
   flag; `InstructionTime` consumes a nullified slot (`PC + 4`, no fetch, no exception, the timer
   ticks); an interrupt can be taken there (EPC = branch, BD = 1).
2. **Representation of `I+1:`.** An Operation schedules its `I+1:` statements with `I1 d`
   (`Delay.jump t | fallThrough | nullify`). `Complete` turns that into `PC := PC + 4` (the delay
   slot) and `BranchDelay := some t` (taken) or `some (branchPC + 8)` (not taken / nullify; "PC + 4"
   of the slot, Table 1.1 p.6). `BranchDelay.isSome` is `InstructionInBranchDelaySlot`. This is the
   model's representation, stated in the spec (`Manual/Cycle.lean` header).
3. **Decoding is a parameter.** `InstructionTime impl oracle dec a` takes the decoder; the spec only
   requires `DecoderSound dec` (an instruction returned for `w` has diagram `w`); completeness is 7D.
   The harness passes the model's `decode`; the spec never names it.
4. **`Operation` is partial in 7A.** `Operation i = none` for an untranscribed page; `InstructionTime`
   is then `none` and the harness counts the state as skipped. 7B makes `Operation` total and 7D can
   drop the `Option`.
5. **Exceptions keep the partial state.** `Pseudo` keeps the state at `SignalException`, so FCSR.Cause
   written before `CheckFPException` survives (Vol I-A §6.7.1); `GeneralExceptionProcessing` is
   applied to it. `LLbit ← 0` at every exception (SC p.350, "Exceptions between the LL and SC cause
   SC to fail").
6. **Bool tests in `if`.** Conditions are written as `Bool` (`!=`, `==`, `&&`) wherever possible:
   rewriting a `Prop` condition under its `Decidable` instance broke `simp` in the proofs (see
   Part II, rule 6).
7. **Dependent widths** (`memword7+8*byte..0 || GPR[rt]23-8*byte..0`) are written with `low x n`
   (`x_{n-1..0}`, `n` may be 0) and `++`, then `.setWidth 32`. Proofs case-split on the offset before
   rewriting (a width cannot be rewritten in place).
8. **`Status.RE` reads 0** (`StatusRE _ = false`): the bit is optional and absent ("If this bit is
   not implemented, it must be ignored on write and read as zero", Vol III Table 9.47 p.192), so
   `ReverseEndian` is always false; the stored `Status` word is not consulted for it.
9. **Refinement statement shape.** `Refine.<ctor>_refines (s) (hg : Good s) … (hw : enc i = some w) :
   Execute modelCtx w i (abs s) = some (abs (execInstr s i))`, plus `s.nullified = false` for the
   branches (the spec's completion writes `Nullify`). `Good s` = both register files have 32 entries
   and `$zero` reads 0 (all invariants of `step`).

## I.3 Validation (plan §3)

`lake exe EquivHarness` (gate step 6) runs every `tests/corpus` and `tests/oracle` program hosted and
compares, on every state, `Manual.InstructionTime modelImpl modelOracle decode (abs s)` with
`abs (step s)` field by field (memory: bytes the model wrote and the aligned word at a pilot load or
store). Result at the end of 7A: 183 programs, 10012 states compared, 0 mismatches, 47813 states
skipped (instruction not transcribed). A deliberate spec bug (`BEQL` not nullifying) is caught (1
mismatch, `tests/oracle/branch_likely_not_taken.asm`). `Semantics/Tests/ManualTests.lean` has
`#guard`s on concrete states.

## I.4 Review fixes (Wave 7R)

The independent review of 7B led to these changes (details and citations in `docs/spec/SPEC-NOTES.md`
§9 items 13, 21 and §11):

1. **Multiply-add family as separate operations** (MADD.fmt p.256, NMADD.fmt p.308): spec and model
   run multiply, add/subtract and (NM*) negate as separate operations, each with its own Cause, trap
   check and Flags. Spec: `Ops.MADD_S` … over `IEEE.mulS/addS/subS` and `IEEE.negS`; model: `fpStep` then `fpFinishS/D` with the union of the operations' conditions (Wave 12a: Cause per
   instruction, Flags only when no exception is taken; spec `FPCheck` then `FPResult`).
2. **NMADD/NMSUB operand order** as printed: NMADD `−(vfr + (vfs × vft))`, NMSUB `−((vfs × vft) − vfr)`.
3. **ABS/NEG of a QNaN**: `Oracle.absNegNaN` (readings A, A′, B); the model takes A′.
4. **Choices lifted out of the IEEE core**: `Impl.recipS/D`, `Impl.rsqrtS/D`, `Oracle.cvtQNaNToD/ToS`;
   the multi-QNaN choice is documented in the `Manual/FPU.lean` header.
5. **JR.HB / JALR.HB**: new constructors `jrHb`/`jalrHb`; `decode` no longer ignores the hint, so
   `DecoderSound decode` holds (checked by `#guard`s in `Tests/ManualTests.lean`, not proved).
6. **UNPREDICTABLE encodings**: `UnpredictableEncoding` + `Oracle.unpredictableEncoding` in
   `FetchExecute`; EXT/INS use `unpredictableOr` and read the diagram's 5-bit fields.
7. **`Impl.WF`** (`HSS = PSS = 0`, `IntCtl.VS = 0`), proved for `modelImpl`; `Oracle.shadowSetUndefined`
   removed; `vectorOffset` and `GeneralExceptionProcessing` take the `Impl`.
8. **New oracle fields** `ebaseWriteBEV0`, `loadClearsLL`; `ctc1Unpredictable` and `fprOddWrite` return
   an `Outcome`.
9. **Reset**: the oracle's `Status` is masked with the implemented Status bits.

## I.5 The cycle refinement and the top theorems (Wave 7D, part 1)

### Files

| File | Contents |
|---|---|
| `Manual/Relation.lean` (spec) | `UserPAddr`, `CP0Same`, `InaccessibleSame`, `AccessibleSame`, `SameMode`, `UnpredictableLimits`, `OutcomeValid`, `UndefinedOutcomeValid`, `OutcomeAgree`, `NIValue`, `NIOutcome`, `QNaNValid`, `Oracle.Valid`, `Step`, `InstructionTimes`, `OddFPR`, `FPRPair`, `FPCC`, `CTC1Unpredictable`, `CmpAbsorbs`, `MaddAbsorbs` (wave 9), `ConsultsOracle`, `ctxOf`, `ChoiceFree` (wave 8: `KernelState` and `OracleFreeOp` removed) |
| `Refine/Cycle.lean` | the non-instruction paths: `timerTick_abs`, `causeValue_abs`, `interruptRequests_abs`, `interruptsEnabled_abs`, `interruptTaken_abs`, `intVector_eq`, `takeInterrupt_abs`, `standbyStep_abs`, `nullifiedStep_abs`, `fetch_run`, `fetchError_abs`, `undecodable_abs` (+ encoding-space lemmas `isCop0Word_eq`, `isCop1Word_eq`, `isCop2Word_eq`, `cop01_disjoint`, `cop2_of_unpredictable`) |
| `Refine/Decode.lean` | `decode_enc` (`decode w = some i → enc i = some w`), `decoderSound_decode : DecoderSound decode`, `encode_of_decode`, `enc_eq_encode`, `decode_of_enc` (completeness on well-formed instructions) |
| `Refine/Invariant.lean` | the preservation of `FcsrReservedZero`, `StatusImplemented` (defined in `Refine/Defs.lean`) by `step`, `resetException`, establishment by `resetState`, `hostedStart`, `load` |
| `Refine/Instr.lean` | `InstrRefines`, `instrRefines_<ctor>` (all 183, generated), `allInstrRefines` |
| `Refine/Step.lean` | `step_preserves_inv`, `inv_resetState`, `inv_hostedStart`, `inv_load`, `execute_abs`, `stepCore_abs`, `step_eq_manual`, `run_refines_manual`, `resetException_refines_manual`, `resetState_refines_manual` |
| `Refine/ChoicePoints.lean` (wave 8) | `cf_<ctor>` for the 70 constructors whose Operation reads the oracle, `operation_choiceFree` (all 183), the tactics `case_ite`/`ofree` |
| `Refine/Determinism.lean` | `qnan32_to64`, `qnan64_to32`, `modelOracle_valid`, `step_refines_manual`, `fetch_oracleFree`, `execute_oracleFree`, `instructionTime_oracleFree`, `manual_step_deterministic`, `step_unique_of_choiceFree`, `modelOracleCE1`, `gep_causeCE_choice`, `interrupt_not_choiceFree`, `interrupt_choice_exists` |
| `Refine/ChoiceFp.lean` (wave 9) | `FPResult_eq`, `fpc`/`fpf`/`trapC` and their algebra (`trapC_inv`, `trapC_en`, `trapC_fpf`, `fpf_fpf`, `bit6_fpf`, `bit16_fpf`), the NaN branch of the binary FP operations (`NR`, `add_nan` …, `mul_qnan_left` …), `Dist`, `dist_left`/`dist_right`/`dist_both`, witness constants `QA64`, `QB64`, `SN64`, `One64`, `Four64`, `QA32`, `QB32` |
| `Refine/ChoiceWitness.lean` (wave 9) | the witness oracles `WP`, `wo`, `wo_valid`; `CEof`, `ceA`, `ceB`, `gep_CE`; `Obs`, `RunP`, `RowWitness` |
| `Refine/ChoiceRows.lean`, `ChoiceRowsFp.lean`, `ChoiceRowsFma.lean` (wave 9) | `rw_<ctor>` for the 68 constructors with a `ConsultsOracle` row; the tactics `runp`, `runp_fp`, `runp_fe` |
| `Refine/ChoiceExact.lean` (wave 9) | `operation_some`, `consults_row`, `Sep`, `resOf`, `sep_run`, `fetch_notCpU`, `choiceFree_exact`, `choiceFree_iff` |

### Decisions

1. **`InstructionTime` stays `Option`-valued**: `Operation` is total in content since 7B (every
   constructor is `some`), but making the type total would restate all per-instruction theorems; the
   top theorem is stated as `InstructionTime … (abs s) = some (abs (step s))`.
2. **The invariant** `Inv s` = `Good s` (32-entry register files, `$zero` reads 0) ∧
   `FcsrReservedZero s` (FCSR bits 22..18 read 0; needed by `cfc1_refines`) ∧ `StatusImplemented s`
   (`Status` holds only implemented bits; needed by the Reset refinement, whose oracle `Status` is
   masked). No path of the cycle needs a `pendingBranch`/`nullified`/`standby` consistency
   condition: `s.nullified = false` on the execute path comes from `stepCore`'s own case split and
   `enc i = some w` from `decode_enc`.
3. **Unconditional top theorems (7D part 2).** In part 1, `step_eq_manual` and its corollaries took
   `PendingRefines` (the per-instruction refinement of the constructors not yet merged) as a
   hypothesis. Part 2 merged the memory and FPU groups, generated `instrRefines_<ctor>` for all 183
   constructors and proved `allInstrRefines : ∀ i, InstrRefines i`; `Covered`, `instrRefines_covered`,
   `PendingRefines`, `allInstrRefines_of` and `step_eq_manual_of` were removed (the hypothesis is gone,
   nothing else in the statements changed).
4. **`ChoiceFree`** (exact since wave 8, see I.6): `false` at an interrupt and at every exception other
   than Coprocessor Unusable (`Cause.CE` "is loaded, but not defined"), at a word with an UNPREDICTABLE
   field value whose coprocessor is usable, at a CTI in a delay slot, and where the Operation reaches an
   oracle choice whose value can change the result (`ConsultsOracle`). Until wave 8 it was also `false`
   for every instruction outside a fixed list `OracleFreeOp`.
5. **`UnpredictableLimits` / `Oracle.Valid`** formalize the three restrictions of §1.2.1 (p.3-4) since
   wave 8 (I.6); until then "must not depend on inaccessible data" was not formalized.

### Top theorems (on the trusted surface since 7D part 2)

Proved in `Refine/` and restated in `Semantics/Statements.lean` (namespace `Trusted`, last section),
`StatementsProofs.lean` and `comparator.json` (143 → 156 statements; 158 since wave 8, I.6; 159 since wave 9, I.7):

~~~lean
theorem step_eq_manual (s : State) (hs : Refine.Inv s) :
    Manual.InstructionTime Manual.modelImpl Manual.modelOracle Manual.decodeDiagram (Refine.abs s) =
      some (Refine.abs (step s))
theorem step_refines_manual (s : State) (hs : Refine.Inv s) :
    Manual.Step Manual.modelImpl Manual.decodeDiagram (Refine.abs s) (Refine.abs (step s))
theorem run_refines_manual (s : State) (hs : Refine.Inv s) (n : Nat) :
    Manual.InstructionTimes Manual.modelImpl Manual.modelOracle Manual.decodeDiagram n (Refine.abs s) =
      some (Refine.abs (run s n))
theorem step_unique_of_choiceFree (s : State) (hs : Refine.Inv s)
    (h : Manual.ChoiceFree Manual.modelImpl Manual.decodeDiagram (Refine.abs s) = true) (a' : Manual.Arch)
    (h' : Manual.Step Manual.modelImpl Manual.decodeDiagram (Refine.abs s) a') : a' = Refine.abs (step s)
theorem modelOracle_valid : Manual.modelOracle.Valid
theorem manual_step_deterministic (i : Manual.Impl) (dec : W32 → Option Instruction)
    (a a₁ a₂ : Manual.Arch) (h : Manual.ChoiceFree i dec a = true) (h₁ : Manual.Step i dec a a₁)
    (h₂ : Manual.Step i dec a a₂) : a₁ = a₂
theorem decoderSound_decode : Manual.DecoderSound decode
theorem resetException_refines_manual (s : State) (h : Refine.StatusImplemented s) :
    Refine.abs (resetException s) = Manual.ResetException Manual.modelOracle (Refine.abs s)
theorem resetState_refines_manual :
    Refine.abs resetState = Manual.ResetException Manual.modelOracle (Refine.abs powerOnState)
theorem step_preserves_inv (s : State) (h : Refine.Inv s) : Refine.Inv (step s)
theorem inv_resetState : Refine.Inv resetState
theorem inv_hostedStart : Refine.Inv hostedStart
theorem inv_load (p : Program) : Refine.Inv (load p)
~~~

**What the comparator trusts for them.** `Statements.lean` imports `Semantics/Refine/Defs.lean`
(definitions only) and through it `Semantics/Manual/*`. The comparator checks that each solution
proves the same statement over the same constants; the meaning of these statements therefore rests
on the definitions they mention: the `Manual` definitions (the transcription), `modelImpl` and
`modelOracle` (the pins), `Refine.abs` and `Refine.Inv`, the model (`step`, `run`, `decode`,
`resetException`, `resetState`, `powerOnState`, `hostedStart`, `load`), and the IEEE rounding core of
`FpOps.lean` that `Manual.IEEE.*` wraps. Not their proofs (`Semantics/Refine/*`), which the kernel
replays (`lake check`).

# Part II. Transcribing an Operation (guide for 7B)

## II.1 Rules

1. **One `def` per manual page**, in `Semantics/Manual/Ops/<Family>.lean`, `namespace Manual.Ops`,
   named by the mnemonic (`ADD`, `LWL`, `ADD_S` for `ADD.fmt` with fmt S, `C_cond_S`, …). Add the arm
   to `Manual.Operation` and the format line to `Manual.enc` (in 7B: `Manual/Encoding/<Group>.lean`).
2. **Docstring**: `**MNEMONIC operands** — MD00086 Vol II-A Rev 6.06, MNEMONIC, p.N.` followed by the
   page's Operation pseudocode verbatim in a code block, then any Restrictions sentence the Lean
   implements (pre-Release-6 alignment), with its page. Look every page up with
   `python3 manuals/mipsdoc.py insn MNEMONIC`; image-only pages are read from the PDF and
   say so. The page number is the PRINTED page.
3. **Pseudocode lines as comments**: each Lean statement is preceded by the manual line it
   implements (`-- vAddr ← sign_extend(offset) + GPR[base]`).
4. **Vocabulary** (`Manual/Pseudocode.lean` etc.; nothing else from the model):
   * registers: `GPR (reg rs)` (read; r0 reads 0), `setGPR (reg rd) v`, `HI`, `LO`, `setHI`, `setLO`,
     `PC`, `setPC v` (time `I`), `I1 (.jump t)` / `I1 .fallThrough` / `I1 .nullify` (time `I+1`);
   * fields of the raw instruction: `reg w : Fin 32`, `imm16 w : BitVec 16`, `w.toNat` for `rd`/`sel`;
   * bit strings: `bits x hi lo` (`x_{hi..lo}`), `bit x k` (`x_k`, Bool), `low x n` (`x_{n-1..0}`),
     `a ++ b` (`a || b`), `BitVec.fill n b` (`b^n`), `BitVec.ofBool b`, `sign_extend v` (width of `v`),
     `zero_extend v`, `memory_address`;
   * exceptions: `SignalException .IntegerOverflow` etc. (`Manual.Exception`; Address Error carries
     the failing address);
   * memory: `AddressTranslation vAddr .DATA .LOAD|.STORE`, `LoadMemory CCA len pAddr vAddr .DATA`
     (returns the aligned word), `StoreMemory CCA len memElem pAddr vAddr`, `BYTE`/`HALFWORD`/`WORD`,
     `BigEndianMem`, `BigEndianCPU a`, `ReverseEndian a`;
   * FPU: `ValueFPR32`, `StoreFPR32` (D/L formats: add `ValueFPR64`/`StoreFPR64` with the oracle for an
     odd register), `FPResult (IEEE.op a x y)` for every arithmetic result (Cause, CheckFPException,
     Flags), `FPConditionCode`/`SetFPConditionCode` (to add, Figure 2.25/2.26 p.23-24);
   * CP0: the field readers of `Manual/CP0.lean`, `CPRRead`, `CPRWrite`,
     `IsCoprocessorRegisterImplemented`;
   * UNPREDICTABLE / UNDEFINED: read a field of `Pseudo.oracle` and `resolve` it; add the field to
     `Oracle` with the manual sentence, and its model choice to `modelOracle` with the SPEC-NOTES pin.
5. **Never** name a model definition (`readReg`, `execBody`, `decode`, masks, `fpUpdate`, …); gate step 1
   rejects it. Compute a field from its bit positions (`bit a.Status 1` is `StatusEXL`).
6. **Write conditions as `Bool`** (`if x != 0#2 then`, `if bit t 32 != bit t 31 then`) rather than
   `Prop` (`≠`): `simp` cannot rewrite inside a `Decidable` instance and the refinement proof breaks.
7. **Coprocessor Unusable and CTI-in-slot** are not in the Operation: `Cycle.Execute` does them from
   the word's encoding space and from `IsCTI`.
8. Run `lake exe EquivHarness` after each family: every mismatch is investigated (spec bug: fix the
   transcription; model bug: SPEC-NOTES entry with the reproducer, fix the model).

## II.2 Worked example 1: ADD (MD00086 Vol II-A Rev 6.06, ADD, p.33)

~~~lean
/-- **ADD rd, rs, rt** — MD00086 Vol II-A Rev 6.06, ADD, p.33.
```
temp ← (GPR[rs]31||GPR[rs]31..0) + (GPR[rt]31||GPR[rt]31..0)
if temp32 ≠ temp31 then
   SignalException(IntegerOverflow)
else
   GPR[rd] ← temp
endif
``` -/
def ADD (rs rt rd : W32) : Pseudo Unit := do
  let x ← GPR (reg rs)
  let y ← GPR (reg rt)
  -- temp ← (GPR[rs]31||GPR[rs]31..0) + (GPR[rt]31||GPR[rt]31..0)
  let temp : BitVec 33 := (BitVec.ofBool (bit x 31) ++ x) + (BitVec.ofBool (bit y 31) ++ y)
  -- if temp32 ≠ temp31 then SignalException(IntegerOverflow)
  if bit temp 32 ≠ bit temp 31 then SignalException .IntegerOverflow
  -- else GPR[rd] ← temp
  else setGPR (reg rd) (low temp 32)
~~~
(ADD's test `≠` between two `Bool`s predates rule 6; new code writes `!=`.)
`enc` line: `| .add rs rt rd => some (rFormat 0#32 rs rt rd 0#32 0x20#32)` (SPECIAL `000000` … ADD
`100000`, p.33). Refinement: `Refine.add_refines` (`Refine/IntArith.lean`): the 33-bit overflow test
is the model's `addOverflows` (`add_ovf`), the low 32 bits are `x + y` (`add33_low`).

## II.3 Worked example 2: BEQL (MD00086 Vol II-A Rev 6.06, BEQL, p.73)

~~~lean
/-- **BEQL rs, rt, offset** — MD00086 Vol II-A Rev 6.06, BEQL, p.73.
```
I:   target_offset ← sign_extend(offset || 0^2)
     condition ← (GPR[rs] = GPR[rt])
I+1: if condition then
        PC ← PC + target_offset
     else
        NullifyCurrentInstruction()
     endif
```
In `I+1`, `PC` is the address of the delay slot, the branch's `PC + 4`. -/
def BEQL (rs rt offset : W32) : Pseudo Unit := do
  -- I: target_offset ← sign_extend(offset || 0^2)
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- condition ← (GPR[rs] = GPR[rt])
  let condition := (← GPR (reg rs)) == (← GPR (reg rt))
  let pc ← PC
  -- I+1: if condition then PC ← PC + target_offset else NullifyCurrentInstruction() endif
  if condition then I1 (.jump ((pc + 4#32) + target_offset)) else I1 .nullify
~~~
`enc` line: `| .beql rs rt off => some (iFormat 0x14#32 rs rt off)`. Refinement:
`Refine.beql_refines` (`Refine/BranchLikely.lean`), with `s.nullified = false`.

# Part III. The approved plan (as handed over)

# Wave 7 plan: an independent manual specification and the refinement of `step`

I explored the repo read-only. I did not run lake and changed no files. The design below rests on four facts I found:

- **HashMap equality is a problem.** `State.physMem` is a `Std.HashMap`. Two maps built by inserting the same bytes in a different order are not equal values. So `step s = specStep s` cannot be stated directly over `State`.
- **The manual's own vocabulary fits this design.** MD00086 Vol II-A Rev 6.06 §2.2.2 (p.16-26) defines `ValueFPR`/`StoreFPR`, where an odd register with format D is UNPREDICTABLE (p.22-23). It also defines `CheckFPException` (p.23), `SignalException` and `NullifyCurrentInstruction` (p.26), and the `I:`/`I+n:` timing labels (§1.3).
- **Branch-likely is the main structural difference.** Its manual Operation says "I+1: … else NullifyCurrentInstruction()" (BEQL). The model does this differently (point 5).
- **`FpOps.lean` mixes two things.** It holds the IEEE operation core and also the FCSR folding (`fpUpdate`, its §9). Only the core may be shared.

## 1. Shape of the spec: an executable interpreter with an explicit choice argument

I recommend a hybrid: a relation defined on top of a function that takes the manual's choices as an argument.

- **`Manual.Arch`** is the manual's state, with functions instead of arrays and maps:
  - `PC`, `GPR : Fin 32 → W32`, `HI`, `LO`, `FPR`, `FCSR`, `Mem : PAddr → UInt8`, `LLbit`, `LLAddr`
  - the CP0 registers under the manual's names: `Status`, `Cause`, `EPC`, `BadVAddr`, `ErrorEPC`, `EBase`, `ConfigK0/K23/KU`, `Count`, `Compare`, `CauseTI`, `HWREna`
  - the inputs `HW : BitVec 6`, `LowPower`, and `BranchDelay : Option VAddr`, documented as "the PC written by the previous instruction's I+1 statements".
- **`Manual.Impl`** holds the fixed choices of one implementation: Count increments per instruction time, CCRes, PRId, the constant parts of Config/Config1/Config2/Config3/IntCtl/SRSCtl, and whether WAIT restarts on an interrupt that is not enabled. `Manual.modelImpl` is the model's instance.
- **`Manual.Oracle impl`** has one field for each place the manual allows several outcomes, typed by what it is asked:
  - `unpredictableWord` (an odd FPR with format D)
  - `ctiInSlot : (a : Arch) → {a' // Manual.UnpredictableLimits a a'}`, the limits of Vol II-A §1.2 (p.3-4)
  - `storeClearsLL` (a memory access between LL and SC: "may succeed or fail")
  - `exceptionClearsLL`
  - `causeCE` ("loaded, but not defined", Vol III p.87)
  - `resetUndefined` (registers whose reset state is undefined)
- **`Manual.InstructionTime impl o : Arch → Arch`** is deterministic once the oracle is given, and it runs, so it can be tested.
- **The relation** is `Manual.Step impl a a' := ∃ o, Manual.InstructionTime impl o a = a'`. It allows every outcome the manual permits.

Why not a Prop-valued relation or monad: `step` is checked against the spec by equality with one named oracle, which is cheap to prove (`simp only` plus bridge lemmas, no searching for witnesses). The spec can also be run against `step` on the test corpus before any proof work. Determinism is a separate theorem about the oracle.

Pseudocode is written in `Manual.Pseudo := ReaderT (Impl × Oracle) (StateT Arch (Except Signal))`, so `SignalException` aborts the instruction as p.26 says. An Operation looks like the manual:

```
/-- ADD — MD00086 Vol II-A Rev 6.06, ADD, p.33 -/
def ADD (rs rt rd) : Pseudo Unit := do
  let temp := sext33 (← GPR rs) + sext33 (← GPR rt)
  if temp[32] ≠ temp[31] then SignalException .IntegerOverflow else GPR rd ≔ temp[31:0]
```

What the spec shares with the model:
- **Allowed:** `Types.State` (only through `abs`), `Word`, and the `Instruction` inductive as names and fields only. `decode` is not shared: the spec has its own encoding (`Manual.enc`).
- **Trusted dependency:** the rounding core of `Mips.Fp` (`f32Add` … `cvt*`, `cmp`), wrapped as `Manual.IEEE.*` and declared as trusted. FCSR Cause/Flags/Enables handling and `CheckFPException` are transcribed again from Vol I §6.7.1 and Vol II-A p.23. `fpUpdate`, `envOf` and every `*Mask` constant in `Types.lean` are off limits. The spec defines fields by bit position (`Status.EXL := Status[1]`).

## 2. Files and top theorems

**`Semantics/Manual/` (the spec, a new trusted surface):**

| File | Contents |
|---|---|
| `Arch.lean` | `Arch`, `Impl`, `Oracle`, `UnpredictableLimits` |
| `Pseudocode.lean` | `Pseudo`, `GPR`, `HI`/`LO`, `sign_extend`, `zero_extend`, `memory_address`, `SignalException`, `NullifyCurrentInstruction` (§2.2, p.16-26) |
| `Memory.lean` | `AddressTranslation` (Vol III App. A.1 p.313-317, Table 4.2 p.30), `LoadMemory`, `StoreMemory`, `AccessLength`, `BigEndianCPU`/`BigEndianMem`/`ReverseEndian` |
| `FPU.lean` | `ValueFPR`, `StoreFPR`, `FPConditionCode`, `SetFPConditionCode`, `CheckFPException`, `IEEE` |
| `CP0.lean` | per-register read and write semantics from the Vol III ch.9 tables (`CauseRead`, the side effect of a Compare write) |
| `Exceptions.lean` | `GeneralExceptionProcessing` (§6.2.3 p.86-88, verbatim, including `vectorBase31..30 ‖ (vectorBase29..0 + vectorOffset)`), per-exception extras (§6.2.9, §6.2.21, §6.2.22, §6.2.26), priorities (Table 6.6 p.83) |
| `Interrupts.lean` | §6.1 and Table 6.2 p.72-73 |
| `Timer.lean` | §9.27 and §9.30 |
| `Reset.lean` | §6.2.5 p.89-90 |
| `Encoding.lean` | `Manual.enc : Instruction → W32`, one line per format diagram |
| `Ops/{IntArith,Shift,MulDiv,BitOps,Immediate,Memory,Atomic,Unaligned,Branch,BranchLikely,Jump,Trap,Cp0,FpuArith,FpuConvert,FpuCompare,FpuMove,FpuMemory,FpuBranch}.lean` | one `def` per manual page, named by mnemonic; docstring citation `MD00086 Vol II-A Rev 6.06, <MNEMONIC>, p.N`; the pseudocode lines kept as comments next to the Lean |
| `Operation.lean` | `Manual.Operation : Instruction → Pseudo Unit` (183 one-line arms since 7R) |
| `Cycle.lean` | `InstructionTime`: interrupt check → low power → fetch (Fig 2.29 p.25) → decode by `enc` → CTI in delay slot (oracle) → `Operation` → apply `BranchDelay` or `PC+4` → timer; plus `Step`, `Steps` |
| `Choices.lean` | `modelImpl`, `modelOracle`: each field is a one-line pin citing SPEC-NOTES |

**`Semantics/Refine/` (proofs, not trusted):**

| File | Contents |
|---|---|
| `Abs.lean` | `abs : State → Manual.Arch` (field-by-field projection only), with `abs_writeReg`, `abs_writeMem*` (via `HashMap.getElem?_insert`), etc., all under `RegFilesWF` |
| `Fetch.lean` | `translate_eq`, `readMem*_eq` |
| `Bridge.lean` | `exceptionEntry_eq`, `takeInterrupt_eq`, `advance_eq`, `fpFinishS/D/Cmp_eq`, `timerTick_eq`, `resetException_eq`, `causeValue_eq` |
| `Encoding.lean` | `enc_eq_encode` (one theorem per constructor), `decode_iff_manual` (from `decode_encode` plus the converse in `DecodeSpec`) |
| `<Family>.lean` | `Refine.<ctor>_refines`, one per constructor |
| `Step.lean` | the top theorems |

**Trusted surface:** add to `Statements.lean`, `StatementsProofs.lean` and `comparator.json`:
- `step_eq_manual : s.RegFilesWF → abs (step s) = Manual.InstructionTime modelImpl modelOracle (abs s)`
- `step_refines_manual : s.RegFilesWF → Manual.Step modelImpl (abs s) (abs (step s))`
- `modelOracle_valid`, which makes the `∃` above meaningful
- `manual_step_deterministic : Manual.ChoiceFree a → Manual.Step i a a₁ → Manual.Step i a a₂ → a₁ = a₂`
- `step_unique_of_choiceFree`
- `run_refines_manual`
- `resetException_refines_manual`, `resetState_refines_manual`

`ChoiceFree` is decidable. It is false only at an actual choice point, for example a store while `LLbit = 1`, a CTI in a delay slot, or an odd FPR used as a double. CLAUDE.md's trusted list gains `Semantics/Manual/*` and `abs`.

## 3. A proof strategy that keeps build time down

- **Reason about `abs`, not the State record.** Never destructure all 25 State fields and close with `rfl`, which is what makes the existing proofs heavy. Rewrite through the `abs_*` and bridge lemmas instead; HashMap and Array facts are proved once, in `Abs.lean`.
- **Do the hard bit-level work once,** in `Bridge` and `Fetch`, with `bv_omega`, `BitVec.ext` and `getLsbD` lemmas. Examples: the vector "+" against the model's "|||", `temp32≠temp31` against `addOverflows`, and the lwl/lwr lane formulas (4 offsets × 4 instructions).
- **One theorem per constructor,** closed by a `manual_refine` macro (`simp only [execBody, Manual.<OP>, Pseudo.run_*, abs_*, bridge…]` with a closed lemma set). The top theorem does `cases instr` and closes each case with `exact Refine.<ctor>_refines …`, so the terms match syntactically and no large `match` is elaborated. This is the opposite of the 13-minute general delay-slot proof.
- **Rules for agents:**
  - no `decide` on `BitVec`, no default `simp` set, no `maxHeartbeats 0`
  - no `bv_decide` or `native_decide`
  - each `Refine/*.lean` builds in 60 s or less (measure with `lean --profile`)
  - target at most +180 s on `lake check`
- **Validate before proving:** a `MipsRun --manual` mode and an EquivHarness check compare `Manual.InstructionTime modelImpl modelOracle` with `step` on `tests/corpus` and `tests/oracle`, along with `#guard`s in `Semantics/Tests/ManualTests.lean`. This finds spec and model bugs before anyone spends effort on proofs.

## 4. Sub-waves

| Sub-wave | Who | What | Files owned |
|---|---|---|---|
| **7A, infrastructure + pilot** | 1 Opus (a second joins for Bridge) | All of `Manual/` except `Ops`; `Refine/{Abs,Fetch,Bridge}`; pilots ADD, LW/SW, LWL, BEQ/BEQL, ADD.S, MTC0, with `_refines`; the harness mode | those files |
| **7B, transcription** (parallel worktrees) | 4 Sonnet | `Ops/*` plus their part of `Encoding.lean` (split as `Encoding/<Group>.lean`); each Operation copied from `mipsdoc.py insn` | S1: integer ALU (Arith, Shift, MulDiv, BitOps, Immediate). S2: Memory, Atomic, Unaligned, Trap. S3: Branch, BranchLikely, Jump, Cp0. S4: FPU |
| **7B, merge** | orchestrator | Writes `Operation.lean`, runs the harness, triages mismatches into spec bugs and model bugs (model bugs go to SPEC-NOTES with a reproducer) | `Operation.lean` |
| **7B, review** | Opus | Line-by-line check of each Ops file against the manual; no edits | none |
| **7C, proofs** | 4 Opus, worktrees | `Refine/<Group>.lean` and `Refine/Encoding/<Group>.lean`, same split as 7B | those files |
| **7D, closure** | 1 Opus | `Refine/Step.lean`: the top theorems, interrupt, standby, timer and reset paths, determinism, `modelOracle_valid`, trusted-surface edits, docs (README "what is proved", DESIGN, PROOF-NOTES) | those files and docs |

Each sub-wave ends gate-green. The top theorem appears only in 7D, so no `sorry` or stub is ever needed.

## 5. Where the model and the manual differ, and how the spec should say it

1. **Delay slots.** The spec follows the manual's I/I+1 order: the branch's I+1 `PC ←` takes effect with the delay-slot instruction's I part, and is dropped if that instruction signals an exception (EPC = branch, BD = 1, Table 6.11 p.87). A not-taken branch stores `branchPC+8`, which has the same effect. That choice must be stated in `Cycle.lean`.
2. **Branch-likely nullification (owner decision needed).** In the manual the nullified delay slot is a separate instruction time. The model does it within the branch's own step, so `Count` advances once instead of twice and no interrupt can be taken at the nullified slot.
   - Option (a): spec merges the branch and the nullified slot into one step, as an `Impl` pin justified by the implementation-dependent Count rate and asynchronous interrupts. I recommend this.
   - Option (b): faithful two-step spec. It needs a new `State.nullifyNext` field, which is a model and trusted-surface change, and a stuttering simulation.
3. **Exception entry.** The model clears `LLbit` at every exception and loads `CE = 0`; in the spec both are oracle choices. Vector "+" against "|||" is one lemma. With EXL = 1 the vector offset is 0x180 even for an interrupt, which never matters because interrupts are masked then.
4. **FP.** `CheckFPException` tests bit 17 (Unimplemented, "E"). The spec must include it, so a lemma "FpOps never sets E" is needed. Flags are updated only when no trap is taken (Vol I §6.7.1).
5. **LL/SC.**
   - The model's `llAddr` comparison comes from SC p.347 ("SC will fail if…").
   - The pin that a store clears LLbit becomes an oracle choice.
   - ERET clears LLbit, as its Operation says.
6. **lwl/lwr/swl/swr.** The spec uses the page formulas (`memword7+8*byte..0 ‖ GPR[rt]23-8*byte..0`, an aligned `LoadMemory`), while the model works byte by byte. This is the hardest BitVec lemma.
7. **The timer runs after the instruction.** This is an `Impl` choice: `mfc0 Count` sees the value from before the tick, and a Compare write clears TI before the tick can set it again. It must be cited as implementation-dependent (§9.27 p.183).
8. **Interrupt before fetch, and WAIT's I+1.** The interrupt is taken first, with EPC = PC (Table 6.6 / 6.7 p.83-84). The `LowPower` restart on a non-enabled request is the `Impl` flag (WAIT p.442-443).
9. **Decode.** The model rejects words whose must-be-zero fields are nonzero (strict decode). For those words the spec states "not matching any diagram means RI or CpU per §6.2.21 and Table 6.6", and each such case needs a SPEC-NOTES pin where the manual says UNPREDICTABLE.
10. **CTI in a delay slot.** The manual allows any outcome within the §1.2 limits; the model's RI must be proved to stay within them (`modelOracle_valid`).

## 6. Definition of done, checked by the gate

**Status at 7D part 2:** 1 (gate green) done; 2 (top theorems in the comparator) done; 3: the
independence rule is gate step 1 (`scripts/manual_independence.py`), and that every constructor has a
refinement is checked by the build itself (`allInstrRefines` in `Refine/Instr.lean` is a `cases` over
`Instruction` closed by `instrRefines_<ctor>`; a constructor without one leaves a goal open); an
`Operation` arm that is `none` would make that constructor's refinement false (`Execute` is then
`none`), and a missing `Manual.enc` line breaks `decode_enc` (`Refine/Decode.lean`) for every
constructor `decode` produces; a TRACE.md "manual clause / refinement" column is not done; 4 (the
harness in the EquivHarness step) done in 7A; 5 (README) done in 7D part 2.

1. The full gate is green.
2. The top theorems are in the comparator.
3. A new gate step, or an extension of `trace.py --check-manual`, checks that:
   - every `Instruction` constructor has an arm in `Manual.Operation`, a cited `Ops` def whose page is confirmed with `mipsdoc.py` (when the manual texts are present), a `Manual.enc` line, and `Refine.<ctor>_refines` plus `enc_eq_encode_<ctor>`
   - **independence:** `Semantics/Manual/*` imports only `Word`, `Types`, `Instruction`, `FpOps`, and uses none of the names defined in `Step.lean`/`State.lean`, `decode`, any `*Mask`, `fpUpdate` or `envOf` (the forbidden list is generated from those files)
   - `docs/TRACE.md` gets a "manual clause / refinement" column.
4. The `--manual` harness is part of the EquivHarness step.
5. README marks `_spec_raw` as restatements and `step_eq_manual` as the independent correctness result. A list of the `modelOracle`/`modelImpl` pins is in SPEC-NOTES.

### Critical Files for Implementation
- Semantics/Step.lean
- Semantics/State.lean
- Semantics/Types.lean
- Semantics/FpOps.lean
- Semantics/Statements.lean
- scripts/trace.py
- Semantics/Specs/DecodeSpec.lean

## I.6 Wave 8: exact choice points, the third UNPREDICTABLE restriction, RECIP accuracy

**`ChoiceFree` (`Manual/Relation.lean`).** `ConsultsOracle ins a` lists, per Operation that reads the
oracle, the condition under which the read is reached and its value can change the result: the loads
and stores while `LLbit = 1` (`LL`/`SC` never: they set `LLbit` themselves afterwards), `DIV`/`DIVU` by
zero, `MUL`, an odd FPR read or written as a double on the path the Operation takes, a quiet NaN operand
of `ABS`/`NEG`/`CVT.D.S`/`CVT.S.D`, a quiet-NaN sum in `NMADD`/`NMSUB`, `CFC1` of a missing register into
`rt ≠ 0`, the UNPREDICTABLE arms of `CTC1`/`EXT`/`INS`, branch-and-link with `rs = 31`, `JALR`/`JALR.HB`
with `rs = rd`, `MFC0`/`MTC0` of a missing register and an `EBase` write with `BEV = 0`. Where it is
`false` the Operation's run is the same under every oracle (`Refine.operation_choiceFree`, all 183
constructors: 113 by `rfl`, 70 by the `cf_<ctor>` lemmas of `Refine/ChoicePoints.lean`). `ChoiceFree`
uses it in place of `OracleFreeOp`; an UNPREDICTABLE encoding whose coprocessor-usability check fires
first is now choice-free (the Coprocessor Unusable exception is determined). The other direction is
proved for the `Cause.CE` choice (`gep_causeCE_choice`, `interrupt_choice_exists`) and argued per row
for `ConsultsOracle` (wave 8); wave 9 proved it for every row (I.7).

**`Oracle.Valid`.** Restriction 1 of §1.2.1 ("must not depend on any data source (memory or internal
state) which is inaccessible in the current processor mode", p.3) is non-interference: in User Mode,
for two states in the same mode that agree on the accessible state (`AccessibleSame`: everything but
the physical memory no User Mode address reaches and, while `CU0 = 0`, the CP0 registers), every
UNPREDICTABLE value is equal (`NIValue`: `divByZero`, `divuByZero`, `mulHILO`, `fprOddRead`,
`cfc1Unpredictable`) and every UNPREDICTABLE outcome agrees on the accessible state (`NIOutcome`).
Restriction 2 (`InaccessibleSame` in `UnpredictableLimits`) now leaves the CP0 registers free when
`CU0 = 1` (they are accessible then; Vol III §3.5.3, p.23). The UNDEFINED fields `cp0Undefined` and
`ebaseWriteBEV0` are held to the one restriction on UNDEFINED operations (§1.2.2, p.4: must not hang),
not to the UNPREDICTABLE limits. `QNaNValid`: the `CVT` QNaN fields return quiet NaNs (MD00082 Vol I-A
§6.3.1.5, p.82). Not restricted: `causeCE`, `storeClearsLL`, `loadClearsLL`, `resetUndefined` (beyond
memory and the input lines).

**`Impl.Valid` (`Manual/Choices.lean`).** `Impl.WF` and `Impl.RecipAccurate`: `RECIP.fmt` within 1 ULP
(order-key distance) of the IEEE core's correctly rounded `1.0 / fs` wherever that is finite (RECIP.fmt
p.336). The bound against the exact result and `RSQRT.fmt`'s 2-ULP bound (p.343) are not formalized
(still the case after wave 9, I.7).

**Trusted surface 156 → 158**: added `interrupt_choice_exists`, `modelImpl_valid`. The statement text
of `modelOracle_valid`, `manual_step_deterministic` and `step_unique_of_choiceFree` is unchanged; their
meaning changed with `Oracle.Valid` and `ChoiceFree` (README, (b′)).

## I.7 Wave 9: `ChoiceFree` is exact (proved), three rows refined, test robustness

**`choiceFree_exact` (trusted, `Refine/ChoiceExact.lean`).**

~~~lean
theorem choiceFree_exact (dec : W32 → Option Instruction) (a : Manual.Arch)
    (h : Manual.ChoiceFree Manual.modelImpl dec a = false) :
    ∃ o₁ o₂ : Manual.Oracle, o₁.Valid ∧ o₂.Valid ∧
      Manual.InstructionTime Manual.modelImpl o₁ dec a ≠ Manual.InstructionTime Manual.modelImpl o₂ dec a
~~~

No hypothesis on `a` (no invariant) and any decoder; the implementation constants are the model's
(`modelImpl`): for another `Impl`, `recipD`/`rsqrtD` could be constant functions and hide the value read
from an odd register, so the statement is false for an arbitrary `Impl`. With `manual_step_deterministic`
it gives `Refine.choiceFree_iff` (`ChoiceFree modelImpl dec a = true` iff all valid oracles give the same
instruction time); `choiceFree_iff` is proved but not on the trusted surface.

**Proof.** The witnesses are one family `wo p ce` (`Refine/ChoiceWitness.lean`): every UNPREDICTABLE or
UNDEFINED operation of the oracle signals Reserved Instruction ("may cause ... arbitrary exceptions",
MD00086 Vol II-A Rev 6.06 §1.2.1, p.3; §1.2.2, p.4), every value field is a constant (`p`), and
`Cause.CE` is the constant `ce`; `wo_valid`. The two `ce` are chosen different from each other and from
`Cause.CE` of `a` (`ceA`, `ceB`), so a signalled exception (whose `Cause.CE` is the oracle's, Vol III
§6.2.3, p.87) differs from another signalled exception and from a completed instruction (which leaves
`Cause` alone). A completed instruction is told apart by `Obs` (`LLbit`, `HI`, `GPR`, `FPR`, `FCSR`,
memory). This avoids a lemma "no Operation reads `causeCE`". Per row (`rw_<ctor>`, 68 constructors):

| Row | Witness values | Visible in |
|---|---|---|
| loads / stores, `LLbit = 1` | `loadClearsLL` / `storeClearsLL` true, false | `LLbit` (SC p.347-348) |
| `DIV`/`DIVU` by zero, `MUL` | `(HI, LO)` = (0,0), (1,1) | `HI` |
| `CFC1` missing register, `MFHC1` odd `fs`, `rt ≠ 0` | 0, 1 / all-zeros, all-ones | `GPR[rt]` |
| `SDC1`/`SDXC1` odd `ft`, `LLbit = 0` | all-zeros, all-ones doubleword | the bytes of the last word stored |
| `CTC1`, `MFC0`/`MTC0`, `EXT`/`INS`, `rs = 31` links, `JALR rs = rd`, `MTHC1`/`LDC1`/`LDXC1` odd, any odd `fd` | Reserved Instruction | `Cause.CE` (both signal) |
| `ABS`/`NEG` (S and D), `NMADD`/`NMSUB` (S and D) | readings `A`, `B` of `absNegNaN`; odd registers read the quiet NaN `QA64` | `FCSR.Cause.V` (bit 16) or a trap |
| `ADD`/`SUB`/`MUL`/`DIV.D` odd source | signaling NaN, quiet NaN | the result or Invalid (`dist_*`) |
| `SQRT`/`RECIP`/`RSQRT.D`, `CVT.S.D` odd `fs` | signaling NaN, quiet NaN | Invalid |
| `ROUND`/`TRUNC`/`CEIL`/`FLOOR`/`CVT.W.D` odd `fs` | +1.0, +4.0 | `FPR[fd]` = 1, 4 |
| `MOV.D`, `MOVF/MOVT/MOVN/MOVZ.D` | two quiet NaNs | `FPR` pair of `fd` |
| `CVT.D.S`/`CVT.S.D` quiet NaN | the two QNaNs of each field | `FPR` |
| `C.cond.D` | signaling NaN; quiet NaN (`cond3 = 0`) or +1.0 (`cond3 = 1`) | Invalid |
| `MADD.D`/`MSUB.D` | five cases (`rw_maddD`) | the result, Invalid, a trap, or the Invalid Flag (bit 6) |

The other cases of `ChoiceFree` (interrupt: `interrupt_choice_exists`; fetch error, undecodable word,
UNPREDICTABLE encoding, CTI in a delay slot, an Operation that signals with `ConsultsOracle = false`
(via `operation_choiceFree`)) all signal an exception other than Coprocessor Unusable under both
witnesses.

**`ConsultsOracle` rows changed (spec, `Manual/Relation.lean`).** The proof found three rows that were
`true` where no oracle can change the result; each is now exact and soundness was re-proved
(`cf_mfhc1`, `cf_cCondD`, `cf_maddD`, `cf_msubD` in `Refine/ChoicePoints.lean`):
1. `MFHC1 rt, fs`: was `OddFPR fs`, now `OddFPR fs && reg rt != 0` (the value goes to `GPR[0]`).
2. `C.cond.D cond cc fs ft`: was `OddFPR fs || OddFPR ft`; now `false` also when exactly one register is
   odd and the other operand `y` satisfies `CmpAbsorbs cond y` (`y` a signaling NaN, or a quiet NaN with
   `cond3 = 1`): the comparison is unordered and Invalid is raised whatever the odd register reads
   (C.cond.fmt, p.110, p.112-113).
3. `MADD.D`/`MSUB.D fd fr fs ft`: was `OddFPR fr || OddFPR fs || OddFPR ft || OddFPR fd`; now `false`
   also in `MaddAbsorbs`: `fd`, `fs`, `fr` even, `ft` odd, `fs` a quiet NaN, the Invalid enable (FCSR bit
   11) 0, and the Invalid Flag (bit 6) already 1 or `fr` a signaling NaN. The multiply then delivers `fs`
   whatever `ft` reads, its Invalid does not trap, its Cause is overwritten by the add ("The Cause bits
   are written during each floating point arithmetic operation", MD00082 Vol I-A Rev 6.01 §6.7.1, p.99),
   and its Flag is set anyway (MADD.fmt p.256, MSUB.fmt p.287: "as if separate floating-point multiply
   and add instructions were executed").

No other row changed. No model file changed, so no `_spec_raw` or refinement theorem changed.

**Trusted surface 158 → 159**: added `choiceFree_exact`. The statement text of `manual_step_deterministic`
and `step_unique_of_choiceFree` is unchanged; their hypothesis `ChoiceFree … = true` now holds at more
states (the three refinements), so they say more.

**`RSQRT.fmt` 2-ULP and `RECIP.fmt` against the exact result: not done.** The plan was to state
`Impl.RsqrtAccurate` (2 ULP of the correctly rounded `1/sqrt(x)`, the latter defined by rational
comparisons `y² · x ≤ 1`) and prove it for `modelImpl` (`SQRT.fmt` then `DIV.fmt`). The proof needs an
error bound for the core's rounding `Mips.Fp.Format.roundCore` (at most 1 ULP, monotone), and the
correctness of `Exact.sqrt`/`isqrt` and `Exact.div` with their sticky bits. None of these exists in the
repository. A rough error analysis says the composition stays within 2 ULP for all four rounding modes
(for RZ: `r − 1/√x ∈ (−1, 2)` ULP, RP symmetric, RN < 1.5 ULP), but this was not machine-checked.
`Impl.Valid` is unchanged (`WF ∧ RecipAccurate`), and `modelImpl_valid` with it.

**Test robustness: `tests/oracle/irq_wait_timer.asm`.** Two races under host load: (1) QEMU descheduled
between reading `Count` and writing `Compare` leaves `Compare` in the past, the match happens only after
`Count` wraps, and the `wait` never returns; (2) the request arrives after `IE = 1` but before the `wait`,
the interrupt is taken there, and the `wait` then sleeps with `Compare` re-armed far ahead. Fix: arm with
`IE = 0` and re-arm while `Count − Compare ≥ 0` (signed) after the write; the handler checks that EPC is
the instruction after `wait` and otherwise re-arms (same check, `EXL = 1`) and returns without recording.
In the model neither fallback runs; expectations unchanged. Load test: 40 runs of
`scripts/oracle.py --only irq_wait_timer` under `stress-ng --cpu 88` on 44 cores: 40 pass.

## I.8 Wave 10: the IEEE core proved; `RECIP`/`RSQRT` against the exact result

**The shared core is no longer only trusted.** `Manual.IEEE.*` still wraps the rounding core of
`Semantics/FpOps.lean`, but the core is now proved against the IEEE 754 definition the manual references
(`Semantics/FpOpsSpec.lean`, `Semantics/FpOpsCorrect*.lean`, README (d)): every nonzero exact value is rounded
as `Format.RoundSpec` requires (correct rounding per MD00082 Vol I-A Rev 6.01 Table 6.10, p.95; overflow §6.7.2.5
and Table 6.14, p.100-102; inexact §6.7.2.6, p.102; tininess after rounding §6.7.2.3, p.101), and `ADD`/`SUB`/
`MUL`/`DIV`/`SQRT` of both formats are correctly rounded. A rounding bug in the shared core would now contradict a
kernel-checked theorem instead of passing through the refinement unnoticed. Still trusted: the reference definition
itself and what the theorems do not cover (special operands, conversions, compares, NaN choices).

**`Impl.Valid` (`Manual/Accuracy.lean`).** Now `WF ∧ RecipAccurate ∧ RecipExact ∧ RsqrtAccurate`:

* `Impl.RecipExact` — RECIP.fmt (MD00086 Vol II-A Rev 6.06 p.336): "The computed result differs from the both the
  exact result and the IEEE-mandated representation of the exact result by no more than one unit in the
  least-significant place (ULP)". For `e.flush = false`, a finite nonzero `fs = y` with `|1/y| ≤` the largest
  finite number, and a finite result `r`: `WithinULPs (1/y) r 1`.
* `Impl.RsqrtAccurate` — RSQRT.fmt (p.343): "... by no more than two units in the least-significant place (ULP)".
  For `e.flush = false`, a finite `fs = y > 0` and a finite result `r`: `WithinULPsRsqrt y r 2`, i.e. with
  `2^ex ≤ 1/√y < 2^(ex+1)` and `U = ULP ex`: `r - 2U ≤ 1/√y ≤ r + 2U`, all stated by squares.
* `ULP eb fb ex = 2^max(E_min - fb, ex - fb)`: the weight of the last significand bit in the exact result's binade
  (MD00082 Table 6.1, p.78-79), the denormalized unit below `2^E_min`. `FPValue` transcribes Table 6.2 (p.80-81)
  again inside `Semantics/Manual/` (the import rule forbids `FpOpsSpec`); `Refine/ImplValid.lean` proves
  `FPValue 8 23 = binary32.value` (and for 64) by `rfl`.

Restrictions (the statements say them): no flushing (with FCSR.FS = 1, §6.7.2.4 p.102, a tiny result may be
replaced by zero, which no ULP bound survives); `RECIP` only where the exact reciprocal is in the finite range;
only finite results are constrained. `modelImpl_valid` (`Refine/ImplValid.lean`) proves all of it for the model in
every rounding mode; for `RSQRT` (`SQRT.fmt` then `DIV.fmt`) the directed modes rely on the two roundings pulling in
opposite directions, RN on two half-ULP errors (`rsqrt_core`).

**Trusted surface 159 → 175**: the 16 floating-point statements listed in `docs/PROOF-NOTES.md`, "Wave 10".


## I.9 Wave 11: the shared FP core proved on every operand

**What the refinement shares is now proved, not trusted.** The manual specification (`Semantics/Manual/FPU.lean`,
`Manual.IEEE.*`) still calls the FP functions of `Semantics/FpOps.lean` for the arithmetic, the conversions and the
compare relation, so a mistake there would pass through the refinement unnoticed. Wave 10 proved the rounding core
and the finite, nonzero-result arithmetic; wave 11 proves the rest of every function the two sides share, against
reference definitions written from the manual in `Semantics/FpOpsSpec.lean` (README (d), `docs/PROOF-NOTES.md`,
"Wave 11"):

* `Manual.IEEE.addS/subS/mulS/divS/sqrtS` and the `D` forms (`f32Add` … `f64Sqrt`): `AddSpec`, `MulSpec`, `DivSpec`,
  `SqrtSpec` on every operand (NaN rule MD00082 Vol I-A Rev 6.01 §6.3.1.4-5, p.81-82; invalid operations §6.7.2.1,
  p.100; division by zero §6.7.2.2, p.100; ∞ arithmetic §6.3.1.3, p.81; flush to zero §6.7.2.4, p.102), every FCSR
  environment (`f32Add_spec` …).
* `Manual.IEEE.toWordS/toWordD` (`f32ToW32`, `f64ToW32`): correct rounding to an integer in each of the four modes
  the `convert_and_round` of `CVT/ROUND/TRUNC/CEIL/FLOOR.W.fmt` names, `2^31-1` with Invalid only otherwise
  (`ToWordSpec`).
* `Manual.IEEE.cvtDS/cvtSD/cvtSW/cvtDW` (`f32ToF64`, `f64ToF32`, `w32ToF32`, `w32ToF64F`): `WidenSpec`/`ExactSpec`
  (exact), `ConvertSpec`, `FromIntSpec`. The QNaN operand case of `cvtDS`/`cvtSD` goes through
  `Oracle.cvtQNaNToD/ToS`; the model's values for them are QNaNs (`modelOracle_valid`) and `ConvertSpec`/`WidenSpec`
  allow any QNaN with no exception, as §6.3.1.5 does.
* `Manual.IEEE.ltS/eqS/ltD/eqD` (`f32Relation`, `f64Relation`): the order of the values in the extended reals
  (`cmpRel`; `f32Compare_spec` with the 16-row `condTable`, MD00086 Vol II-A Rev 6.06 C.cond.fmt p.110-113).
* Not shared, but proved for the model: `fpUpdate` meets `FcsrSpec` (§6.7.1, p.99; CheckFPException, p.23) — the
  manual side has its own transcription, `Manual.FPResult` — and `ABS`/`NEG` meet `SignOpSpec` with reading A′
  (the manual side's `signOpS`/`signOpD` with `Oracle.absNegNaN = .A'`). `MADD`/`MSUB`/`NMADD`/`NMSUB` are proved to be
  the separate operations at the level of `step` (`maddS_separate` …), as `Manual.Ops` already writes them.

What remains trusted of floating point on both sides: the reference definitions of `Semantics/FpOpsSpec.lean` and
the pins they name (SPEC-NOTES §9 items 13, 21, 22, 30), and `Impl.recipS/D`, `Impl.rsqrtS/D` (bounded by I.8).

**Trusted surface 175 → 211**: the 36 floating-point statements listed in `docs/PROOF-NOTES.md`, "Wave 11".

**Trusted surface 211 → 216** (wave 12b): the five decoder statements named in "The spec's decoder (wave 12b)" above; `docs/PROOF-NOTES.md`, "Wave 12b".
