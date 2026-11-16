# The independent manual specification (`Semantics/Manual/`) and the refinement of `step`

Target: MIPS32 **Release 6** (little-endian, 64-bit FPU with `Status.FR = 1`, IEEE 754-2008 NaNs, Fixed Mapping MMU, no optional
modules), 203 `Instruction` constructors. Manual revisions (normative, `manuals/`): MD00082 Vol I-A Rev 6.01, MD00086 Vol II-A
Rev 6.06, MD00090 Vol III Rev 6.02; citations are document + revision + instruction/section + PRINTED page.

`Semantics/Manual/` is the manual's pseudocode transcribed, independently of the model (`Semantics/Step.lean`, `Exec/*`).
`Semantics/Refine/` proves that `step` refines it. The independent correctness result is `step_eq_manual`.

Layout of this document. Part I describes the specification as it is now (Release 6). Part II is the guide for transcribing one
Operation. Part III is the design rationale. Part IV is the history of the pre-Release-6 model (Release 2, tag `mips32r2-final`):
its wave records are kept for the reasoning they hold; nothing in Part IV describes the current model, and its constructor counts,
file lists and statement counts are those of that model.

# Part I. The specification (Release 6)

## I.1 Files

`ls Semantics/Manual` and `ls Semantics/Refine` are the authority; the list below says what each file is for.

| File | Contents |
|---|---|
| `Manual/Arch.lean` | `Arch` (the manual's state: `PC`, `GPR`, 32 64-bit `FPR`, `FCSR`, the CP0 registers under the manual's names including the Release 6 `UserLocal`, `BadInstr`, `BadInstrP`, `KScratch1..6`, `Config5.SBRI`, `LLAddr`/`LLbit`; `Mem`; `BranchDelay`; the inputs `HW`, `LowPower`), `Delay` (an `I+1:` effect: `jump`, `fallThrough`, `forbiddenSlot`), `update`, `FCSRWritable`/`FCSRWrite`/`FCSRRead` |
| `Manual/Choices.lean` | `Exception`, `Outcome`, `Impl` (the implementation constants), `Oracle` (one field per place the manual leaves a choice), `Impl.WF`, `modelImpl`, `modelOracle`, `modelImpl_WF`: the pins |
| `Manual/Accuracy.lean` | `FPValue` (Table 6.2 re-transcribed, because `Manual/` may not import `FpOpsSpec`), `ULP`, `WithinULPs`, `Impl.RecipExact`, `Impl.RsqrtAccurate`, `RecipFlagsOK`, `Impl.RecipFlags`, `Impl.Valid` |
| `Manual/Pseudocode.lean` | `Ctx`, `Frame`, `Result`, `Pseudo` (+ `Monad`), `SignalException`, `I1`, `resolve`, `unpredictableOr`, `setPC`, `PC`, `GPR`/`setGPR`, `reg`, `bits`, `bit`, `low`, `sign_extend`, `zero_extend`, `imm16`, `imm9`, `memory_address`. There is no `HI`/`LO`: Release 6 removed them |
| `Manual/CP0.lean` | the Release 6 Status/Cause field readers (`StatusCU1`, `StatusFR`, no `CU0`), `StatusRead`/`StatusWritable`, `KernelMode`, `UserMode`, `CP0Usable`, `CauseRead`/`CauseWritable`, `IntCtlIPTI`, `EBaseRead`, `ConfigRead`, `Config5Read`, `LLAddrRead`, `HWREnaWritable`, `IsCoprocessorRegisterImplemented`, `CPRRead`/`CPRWrite`, `updateKScratch` |
| `Manual/Memory.lean` | `BigEndianMem` (= `false`), `ReverseEndian`, `BigEndianCPU`, `FixedMapping`, `AddressTranslation`, `LoadMemory`/`StoreMemory`, `InstructionFetch` |
| `Manual/FPU.lean` | `FCSR_RM/Enables/FS`, `env`, the shared IEEE rounding core wrapped (`addS` .. `sqrtS`, `D` forms, `toWordS/D`, `toLongS/D`, `cvt*`, `ltS`/`eqS`, `fmaS/D`, `minMaxS/D`, `classS/D`, `rintS/D`), `FP32RegistersMode`, `ValueFPR32/64`, `StoreFPR32/64`, `CheckFPException`, `FPResult` |
| `Manual/Exceptions.lean` | `ExcCode`, `FaultingCoprocessorNumber`, `vectorOffset`, `vectorBase`, `FaultingInstructionWord`, `GeneralExceptionProcessing` (with the Release 6 `BadInstr`/`BadInstrP` and the forbidden slot) |
| `Manual/Interrupts.lean`, `Timer.lean`, `Reset.lean` | `InterruptRequests`/`InterruptTaken`/`LowPowerTime`, `TimerTick`, `ResetException` |
| `Manual/Encoding.lean` | the format diagrams: `fld`, `rFormat`, `iFormat`, `off9Format`, `sa2Format`, `pc19Format`, `encIf`, `enc` (every constructor), `CmpCondnOK`, `opcode`, `InCop0Space`/`InCop1Space`/`InCop2Space`, `UnpredictableEncoding` |
| `Manual/Decode.lean` | the spec's own decoder `Decode`/`decodeDiagram` from `enc` (not the model's `decode`) |
| `Manual/Ops/*.lean` (21 files) | one `def` per manual page: `IntArith`, `Shift`, `BitOps`, `Immediate`, `PcRel`, `Memory`, `Atomic`, `Trap`, `Syscall`, `Branch`, `CompactBranch`, `Jump`, `Cp0`, `System`, `VP` (DVP/EVP), `FpuArith`, `FpuConvert`, `FpuMemory`, `FpuMove`, `FpuControl`, `FpuR6` |
| `Manual/Operation.lean` | `Operation : Instruction → Option (Pseudo Unit)`, one line per constructor |
| `Manual/Cycle.lean` | `IsCTI`, `DecoderSound`, `Execute`, `Undecodable`, `Unpredictable`, `FetchExecute`, `InstructionTime` |
| `Manual/Relation.lean` | `UnpredictableLimits`, `UndefinedOutcomeValid`, `NIValue`/`NIOutcome`, `QNaNValid`, `Oracle.Valid`, `Step`, `InstructionTimes`, `CTC1Unpredictable`, `ConsultsOracle`, `ChoiceFree` (exact) |
| `Refine/Defs.lean` | definitions only (trusted): `memOf`, `abs`, `Good`, `FcsrReservedZero`, `StatusImplemented`, `Inv` |
| `Refine/Abs`, `Bridge`, `BridgeIntAlu`, `BridgeBits`, `BridgeControl`, `BridgeMem`, `BridgeFpu`, `BridgeFpuMove`, `Fetch` | the plumbing: `abs_*` projections, constants, format lemmas, `execute_run`, FPR/FCSR bridges |
| `Refine/<Family>.lean` | `<ctor>_refines`, one per constructor (203): `IntArith`, `Shift`, `BitOps`, `Immediate`, `PcRel`, `Memory`, `Atomic`, `Trap`, `Syscall`, `Branch`, `CompactBranch`, `Jump`, `Cp0`, `System`, `FpuArith`, `FpuConvert`, `FpuMemory`, `FpuMove`, `FpuControl`, `FpuR6` |
| `Refine/Instr.lean` | `InstrRefines`, `instrRefines_<ctor>`, `allInstrRefines` |
| `Refine/Cycle.lean`, `Decode.lean`, `DecodeDiagram.lean`, `DecodeBridge.lean`, `Invariant.lean` | the non-instruction paths (timer, interrupt, standby, fetch error, undecodable word), `decoderSound_decode`, the decoder agreement theorems, preservation of `Inv` |
| `Refine/Step.lean` | TOP: `step_eq_manual`, `step_refines_manual`, `run_refines_manual`, `resetException_refines_manual`, `resetState_refines_manual`, `step_preserves_inv` |
| `Refine/Determinism.lean` | `modelOracle_valid`, `manual_step_deterministic`, `step_unique_of_choiceFree`, `interrupt_choice_exists` |
| `Refine/ChoicePoints.lean` | `operation_choiceFree` and the `cf_<ctor>` lemmas (56) |
| `Refine/ChoiceFp.lean`, `ChoiceWitness.lean`, `ChoiceRows.lean`, `ChoiceRowsFp.lean`, `ChoiceExact.lean` | the other direction: the `rw_<ctor>` row lemmas, `choiceFree_exact`, `choiceFree_iff` |
| `Refine/ImplValid.lean` | `modelImpl_valid` |

**Independence rule.** `scripts/manual_independence.py` (gate step 1, token pre-check) and `scripts/manual_deps.py`
(`scripts/ManualIndependence.lean`, on the elaborated environment) enforce that `Semantics/Manual/*` imports only `Word`, `Types`
(`W32`/`VAddr`/`PAddr`), `Instruction` (constructor names) and `FpOps` (the IEEE rounding core and the listed shared items), and
names no model definition (`decode`, `encode`, `*Mask`, `fpUpdate`, `envOf`, anything of `Step.lean`/`State.lean`/`Exec/*`). Every
constant reached from a `Manual.*` constant must be a `Manual.*` constant, core Lean/Std, `W32`/`VAddr`/`PAddr`, the `Instruction`
type, or an allow-listed item of `FpOps.lean`. The spec classifies NaNs by its own Table 6.2 transcription (`Manual.FPIsNaN` ..).

**The spec's decoder.** `Manual.Decode` decodes by the format diagrams `Manual.enc`; the top theorems take `Manual.decodeDiagram`.
On the trusted surface: `decode_diagram_sound`, `decode_diagram_complete`, `decode_agrees_manual` (where the model's `decode`
accepts, it agrees), `decode_none_manual` (where `decode` rejects a diagram word, the Operation reaches an oracle choice: EXT/INS out
of range), `decoderSound_decodeDiagram`; `decoderSound_decode` for the model's decoder. Proofs: `Refine/DecodeDiagram.lean`,
`Refine/DecodeBridge.lean`. The model's `decode` is `decodeFor profile.release`, one table per release (`Release` has one arm,
`.r6`); the spec's `Manual.enc` is the Release 6 diagrams only.

## I.2 What `abs`, `Inv` and the top theorems say

`Refine.abs : State → Manual.Arch` projects the model state onto the manual's (physical memory as a function). `Refine.Inv s` is
`Good s ∧ FcsrReservedZero s ∧ StatusImplemented s`:

* `Good`: both register files have 32 entries and `$zero` reads 0;
* `FcsrReservedZero s := s.fcsr &&& 0xFEFC0000#32 = 0#32`: the stored FCSR holds only its R/W fields (bits 31..25 and 23..18 read 0 in the
  word; `ABS2008` and `NAN2008` are added on read, Vol I-A Rev 6.01 Table 6.8 p.92-94). `ctc1_refines` and `ctc1_run` assume it
  (the manual writes `FCSRWrite` of a word built from the old FCSR, which drops the non-R/W bits; the model's `writeControl` keeps
  the old ones); `cfc1_refines` takes it but no longer uses it. It is an internal hypothesis of `Refine/`, supplied by `Inv`
  and preserved by `step` (`step_preserves_fcsrReservedZero`), `resetState`, `hostedStart` and `load`; no trusted statement
  was weakened for it;
* `StatusImplemented`: `Status` holds only implemented bits (needed by the Reset refinement).

~~~lean
theorem step_eq_manual (s : State) (hs : Refine.Inv s) :
    Manual.InstructionTime Manual.modelImpl Manual.modelOracle Manual.decodeDiagram (Refine.abs s) =
      some (Refine.abs (step s))
~~~

Also trusted: `step_refines_manual` (`Manual.Step`, the relation over valid oracles), `run_refines_manual` (`n` steps),
`step_unique_of_choiceFree`, `manual_step_deterministic`, `modelOracle_valid`, `modelImpl_valid`, `interrupt_choice_exists`,
`choiceFree_exact`, `resetException_refines_manual`, `resetState_refines_manual`, `step_preserves_inv`, `inv_resetState`,
`inv_hostedStart`, `inv_load`, and the five decoder statements. **What the comparator trusts for them:** `Statements.lean` imports
`Refine/Defs.lean` and through it `Manual/*`; the meaning of the statements rests on the `Manual` definitions, the pins
`modelImpl`/`modelOracle`, `Refine.abs`/`Refine.Inv`, the model (`step`, `run`, `decode`, `resetException`, `resetState`,
`hostedStart`, `load`) and the IEEE core of `FpOps.lean` that `Manual.IEEE.*` wraps. Not their proofs, which the kernel replays.

## I.3 Decisions of the Release 6 spec

1. **`I+1:` representation.** An Operation schedules its `I+1:` statements with `I1 d`, `Delay.jump t | fallThrough | forbiddenSlot`.
   `Complete` turns that into `PC := PC + 4` (the delay or forbidden slot) and `BranchDelay := some t` (taken) or
   `some (branchPC + 8)` (not taken). `BranchDelay.isSome` is `InstructionInBranchDelaySlot`. There is no `nullify`: Release 6
   has no branch-likely instruction, so no slot is ever nullified, and the model has no `nullified` field.
2. **Decoding is a parameter.** `InstructionTime impl oracle dec a` takes the decoder; the spec requires `DecoderSound dec`.
3. **`Operation` is `Option`-valued** for historical reasons; every constructor is `some`, and `step_eq_manual` is stated as
   `... = some (abs (step s))`.
4. **Exceptions keep the partial state.** `Pseudo` keeps the state at `SignalException`, so FCSR.Cause written before
   `CheckFPException` survives (Vol I-A Rev 6.01 §6.7.1 p.99).
5. **Exception entry does not clear `LLbit`** (Release 6): `Manual.GeneralExceptionProcessing` leaves it alone; ERET clears it,
   ERETNC does not (MD00086 Vol II-A Rev 6.06 SC p.347, ERETNC p.179; SC p.350 "Exceptions between the LL and SC cause SC to fail"
   is read with the ERET/ERETNC pages).
6. **Conditions are `Bool`** (`!=`, `==`, `&&`), not `Prop`: `simp` cannot rewrite under a `Decidable` instance and the refinement
   proofs break (Part II, rule 6).
7. **Dependent widths** are written with `low x n` and `++` then `.setWidth`.
8. **Misaligned accesses.** Every misaligned load/store is an Address Error; LL/SC always (D3: Vol I-A Rev 6.01 Appendix B.2
   p.128, "it is permitted for a processor implementation to produce the Address Error exception for all misaligned accesses";
   SC p.349). The Operations check alignment; `Manual/Ops/Memory.lean` documents the pin. Hardware support would be the alternative.
9. **Refinement statement shape.** `Refine.<ctor>_refines (s) (hg : Good s) .. (hw : enc i = some w) :
   Execute modelCtx w i (abs s) = some (abs (execInstr s i))`.

## I.4 Release 6 transcription notes

Each is a reading of the pages; the pin is in `Manual/Choices.lean` or the Operation docstring and in `docs/spec/SPEC-NOTES.md`.
Citations are the corrected ones of the R6-7 re-audit (below, `docs/AUDIT.md` section 1).

**Compact branches and the forbidden slot** (`Manual/Ops/CompactBranch.lean`, 24 constructors). BC and BALC have no delay and
no forbidden slot (BC p.53, BALC p.52). The conditional compact branches (BEQC, BNEC, BLTC, BGEC, BLTUC, BGEUC, BLEZC, BGEZC, BGTZC,
BLTZC, BEQZC, BNEZC, the B*ZALC family, BOVC, BNVC; B<cond>C p.82-85) share `CompactIf cond target_offset`: taken sets `PC`, not taken
schedules `Delay.forbiddenSlot`. The forbidden slot is not an `I+1:` statement of the pages; it comes from the Restrictions (B<cond>C
p.84) and MD00082 Vol I-A Rev 6.01 §5.3.2, p.62: a control transfer instruction in a delay or forbidden slot signals Reserved
Instruction (§5.3.2.1, p.62; BEQ p.72, JALR p.196: "Release 6 implementations are required to signal a Reserved Instruction
exception"). Pin D6: an exception in a forbidden slot reports EPC = the compact branch and `Cause.BD = 1` (Vol I-A §5.3.2.2 p.62;
"StatusBD" there is a misprint for `CauseBD`, Vol III Table 9.52 p.209); Vol III §6.2.3 p.87 and `BadInstrP` p.181 speak only of
a branch delay slot. `BadInstrP` for a forbidden slot is the compact branch word, a permitted value (the spec fixes it instead of
asking `Oracle.badInstrP`, so it is stricter than the manual there). Misprint readings: the B<cond>C Operation p.84 writes
`PC+4+sign_extend(offset)` where p.83 and the encoding define `target_offset` (18/23-bit signed offset, the field shifted left
2): `target_offset` is used (D11); BOVC/BNVC p.107-108 and BC1EQZ/BC1NEZ p.54-55 read the same way. B*ZALC with `rt = 31` is
UNPREDICTABLE (p.78): `Oracle.linkSourceIs31`, pin `.proceed`. The reversed-operand idioms BGTC/BLEC/BGTUC/BLEUC (B<cond>C p.83) are
assembler aliases, not constructors.

**Release 6 integer** (`Ops/IntArith`, `BitOps`, `PcRel`): MUL/MUH/MULU/MUHU, DIV/MOD/DIVU/MODU, SELEQZ/SELNEZ, LSA, ALIGN, BITSWAP,
ADDIUPC, AUIPC, ALUIPC, LWPC. DIV/MOD by zero is UNPREDICTABLE (DIV MOD DIVU MODU p.168-169): `Oracle.divByZero`, the model delivers
dividend / 0 (matches QEMU). ALIGN's Operation (image-only p.39, read in the PDF) writes `tmp_rt_lo` where only `tmp_rs_lo` is defined;
`tmp_rs_lo` is used.

**Release 6 FPU** (`Ops/FpuR6`, `FpuArith`, `FpuConvert`, `FpuControl`): the register file is 32 64-bit FPRs
(`FP32RegistersMode = 1`, Vol I-A §6.4.1 p.84); there are no odd-FPR choice points. A 32-bit result leaves the upper half of the
FPR UNPREDICTABLE (Vol I-A §6.6.2 p.98): `Oracle.fprUpper`. NaNs follow `NAN2008`/`ABS2008` (`FIR = 0x00F30000`, Vol I-A §6.5.1
p.88-89); ABS/NEG are non-arithmetic. New: CMP.condn.S/D (the 22 predicates of Table A.17 p.457; other `condn` values are Reserved
Instruction, CMP p.136), BC1EQZ/BC1NEZ, SEL/SELEQZ/SELNEZ (no FCSR effect, p.368, p.371), fused MADDF/MSUBF (one rounding; the
pages' Operation p.260 has `vfr` and MADDF twice, read as `ft` and MSUBF), MAX/MIN/MAXA/MINA (funct from the diagrams p.262, not
Table A.15), CLASS, RINT, and the L-format conversions. "-2^63-1" printed on the .L and CVT.W pages is read as the Table 6.3 value
(Vol I-A p.82). FS = 1 flushes subnormal inputs and signals Inexact in every non-comparison instruction (§6.7.2.4 p.102; Table 7.9
p.110 lists CLASS, CMP, MAX, MAXA, MIN, MINA as comparisons): `FPResult` and `Impl.RecipFlags` carry it. CFC1 of FRE (`fs = 5`)
raises Reserved Instruction (CFC1 p.129 Restrictions; the page p.130 prints a relational glyph read as `ConfigAR < 2`);
CTC1 of a missing or Release 6 reserved register is Reserved Instruction, and its final `CheckFPException()` runs (p.149-150).

**CP0 Release 6 layout** (`Manual/CP0.lean`, model: `cp0Layout : Release → Nat → Nat → Option Cp0Reg` in `Exec/Cp0.lean`, a table
keyed by (register, select)). `Status` bit 28 is `RW`, not `CU0` (Vol III Table 9.47 p.190, image-only page; §3.5.3 p.23 still
mentions CU0): CP0 is usable in Kernel Mode only. `UserLocal`, `BadInstr`/`BadInstrP` (always implemented, Config3 §9.48 p.246),
`KScratch1..6` (Config4 `KScrExist = 0xFC`, p.255), `LLAddr.LLB`, Config3/4/5 are implemented. MFC0/MTC0 of an unimplemented
register reads 0 / is ignored (MFC0 p.266, MTC0 p.290). Fixed Mapping MMU (D4): TLB registers read 0 and writes are ignored, and
TLBWR/TLBWI/TLBP/TLBR, TLBINV/TLBINVF raise Reserved Instruction (Vol III A.1.3 p.317; TLBINV p.423, TLBINVF p.426). RDHWR 5 (`XNP`)
and 29 (`ULR`). SDBBP/DERET are subsetted out (no EJTAG; Vol I-A §2.4.1 p.31, SDBBP p.361), CACHE is a no-op with no caches (CACHE
p.119), DVP/EVP are no-ops with `Config5.VP = 0` (DVP p.172-173, EVP p.181-182). WAIT transcribes the Release 6 pseudocode
(`interrupt_pending_and_not_masked_out`, WAIT p.442-443). SIGRIE (Config5.SBRI), ERETNC are new.

**Choices pins** (`Manual/Choices.lean`; the R6-7 audit re-checked each, `docs/AUDIT.md`). `Impl`: `CountIncrement = 1` (Vol III §9.27
p.183), `PRId`, `ConfigFixed = 0x8000_0980` (BE = 0, AR = 2 "Release 6", MT = 3 "Fixed Mapping", Table 9.64 p.233-235),
`Config1 = 0x8000_0001`, `Config2 = 0x8000_0000`, `Config3 = 0x8C00_3000` (M, BP, BI, ULRI, RXI), `Config4 = 0x80FC_0000`,
`Config5Fixed = 0x0000_2010` (`XNP = 1`, `LLB = 1`, `DEC = 0`; Table 9.69 p.259-264), `FIR = 0x00F3_0000`, `IntCtl`/`SRSCtl`
constants, `recipS/D`, `rsqrtS/D`. `Impl.WF` states these. `Oracle` fields: `storeClearsLL = true`, `loadClearsLL = false` (with
`Config5.LLB = 1`: a store to the block makes the SC fail, a load does not; the fields take no address, so the spec admits oracles
Release 6 forbids for same-block accesses, a looseness of the spec, not of the model), `causeCE`, `resetUndefined`, `jalrRsIsRd`,
`linkSourceIs31`, `fprUpper`, `ctc1Unpredictable`, `extOutOfRange`, `insLsbAboveMsb`, `unpredictableEncoding`, `ebaseWriteBEV0`,
`cvtQNaNToD/ToS`, `badInstrNoWord`, `badInstrP`, `divByZero`. Fields removed with R2: `absNegNaN`, `fprOddRead/Write`, `mulHILO`,
`divuByZero`. COP2-space words signal Coprocessor Unusable with `CE = 2` (no CP2; Vol III §6.2.22 p.100); QEMU raises Reserved
Instruction, a declared deviation.

**Accuracy** (`Manual/Accuracy.lean`): `Impl.Valid = WF ∧ RecipAccurate ∧ RecipExact ∧ RsqrtAccurate ∧ RecipFlags`, with the 1-ULP
bound of RECIP.fmt (p.336), 2-ULP of RSQRT.fmt (p.343), and, since R6-7, a clause for a flushed subnormal input in `RecipFlagsOK`:
`divZero = true, invalid = false` (Vol I-A Rev 6.01 §6.7.2.4 p.102). `modelImpl_valid` proves it for the model.

## I.5 Choice points: `ConsultsOracle`, `Oracle.Valid`, `ChoiceFree`

`ConsultsOracle ins a` lists, per Operation that reads the oracle, the condition under which the read is reached and its value can
change the result. In Release 6: loads and stores while `LLbit = 1` (and `LWPC`), `CTC1` UNPREDICTABLE arms, `MTC0` of `EBase` with
`BEV = 0`, `EXT`/`INS` out of range, `JALR`/`JALR.HB` with `rs = rd`, B*ZALC with `rt = 31`, every instruction that stores a 32-bit
result into an FPR (`fprUpper`; the `.S` forms, `MTC1`, `LWC1`, the `W` conversions, the Release 6 `.S` forms), `CVT.D.S` of a QNaN,
and DIV/MOD/DIVU/MODU by zero with `rd != 0`. Where it is `false` the Operation's run is the same under every oracle
(`Refine.operation_choiceFree`). `ChoiceFree` is false at an interrupt, at every exception other than Coprocessor Unusable (its
`Cause.CE` "is loaded, but not defined", Vol III §6.2.3 p.87), at a word with an UNPREDICTABLE field value whose coprocessor is
usable, at a CTI in a delay or forbidden slot, and at a `ConsultsOracle` row. `choiceFree_exact` (trusted) proves the other
direction: where `ChoiceFree = false`, two valid oracles give different instruction times.

`Oracle.Valid` formalizes the three restrictions of MD00086 Vol II-A Rev 6.06 §1.2.1 (p.3-4): non-interference in User Mode
(`NIValue`/`NIOutcome` over `AccessibleSame`), the inaccessible state unchanged, no halt; the UNDEFINED fields held to §1.2.2 (p.4);
`QNaNValid` (MD00082 Vol I-A §6.3.1.5 p.82); a Reset changes registers only; and the model-side strengthening that no UNPREDICTABLE or
UNDEFINED outcome changes the hardware interrupt inputs `HW` (Vol III Table 6.2 p.73; `IP7..IP2` read-only, Table 9.52 p.211).

**Spec looser or stricter than the manual (recorded, not a bug in the model).** Looser: the same-block LL/SC oracle fields above.
Stricter: `BadInstrP` in a forbidden slot (above). Each is also in `docs/AUDIT.md` section 1.

## I.6 Validation

`lake exe EquivHarness` (gate step 6) runs every `tests/corpus` and `tests/oracle` program hosted and compares, on every state,
`Manual.InstructionTime modelImpl modelOracle decode (abs s)` with `abs (step s)`. The gate also runs the corpus (29 programs, valid
Release 6, against MARS), the QEMU/LLVM oracle (`qemu-system-mipsel -cpu mips32r6-generic`, 184 oracle tests at R6-7 including the
runnable `tests/asm` programs, 176 of them `tests/oracle/*.asm`; every constructor must be executed by some oracle program, 203/203)
and `Semantics/Tests/ManualTests.lean` `#guard`s. MARS cannot run Release 6; it is a differential oracle only for corpus programs that are
valid in Release 6.

# Part II. Transcribing an Operation (guide)

## II.1 Rules

1. **One `def` per manual page**, in `Semantics/Manual/Ops/<Family>.lean`, `namespace Manual.Ops`, named by the mnemonic (`ADD`,
   `ADD_S` for `ADD.fmt` with fmt S, `CMP_condn_S`, ..). Add the arm to `Manual.Operation` and the format line to `Manual.enc`.
2. **Docstring**: `**MNEMONIC operands** — MD00086 Vol II-A Rev 6.06, MNEMONIC, p.N.` followed by the page's Operation pseudocode
   verbatim in a code block, then any Restrictions sentence the Lean implements, with its page. Look every page up with
   `python3 manuals/mipsdoc.py insn MNEMONIC`; image-only pages are read from the PDF and say so. The page number is the PRINTED page.
3. **Pseudocode lines as comments**: each Lean statement is preceded by the manual line it implements.
4. **Vocabulary** (`Manual/Pseudocode.lean` etc.; nothing else from the model):
   * registers: `GPR (reg rs)` (read; r0 reads 0), `setGPR (reg rd) v`, `PC`, `setPC v` (time `I`), `I1 (.jump t)` /
     `I1 .fallThrough` / `I1 .forbiddenSlot` (time `I+1`);
   * fields of the raw instruction: `reg w : Fin 32`, `imm16 w`, `imm9 w`, `w.toNat` for `rd`/`sel`;
   * bit strings: `bits x hi lo`, `bit x k`, `low x n`, `a ++ b`, `BitVec.fill n b`, `BitVec.ofBool b`, `sign_extend v`,
     `zero_extend v`, `memory_address`;
   * exceptions: `SignalException .IntegerOverflow` etc. (`Manual.Exception`; Address Error carries the failing address);
   * memory: `AddressTranslation vAddr .DATA .LOAD|.STORE`, `LoadMemory`, `StoreMemory`, `BYTE`/`HALFWORD`/`WORD`;
   * FPU: `ValueFPR32/64`, `StoreFPR32/64`, `FPResult (IEEE.op a x y)` for every arithmetic result (Cause, CheckFPException,
     Flags);
   * CP0: the field readers of `Manual/CP0.lean`, `CPRRead`, `CPRWrite`, `IsCoprocessorRegisterImplemented`;
   * UNPREDICTABLE / UNDEFINED: read a field of `Pseudo.oracle` and `resolve` it; add the field to `Oracle` with the manual
     sentence, its model choice to `modelOracle` with the SPEC-NOTES pin, and a `ConsultsOracle` row (the build tells you).
5. **Never** name a model definition (`readReg`, `execBody`, `decode`, masks, `fpUpdate`, ..); gate step 1 rejects it.
6. **Write conditions as `Bool`** (`if x != 0#2 then`), not `Prop` (`≠`).
7. **Coprocessor Unusable and CTI-in-slot** are not in the Operation: `Cycle.Execute` does them from the word's encoding space and
   from `IsCTI`.
8. Run `lake exe EquivHarness` after each family: every mismatch is investigated (spec bug: fix the transcription; model bug:
   SPEC-NOTES entry with the reproducer, fix the model).

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
(ADD's test `≠` between two `Bool`s predates rule 6; new code writes `!=`.) Refinement: `Refine.add_refines`
(`Refine/IntArith.lean`): the 33-bit overflow test is the model's `addOverflows` (`add_ovf`), the low 32 bits are `x + y`.

## II.3 Worked example 2: BEQC (MD00086 Vol II-A Rev 6.06, B<cond>C, p.82-85)

~~~lean
/-- **BEQC rs, rt, offset** — B<cond>C, p.82-85. -/
def BEQC (rs rt offset : W32) : Pseudo Unit := do
  let target_offset := sign_extend (imm16 offset ++ 0#2)
  -- BEQC: cond ← GPR[rs] = GPR[rt]
  let cond := (← GPR (reg rs)) == (← GPR (reg rt))
  CompactIf cond target_offset
~~~
`CompactIf cond target_offset` is `if cond then setPC (PC + 4 + target_offset) else ForbiddenSlot`: taken sets `PC` at once
(compact branches have no delay slot), not taken schedules the forbidden slot (`Delay.forbiddenSlot`, see I.4). Refinement:
`Refine.beqc_refines` (`Refine/CompactBranch.lean`).

# Part III. Design rationale

* **A function with an explicit choice argument, and a relation on top.** `Manual.InstructionTime impl oracle dec : Arch → Option Arch`
  is deterministic once the oracle is given and runs, so it can be tested against `step` on the corpus before any proof work;
  `Manual.Step impl dec a a' := ∃ o, o.Valid ∧ InstructionTime impl o dec a = some a'` allows every outcome the manual permits.
* **`Impl` and `Oracle`.** `Impl` holds the fixed constants of one implementation (Count rate, PRId, Config registers, FIR, the
  reciprocal approximations); `Oracle` has one field per place the manual allows several outcomes, typed by what it is asked.
  `modelImpl`/`modelOracle` are the model's instance, each field a one-line pin citing SPEC-NOTES.
* **`Pseudo`** is `ReaderT (Impl × Oracle) (StateT Arch (Except Signal))`, so `SignalException` aborts the instruction as
  MD00086 §2.2.2.5.1 p.26 says.
* **Why `abs`.** `State.physMem` is a `Std.HashMap`; two maps built in a different order are not equal values, so the statement is
  about `abs s`, with memory as a function. Reason about `abs`, not the `State` record: rewrite through the `abs_*` and bridge lemmas.
* **One theorem per constructor**, closed by one macro-style script; the top theorem does `cases instr` and closes each case with
  `Refine.<ctor>_refines`, so no large `match` is elaborated. No `decide` on `BitVec`, no default `simp` set, no `bv_decide`.
* **What the model and the manual share.** Only the IEEE rounding core of `FpOps.lean`, proved against `FpOpsSpec.lean` (see Part IV
  and `docs/PROOF-NOTES.md`); FCSR Cause/Flags/Enables and `CheckFPException` are transcribed again (Vol I-A §6.7.1 p.99, Vol II-A p.23).

# Part IV. History of the Release 2 model (tag `mips32r2-final`)

Everything below describes the pre-Release-6 model (183 constructors, big-endian, 32-bit FPU, legacy NaNs, branch-likely, HI/LO), as
built in waves 7A-12b. The wave-8 to wave-11 choice and FP machinery survives in Release 6 in changed form (Part I); the
constructor, row and statement counts and the file names below are those of the old model. Pre-Release-6 pages cited here
(for example BEQL p.73) are the Rev 6.06 pages of instructions Release 6 removed. The original plan document (a 150-line
design handed to the 7B agents, with its R2-specific section on branch-likely) is not reproduced.

## IV.1 Decisions of 7A (R2)

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


## IV.2 Validation at 7A (R2)

`lake exe EquivHarness` (gate step 6) runs every `tests/corpus` and `tests/oracle` program hosted and
compares, on every state, `Manual.InstructionTime modelImpl modelOracle decode (abs s)` with
`abs (step s)` field by field (memory: bytes the model wrote and the aligned word at a pilot load or
store). Result at the end of 7A: 183 programs, 10012 states compared, 0 mismatches, 47813 states
skipped (instruction not transcribed). A deliberate spec bug (`BEQL` not nullifying) is caught (1
mismatch, `tests/oracle/branch_likely_not_taken.asm`). `Semantics/Tests/ManualTests.lean` has
`#guard`s on concrete states.

## IV.3 Review fixes (Wave 7R, R2)

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

## IV.4 The cycle refinement (Wave 7D, R2)

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

## IV.5 Wave 8: exact choice points, the third UNPREDICTABLE restriction, RECIP accuracy

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

## IV.6 Wave 9: `ChoiceFree` is exact (proved), three rows refined, test robustness

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

## IV.7 Wave 10: the IEEE core proved; `RECIP`/`RSQRT` against the exact result

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


## IV.8 Wave 11: the shared FP core proved on every operand

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
