import Semantics.Specs.WellFormed
import Semantics.Specs.DecodeSpec
import Semantics.Specs.Defs
import Semantics.Specs.Lemmas
import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures
import Semantics.Specs.Exception
import Semantics.Specs.Fetch
import Semantics.Specs.DelaySlot
import Semantics.Specs.Invariants
import Semantics.Specs.RegFileSize
import Semantics.Specs.Arith
import Semantics.Specs.Shift
import Semantics.Specs.BitOps
import Semantics.Specs.Immediate
import Semantics.Specs.Memory
import Semantics.Specs.Atomic
import Semantics.Specs.Branch
import Semantics.Specs.Jump
import Semantics.Specs.Trap
import Semantics.Specs.Syscall
import Semantics.Specs.Cp0
import Semantics.Specs.Mode
import Semantics.Specs.Reset
import Semantics.Specs.FpuCommon
import Semantics.Specs.FpuMove
import Semantics.Specs.FpuControl
import Semantics.Specs.FpuMemory
import Semantics.Specs.FpuArith
import Semantics.Specs.FpuConvert
import Semantics.Specs.SelfModifying
import Semantics.Specs.Mmu
import Semantics.Specs.Loader
import Semantics.Specs.Hosted
import Semantics.Specs.Timer
import Semantics.Specs.Interrupt
-- BEGIN R6-4
import Semantics.Specs.PcRel
-- END R6-4
-- BEGIN R6-3
import Semantics.Specs.CompactBranch
-- END R6-3

/-!
# StepSpec — index of the specification of `step`

This module only imports the spec files; it contains no declaration. `Checked.lean` imports it, so
`lake check` kernel-replays every file below, and `comparator.json` names it as the solution
module that `lake comparator` judges against the statements-only `Semantics/Statements.lean`.

## How to read the statements

Each per-instruction theorem `<ctor>_spec_raw` is an equation `step s = timerTick (…)` whose
argument is the instruction's effect written out with the state primitives (`readReg`, `writeReg`, `readMemWord`, …) and
`Step.lean`'s small helpers. Names ending in `Spec` (`regIdxSpec`, `addOverflowsSpec`, …) are
abbreviations for the real `Step.lean` definitions, not copies (`Defs.lean`).

* `timerTick` (`Step.lean`) is the timer's part of every step: `Count` + 1 unless `Cause.DC = 1`,
  `Cause.TI` set when `Count = Compare`; it changes nothing else (`timerTick_*` in `Lemmas.lean`,
  `Timer.lean`).
* `hfetch : readMemWord s s.pc = some w` and `hdecode : decode w = some instr` say "the word in
  memory at `pc` is `w`, and it decodes to `instr`": `step` fetches from `State.physMem` through the
  MMU (`translate`), so this is the fetch itself (there is no separate program). A misaligned `pc`, or
  a `pc` outside useg in User Mode, makes `readMemWord` `none`.
* `hexec : executesInstr s = true` says that this step executes the instruction at `pc`: no interrupt is
  taken (`interruptTaken`) and the processor is not in standby after `wait`. Otherwise the step is the
  Interrupt exception or a standby step (`Interrupt.lean`: `step_interrupt`, `step_standby_*`).
* `hpb : s.pendingBranch = none` restricts a theorem to an instruction that is not in a branch
  delay slot. `delay_slot_commits_target` (`DelaySlot.lean`) lifts any such equation to the
  delay-slot case; `exceptionEntry_*` (`Exception.lean`) describe exception entry in both cases.
* Exceptions (overflow, address error, reserved instruction, syscall, breakpoint, trap,
  coprocessor unusable, floating point) appear on right-hand sides as `takeException s code` /
  `takeAddressException s code addr`; `Exception.lean` states exactly what those do.
* FPU theorems carry `hcu : cu1Enabled s = true`; `fp_coprocessor_unusable` (`FpuCommon.lean`)
  covers the other case. Coprocessor-0 theorems carry `hcp0 : cp0Usable s = true` (Kernel Mode;
  Release 6 has no `Status.CU0`); `cp0_instruction_user_mode_unusable` (`Cp0.lean`) covers the other case.

Besides the general statement, most files contain **satisfiable examples** (`#guard`s that run
`step` on a concrete program loaded into a state with `Fixtures.lean`, showing the hypotheses are
not vacuous) and **bad-output rejection** theorems (an outcome a buggy implementation might
plausibly produce, which `step` provably does not). `#guard` rather than `decide` is used
wherever a `Program`/`State.physMem` hash map is involved, because those do not reduce in the kernel.

Every theorem is fully proved. Notes on how individual proofs came about are in
`docs/PROOF-NOTES.md`, not here.

## Where things are

| Family | File | What a reviewer should read there |
|---|---|---|
| Statement vocabulary | `Defs.lean` | every definition: they occur in statements |
| Helper lemmas | `Lemmas.lean` | nothing (kernel-checked plumbing) |
| Proof scripts | `Tactics.lean` | the three macros `step_spec` / `fp_step_spec` / `cp0_step_spec`, once |
| Example fixtures | `Fixtures.lean` | the three builders used by `#guard`s |
| Decode / encode | `WellFormed.lean`, `DecodeSpec.lean` | `Instruction.WellFormed` (field ranges), `decode_encode` (round trip) |
| Exception entry | `Exception.lean` | `exceptionEntry_always`, `_exl0_not_in_delay_slot`, `_exl0_in_delay_slot`, `_exl1`, `_excCode`, `_ce` |
| Fetch / decode failure | `Fetch.lean` | `step_misaligned_pc`, `step_fetches_from_memory`, `step_undecodable`, `step_reserved_instruction`, `step_reserved_cop0_unusable` |
| Self-modifying code | `SelfModifying.lean` | `sw_next_instruction_is_fetched`, `store_changes_next_instruction` (and `readMemWord_writeMemWord_alias`) |
| Address translation (Fixed Mapping MMU) | `Mmu.lean` | `fixedMappingPA_*` (each segment, `ERL`, kseg0/kseg1 alias), `translate_*`, the `*_user_kernel_address` Address Errors (every access function, fetch, `lw`, `sw`), `kseg1_store_visible_through_kseg0` |
| Loader | `Loader.lean` | `loadImage_readMemWord`, `load_readMemWord`, `load_step_fetches_image`, `loadAtReset_readMemWord_kseg`, `canonicalVAddr_loadAddr`, `canonicalVAddr_loadAddr_kseg1`, `loadAddr_canonicalVAddr` |
| Delay slots | `DelaySlot.lean` | `delay_slot_commits_target`, `branch_in_delay_slot_reserved_instruction` (the rest is proof device) |
| Invariants | `Invariants.lean` | `step_preserves_zero_register`, `run_preserves_zero_register` (the rest is proof device) |
| Register-file sizes | `RegFileSize.lean` | `step_preserves_wellFormed`, `run_initialState_wellFormed`: the `regs.size = 32` / `fpRegs.size = 32` side conditions are invariants (the rest is proof device) |
| R-type arithmetic / logic | `Arith.lean` | the `_spec_raw` statements; overflow corollaries; the Release 6 `mul`/`muh`/`mulu`/`muhu`, `div`/`mod`/`divu`/`modu` (the zero-divisor pin), `seleqz`/`selnez`, `lsa` |
| Shifts, rotates | `Shift.lean` | the `_spec_raw` statements; `rotr` is not `srl` |
| Bit operations | `BitOps.lean` | `clo`/`clz`/`seb`/`seh`/`wsbh`/`ext`/`ins`/`align`/`bitswap` statements |
| PC-relative (Release 6) | `PcRel.lean` | `addiupc`/`auipc`/`aluipc`/`lwpc`: `PC` is the instruction's own address |
| Immediates | `Immediate.lean` | sign- vs zero-extension of the immediate in each statement |
| Loads / stores | `Memory.lean` | alignment conditions and `AdEL`/`AdES`; sign/zero extension; `sync`/`synci` no-ops; `pref` a no-op or Reserved Instruction (hints 24..31) |
| `ll` / `sc` | `Atomic.lean` | when `sc` succeeds; `LLbit` |
| Branches | `Branch.lean` | taken / not-taken corollaries; the link register of `nal`/`bal` |
| Jumps | `Jump.lean` | target computation; `jal_sets_ra`, `jalr_sets_rd`; the compact jumps `jic`/`jialc` |
| Compact branches (R6-3) | `CompactBranch.lean` | no delay slot; the forbidden slot (`compact_not_taken_forbidden_slot`, `forbidden_slot_cti_reserved`) |
| Traps, `break` | `Trap.lean` | the trap condition of each statement |
| `syscall` | `Syscall.lean` | `syscall_spec_raw` (the System Call exception, always) |
| Hosted run (environment, not architecture) | `Hosted.lean` | `hostStep_eq_step`, `runHosted_agrees_with_run` (where the hosted run differs from `step`); `hostStep_syscall_spec`, `hosted_print_int`, `hosted_exit` (the MARS-style services) |
| Timer, hardware registers | `Timer.lean` | `step_count_advances`, `step_count_stopped` (Count + 1 per step unless `Cause.DC`), `step_timer_match_sets_ti`, `step_timerInt`, `mtc0_compare_clears_ti`, `causeValue_timer`; `rdhwr_spec_raw` and its access rule (`rdhwr_reserved_unimplemented`, `rdhwr_reserved_not_enabled`, `rdhwr_allowed`), `hwrValue_*` |
| Coprocessor 0 | `Cp0.lean` | `mfc0`/`mtc0` register map and write masks; `eret`; `cp0_instruction_user_mode_unusable` |
| Operating modes | `Mode.lean` | `userMode_iff`, `cp0Usable_false_iff`, `exceptionEntry_enters_kernel_mode`, `exception_from_user_mode_enters_kernel_mode`, `eret_to_user_mode` |
| Reset, boot convention | `Reset.lean` | `resetException_spec`, `resetException_keeps`, `resetState_spec`, `hostedStart_is_reset_then_boot` |
| FPU, common | `FpuCommon.lean` | `fp_coprocessor_unusable`; `fpCompletes*_trap` / `_ok` |
| FPU moves | `FpuMove.lean` | statements (FCSR untouched) |
| FPU control registers | `FpuControl.lean` | `cfc1`/`ctc1` statements; `fcsr_ctc1_cfc1_roundtrip` |
| FPU loads / stores | `FpuMemory.lean` | alignment and the register pair used for doubles |
| FPU arithmetic | `FpuArith.lean` | which `Mips.Fp` function each instruction applies |
| FPU conversions | `FpuConvert.lean` | which rounding mode each conversion uses |

<!-- BEGIN R6-2 -->
Release 6 privileged architecture (Wave R6-2): the CP0 layout table (`Cp0.lean`: `cp0ReadAt_eq`,
`cp0WriteAt_eq`, `mfc0_unimplemented_reads_zero`, `mtc0_unimplemented_ignored`, `mfc0_config3/4/5`,
`mfc0_llAddr`, `mtc0_llAddr*`, `cp0_scratch_round_trip`, `cp0Usable_iff_kernelMode`); `eretnc` and
`cache` (`Cp0.lean`: `eretnc_spec_raw`, `eretnc_keeps_llBit`, `cache_spec_raw`, `cache_noop`);
`sigrie` (`Trap.lean`: `sigrie_spec_raw`); `BadInstr`/`BadInstrP` (`Exception.lean`:
`exceptionEntry_badInstr`, `takeInterrupt_badInstr_unchanged`); `rdhwr` 5 and 29 (`Timer.lean`:
`hwrValue_xnp`, `hwrValue_ulr`); reset (`Reset.lean`: `resetException_r6`, `resetState_r6`).
<!-- END R6-2 -->

The partition follows the constructor groups of `Instruction` (`Semantics/Instruction.lean`) and
the sections of `docs/spec/INSTRUCTION-REF.md`; each family file's header lists its constructors,
the manual pages and its theorems.
-/
