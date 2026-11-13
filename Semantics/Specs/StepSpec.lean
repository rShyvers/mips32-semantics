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
import Semantics.Specs.MulDiv
import Semantics.Specs.BitOps
import Semantics.Specs.Immediate
import Semantics.Specs.Memory
import Semantics.Specs.Atomic
import Semantics.Specs.Unaligned
import Semantics.Specs.Branch
import Semantics.Specs.BranchLikely
import Semantics.Specs.Jump
import Semantics.Specs.Trap
import Semantics.Specs.Syscall
import Semantics.Specs.Cp0
import Semantics.Specs.FpuCommon
import Semantics.Specs.FpuMove
import Semantics.Specs.FpuControl
import Semantics.Specs.FpuMemory
import Semantics.Specs.FpuArith
import Semantics.Specs.FpuConvert
import Semantics.Specs.FpuCompare
import Semantics.Specs.FpuBranch

/-!
# StepSpec — index of the specification of `step`

This module only imports the spec files; it contains no declaration. `Checked.lean` imports it, so
`lake check` kernel-replays every file below, and `comparator.json` names it as the solution
module that `lake comparator` judges against the statements-only `Semantics/Statements.lean`.

## How to read the statements

Each per-instruction theorem `<ctor>_spec_raw` is an equation `step p s = …` whose right-hand
side is written out with the state primitives (`readReg`, `writeReg`, `readMemWord`, …) and
`Step.lean`'s small helpers. Names ending in `Spec` (`regIdxSpec`, `addOverflowsSpec`, …) are
abbreviations for the real `Step.lean` definitions, not copies (`Defs.lean`).

* `hfetch : fetchWord p s.pc = some w` and `hdecode : decode w = some instr` say "the next
  instruction the simulator runs is `instr`".
* `hpb : s.pendingBranch = none` restricts a theorem to an instruction that is not in a branch
  delay slot. `delay_slot_commits_target` (`DelaySlot.lean`) lifts any such equation to the
  delay-slot case; `exceptionEntry_*` (`Exception.lean`) describe exception entry in both cases.
* Exceptions (overflow, address error, reserved instruction, syscall, breakpoint, trap,
  coprocessor unusable, floating point) appear on right-hand sides as `takeException s code` /
  `takeAddressException s code addr`; `Exception.lean` states exactly what those do.
* FPU theorems carry `hcu : cu1Enabled s = true`; `fp_coprocessor_unusable` (`FpuCommon.lean`)
  covers the other case.

Besides the general statement, most files contain **satisfiable examples** (`#guard`s that run
`step` on a concrete program and state built with `Fixtures.lean`, showing the hypotheses are not
vacuous) and **bad-output rejection** theorems (an outcome a buggy implementation might
plausibly produce, which `step` provably does not). `#guard` rather than `decide` is used
wherever a `Program`/`State.mem` hash map is involved, because those do not reduce in the kernel.

Every theorem is fully proved. Notes on how individual proofs came about are in
`docs/PROOF-NOTES.md`, not here.

## Where things are

| Family | File | What a reviewer should read there |
|---|---|---|
| Statement vocabulary | `Defs.lean` | every definition: they occur in statements |
| Helper lemmas | `Lemmas.lean` | nothing (kernel-checked plumbing) |
| Proof scripts | `Tactics.lean` | the two macros `step_spec` / `fp_step_spec`, once |
| Example fixtures | `Fixtures.lean` | the three builders used by `#guard`s |
| Decode / encode | `WellFormed.lean`, `DecodeSpec.lean` | `Instruction.WellFormed` (field ranges), `decode_encode` (round trip) |
| Exception entry | `Exception.lean` | `exceptionEntry_always`, `_exl0_not_in_delay_slot`, `_exl0_in_delay_slot`, `_exl1`, `_excCode`, `_ce` |
| Fetch / decode failure | `Fetch.lean` | `step_misaligned_pc`, `step_no_instruction`, `step_undecodable`, `step_reserved_instruction` |
| Delay slots | `DelaySlot.lean` | `delay_slot_commits_target`, `branch_in_delay_slot_halts` (the rest is proof device) |
| Invariants | `Invariants.lean` | `step_preserves_zero_register`, `run_preserves_zero_register` (the rest is proof device) |
| Register-file sizes | `RegFileSize.lean` | `step_preserves_wellFormed`, `run_initialState_wellFormed`: the `regs.size = 32` / `fpRegs.size = 32` side conditions are invariants (the rest is proof device) |
| R-type arithmetic / logic | `Arith.lean` | the `_spec_raw` statements; overflow corollaries; `movn`/`movz` not-taken |
| Shifts, rotates | `Shift.lean` | the `_spec_raw` statements; `rotr` is not `srl` |
| Multiply / divide, HI/LO | `MulDiv.lean` | the `_spec_raw` statements; division by zero |
| Bit operations | `BitOps.lean` | `clo`/`clz`/`seb`/`seh`/`wsbh`/`ext`/`ins` statements |
| Immediates | `Immediate.lean` | sign- vs zero-extension of the immediate in each statement |
| Loads / stores | `Memory.lean` | alignment conditions and `AdEL`/`AdES`; sign/zero extension; `sync`/`synci`/`pref` no-ops |
| `ll` / `sc` | `Atomic.lean` | when `sc` succeeds; `LLbit` |
| `lwl`/`lwr`/`swl`/`swr` | `Unaligned.lean` | the big-endian byte selection in each statement |
| Branches | `Branch.lean` | taken / not-taken corollaries; the link register of `bltzal`/`bgezal` |
| Branch-likely | `BranchLikely.lean` | `beql_not_taken_squashes_delay_slot` and the statements |
| Jumps | `Jump.lean` | target computation; `jal_sets_ra`, `jalr_sets_rd` |
| Traps, `break` | `Trap.lean` | the trap condition of each statement |
| `syscall` | `Syscall.lean` | `syscall_spec_raw` (service dispatch) |
| Coprocessor 0 | `Cp0.lean` | `mfc0`/`mtc0` register map and write masks; `eret` |
| FPU, common | `FpuCommon.lean` | `fp_coprocessor_unusable`; `fpCompletes*_trap` / `_ok` |
| FPU moves | `FpuMove.lean` | statements (FCSR untouched) |
| FPU control registers | `FpuControl.lean` | `cfc1`/`ctc1` statements; `fcsr_ctc1_cfc1_roundtrip` |
| FPU loads / stores | `FpuMemory.lean` | alignment and the register pair used for doubles |
| FPU arithmetic | `FpuArith.lean` | which `Mips.Fp` function each instruction applies |
| FPU conversions | `FpuConvert.lean` | which rounding mode each conversion uses |
| FPU compare | `FpuCompare.lean` | `cCondS_spec_raw`, `cCondD_spec_raw`; `c_lt_s_sets_cc` etc.; the meaning of the predicates is in `Semantics/FpCompareFacts.lean` |
| FPU branches | `FpuBranch.lean` | `bc1f`/`bc1t`/`bc1fl`/`bc1tl` statements |

The partition follows the constructor groups of `Instruction` (`Semantics/Instruction.lean`) and
the sections of `docs/spec/INSTRUCTION-REF.md`; each family file's header lists its constructors,
the manual pages and its theorems.
-/
