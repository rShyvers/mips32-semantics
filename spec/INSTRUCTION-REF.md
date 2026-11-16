# MIPS32 Release 2 Instruction Reference

This document is the per-instruction reference for the instruction set modeled by
`Semantics/` (179 constructors of `Instruction`; the generated matrix is
[`docs/TRACE.md`](../TRACE.md), the compact coverage table is in the root `README.md`).
It began as a reference for ~24 instructions and 4 syscalls grounded in the MARS 4.5 source;
the sections that were written against MARS say so and cite MARS source files, and every
section added later is grounded in the manuals instead. Where MARS deviates from the
architecture, or where a source is ambiguous, the entry says so rather than normalizing it away.

**Citation convention.** A manual citation gives document, revision, instruction or section,
and the *printed* page, e.g. "MD00086 Vol II-A Rev 6.06, MUL, p.299". File names such as
`mars/mips/instructions/InstructionSet.java` or `mars/simulator/Simulator.java` are pointers into the
MARS 4.5 source tree, which is **not vendored** in this repository (only the jar,
`vendor/mars/Mars4_5.jar`, is); line numbers refer to MARS 4.5's own files and cannot be re-checked here
without that source.

> **Exception model — read this first.** Entries below that were written
> against MARS describe overflow, misaligned access and unknown instructions
> as MARS `ProcessingException`s that "halt". In the Lean model these are
> **architectural exceptions**, not halts: see *Global rule 6* and the
> *Coprocessor 0 / traps and exceptions* section. The processor (`step`) never
> halts; only the hosted run (`Semantics/Env.lean`, not part of the
> architecture) stops, with `exit`, `unhandledException` or `noInstruction`.
> **Normative text:** the latest published manuals, read for a
> pre-Release-6 MIPS32 processor with the Release 2 feature set — MD00086
> Vol II-A Rev 6.06, MD00090 Vol III Rev 6.02 and MD00082 Vol I-A Rev 6.01,
> extracted to text under `manuals/` by `fetch.sh` (the PDFs and texts are not committed). Manual citations give
> document, revision, instruction or section, and printed page.

Conventions pinned elsewhere and assumed here (see
[`SPEC-NOTES.md`](SPEC-NOTES.md)): one real-MIPS32 branch delay slot per
branch/jump (not MARS's default `DelayedBranching=false` no-delay-slot
config — see Global rule 3); execution starts at `0x00400000`; big-endian
memory; 32 GPRs plus separate 64-bit `hi`/`lo` pair (internally registers
33/34); `$zero` write-ignored.

All MARS line numbers below refer to `mars/mips/instructions/InstructionSet.java` (MARS 4.5 source, not
vendored) unless otherwise noted; the `simulate()` method body for each instruction is the
MARS-side execution logic (method `populate()`, lines 77–3236).

## Where each family is specified and proved

Every constructor has a primary theorem `<ctor>_spec_raw` (or `<ctor>_spec`) in
`Semantics/Specs/<Family>.lean`; the index and the reading guide are in
`Semantics/Specs/StepSpec.lean`, and the instruction-by-instruction table with line links is the
generated [`docs/TRACE.md`](../TRACE.md). The primary theorems, by file (as listed by `python3 scripts/trace.py`):

| Spec file | Primary theorems |
|---|---|
| `Semantics/Specs/Arith.lean` | `add_spec_raw`, `addu_spec_raw`, `sub_spec_raw`, `subu_spec_raw`, `and_spec_raw`, `or_spec_raw`, `xor_spec_raw`, `nor_spec_raw`, `slt_spec_raw`, `sltu_spec_raw`, `movn_spec_raw`, `movz_spec_raw` |
| `Semantics/Specs/Shift.lean` | `sll_spec_raw`, `srl_spec_raw`, `sra_spec_raw`, `sllv_spec_raw`, `srlv_spec_raw`, `srav_spec_raw`, `rotr_spec_raw`, `rotrv_spec_raw` |
| `Semantics/Specs/MulDiv.lean` | `mult_spec_raw`, `multu_spec_raw`, `div_spec_raw`, `divu_spec_raw`, `mflo_spec_raw`, `mfhi_spec_raw`, `mthi_spec_raw`, `mtlo_spec_raw`, `mul_spec_raw`, `madd_spec_raw`, `maddu_spec_raw`, `msub_spec_raw`, `msubu_spec_raw` |
| `Semantics/Specs/BitOps.lean` | `clo_spec_raw`, `clz_spec_raw`, `seb_spec_raw`, `seh_spec_raw`, `wsbh_spec_raw`, `ext_spec_raw`, `ins_spec_raw` |
| `Semantics/Specs/Immediate.lean` | `addi_spec_raw`, `addiu_spec_raw`, `slti_spec_raw`, `sltiu_spec_raw`, `andi_spec_raw`, `ori_spec_raw`, `xori_spec_raw`, `lui_spec_raw` |
| `Semantics/Specs/Memory.lean` | `lw_spec_raw`, `sw_spec_raw`, `lb_spec_raw`, `lbu_spec_raw`, `lh_spec_raw`, `lhu_spec_raw`, `sh_spec_raw`, `sb_spec_raw`, `synci_spec_raw`, `sync_spec_raw`, `pref_spec_raw` |
| `Semantics/Specs/Atomic.lean` | `ll_spec_raw`, `sc_spec_raw` |
| `Semantics/Specs/Unaligned.lean` | `lwl_spec_raw`, `lwr_spec_raw`, `swl_spec_raw`, `swr_spec_raw` |
| `Semantics/Specs/Branch.lean` | `beq_spec_raw`, `bne_spec_raw`, `blez_spec_raw`, `bgtz_spec_raw`, `bltz_spec_raw`, `bgez_spec_raw`, `bltzal_spec_raw`, `bgezal_spec_raw` |
| `Semantics/Specs/BranchLikely.lean` | `beql_spec_raw`, `bnel_spec_raw`, `blezl_spec_raw`, `bgtzl_spec_raw`, `bltzl_spec_raw`, `bgezl_spec_raw`, `bltzall_spec_raw`, `bgezall_spec_raw` |
| `Semantics/Specs/Jump.lean` | `jr_spec_raw`, `jalr_spec_raw`, `j_spec_raw`, `jal_spec_raw` |
| `Semantics/Specs/Trap.lean` | `teqi_spec_raw`, `tnei_spec_raw`, `tgei_spec_raw`, `tgeiu_spec_raw`, `tlti_spec_raw`, `tltiu_spec_raw`, `teq_spec_raw`, `tne_spec_raw`, `tlt_spec_raw`, `tge_spec_raw`, `tltu_spec_raw`, `tgeu_spec_raw`, `break_spec_raw` |
| `Semantics/Specs/Syscall.lean` | `syscall_spec_raw` |
| `Semantics/Specs/Cp0.lean` | `mfc0_spec_raw`, `mtc0_spec_raw`, `di_spec_raw`, `ei_spec_raw`, `eret_spec_raw`, `wait_spec_raw`, `rdpgpr_spec_raw`, `wrpgpr_spec_raw` |
| `Semantics/Specs/Interrupt.lean` | the Interrupt exception (`step_interrupt`, `interruptTaken_iff`, `takeInterrupt_*`, `interruptVector_*`), its sources, standby after `wait` (`step_standby_*`), `IntCtl`/`SRSCtl` (`mfc0_intctl_spec`, `mfc0_srsctl_spec`, `mtc0_*_ignored`) |
| `Semantics/Specs/Timer.lean` | `rdhwr_spec_raw`; the timer: `step_count_advances`, `step_count_stopped`, `step_timer_match_sets_ti`, `step_timerInt`, `mtc0_count_spec`, `mtc0_compare_clears_ti` |
| `Semantics/Specs/FpuMove.lean` | `mfc1_spec_raw`, `mtc1_spec_raw`, `mfhc1_spec_raw`, `mthc1_spec_raw`, `movS_spec_raw`, `movD_spec_raw`, `movfS_spec_raw`, `movtS_spec_raw`, `movfD_spec_raw`, `movtD_spec_raw`, `movnS_spec_raw`, `movzS_spec_raw`, `movnD_spec_raw`, `movzD_spec_raw`, `movf_spec_raw`, `movt_spec_raw` |
| `Semantics/Specs/FpuControl.lean` | `cfc1_spec_raw`, `ctc1_spec_raw` |
| `Semantics/Specs/FpuMemory.lean` | `lwc1_spec_raw`, `swc1_spec_raw`, `ldc1_spec_raw`, `sdc1_spec_raw`, `lwxc1_spec_raw`, `ldxc1_spec_raw`, `swxc1_spec_raw`, `sdxc1_spec_raw`, `prefx_spec_raw` |
| `Semantics/Specs/FpuArith.lean` | `addS_spec_raw`, `subS_spec_raw`, `mulS_spec_raw`, `divS_spec_raw`, `sqrtS_spec_raw`, `absS_spec_raw`, `negS_spec_raw`, `recipS_spec_raw`, `rsqrtS_spec_raw`, `addD_spec_raw`, `subD_spec_raw`, `mulD_spec_raw`, `divD_spec_raw`, `sqrtD_spec_raw`, `absD_spec_raw`, `negD_spec_raw`, `recipD_spec_raw`, `rsqrtD_spec_raw`, `maddS_spec_raw`, `msubS_spec_raw`, `nmaddS_spec_raw`, `nmsubS_spec_raw`, `maddD_spec_raw`, `msubD_spec_raw`, `nmaddD_spec_raw`, `nmsubD_spec_raw` |
| `Semantics/Specs/FpuConvert.lean` | `roundWS_spec_raw`, `truncWS_spec_raw`, `ceilWS_spec_raw`, `floorWS_spec_raw`, `cvtWS_spec_raw`, `cvtDS_spec_raw`, `cvtSW_spec_raw`, `cvtDW_spec_raw`, `roundWD_spec_raw`, `truncWD_spec_raw`, `ceilWD_spec_raw`, `floorWD_spec_raw`, `cvtWD_spec_raw`, `cvtSD_spec_raw` |
| `Semantics/Specs/FpuCompare.lean` | `cCondS_spec_raw`, `cCondD_spec_raw` |
| `Semantics/Specs/FpuBranch.lean` | `bc1f_spec_raw`, `bc1t_spec_raw`, `bc1fl_spec_raw`, `bc1tl_spec_raw` |

Global (not per-instruction) statements: `Semantics/Specs/DecodeSpec.lean` (`decode_encode`),
`Invariants.lean` (`$zero`), `RegFileSize.lean`, `Exception.lean`, `Fetch.lean`, `DelaySlot.lean`,
`FpuCommon.lean` (Coprocessor Unusable, FP trap), `Cp0.lean` (`cp0_instruction_user_mode_unusable`),
`Mode.lean` (Kernel/User Mode), `Reset.lean` (Reset exception, `resetState`, hosted boot convention),
`Mmu.lean` (Fixed Mapping translation, User-Mode Address Errors, kseg0/kseg1 aliasing), `Loader.lean`
(the loader places every image word where fetch and loads find it),
`FpuControl.lean` (`fcsr_ctc1_cfc1_roundtrip`),
`FpuCompare.lean` and `Semantics/FpCompareFacts.lean` (compare predicates). These theorems restate what
`step` computes in terms of the model's own helpers; see `docs/PROOF-NOTES.md` and the README section
"What is proved, what is tested, what is trusted" for what that does and does not establish.

## Assembler syntax added after the original scope

The assembler (`Semantics/Asm.lean`) accepts GNU-as operand order. Forms below were assembled by
`lake exe MipsRun` while writing this section; `Semantics/Tests/AsmTests.lean` holds the encodings and
`tests/oracle/encodings.list` is compared word for word with `llvm-mc` by `scripts/oracle.py --encodings`.

| Form | Syntax | Notes |
|---|---|---|
| Condition codes | `c.lt.s $fcc3, $f2, $f4`; `c.eq.d $f2, $f4` | all sixteen predicates `c.<cond>.s/.d`; `$fccN` or a bare `N`; `cc` defaults to 0 |
| FP branches | `bc1t 2, label`, `bc1f label`, `bc1tl`, `bc1fl` | optional leading `cc`; delay slot is never filled |
| Conditional moves | `movf $t0, $t1, 2`, `movt`; `movt.d $f2, $f4, 1`; `movn.s $f2, $f4, $t0`, `movz.fmt` | `cc` optional, default 0 |
| Code operands | `break 1, 2`; `syscall 5`; `teq $t0, $t1, 3` (all six register traps); `sync 4`; `wait 5` | `break c1[, c2]`: each 0..1023, `c1` in bits 25..16, `c2` in bits 15..6 (GNU as; SPEC-NOTES §9 item 15); `syscall` 0..0xFFFFF; trap codes 0..1023; `sync` 0..31; `wait` 0..0x7FFFF |
| CP0 select | `mfc0 $t0, $12, 1`; `mtc0 $t0, $12` | `sel` 0..7, default 0 |
| Indexed FP memory | `lwxc1 $f2, $t0($t1)`, `ldxc1`, `swxc1`, `sdxc1`, `prefx 1, $t0($t1)` | `index(base)` with two registers |
| High half moves | `mfhc1 $t0, $f2`, `mthc1` | |
| Multiply-add | `madd.s $f0, $f2, $f4, $f6` (`fd, fr, fs, ft`), `msub`, `nmadd`, `nmsub` (`.s`, `.d`) | |
| Other FP | `recip.s`, `rsqrt.d`, `round.w.d`, `trunc.w.d`, `ceil.w.d`, `floor.w.d`, `cfc1`, `ctc1`, `mfc1`, `mtc1`, `ldc1`, `sdc1` | doubles name the even register of the pair; evenness is not checked by the assembler |
| Integer additions | `pref 4, 8($t0)`, `di`, `ei $t0`, `sb`, `rotr`, `rotrv`, `ext rt, rs, pos, size`, `ins`, `seb`, `seh`, `wsbh` | `di`/`ei` take an optional `rt` |
| Hazard idioms | `ssnop`, `ehb`, `pause`, `nal`, `jr.hb rs`, `jalr.hb rd, rs` | `ssnop`/`ehb`/`pause` assemble to `sll $0,$0,1` / `sll $0,$0,3` / `sll $0,$0,5` (decoded as `sll`; PAUSE: MD00086 Vol II-A Rev 6.06 p.317); `nal` to `bltzal $0,0` = `0x04100000` (NAL p.306) |
| Pseudo-instructions | `b`, `bal`, `beqz`, `bnez`, `neg`, `negu`, `not`, `abs`, `blt/bge/bgt/ble` (+`u`), `li`, `la`, `move`, `nop` | the `blt` family expands through `$at`; none inserts a delay-slot `nop` |
| Directives | `.text .data .ktext .kdata`, `.word .half .byte .float .double .ascii .asciiz .space .align`, `.globl`, `.set noreorder/noat/at` | `.set reorder` is rejected |

`pause` and `nal` take no operands; SPEC-NOTES §9 item 16 explains how their encodings decode.

---


## Summary table

| Mnemonic | Format | One-line semantics |
|---|---|---|
| `add` | R | `$rd = $rs + $rt`, signed; traps on signed overflow |
| `addu` | R | `$rd = $rs + $rt`, wraps, never traps |
| `sub` | R | `$rd = $rs - $rt`, signed; traps on signed overflow |
| `subu` | R | `$rd = $rs - $rt`, wraps, never traps |
| `and` | R | `$rd = $rs & $rt` |
| `or` | R | `$rd = $rs \| $rt` |
| `xor` | R | `$rd = $rs ^ $rt` |
| `nor` | R | `$rd = ~($rs \| $rt)` |
| `sll` | R | `$rd = $rt << shamt` (logical, zero-fill) |
| `srl` | R | `$rd = $rt >> shamt` (logical, zero-fill) |
| `sra` | R | `$rd = $rt >> shamt` (arithmetic, sign-fill) |
| `slt` | R | `$rd = ($rs < $rt) ? 1 : 0`, signed compare |
| `sltu` | R | `$rd = ($rs < $rt) ? 1 : 0`, unsigned compare |
| `mult` | R | `{hi,lo} = $rs * $rt`, signed 64-bit product |
| `multu` | R | `{hi,lo} = $rs * $rt`, unsigned 64-bit product |
| `div` | R | `lo = $rs / $rt`, `hi = $rs % $rt`, signed; no-op on `$rt == 0` |
| `divu` | R | `lo = $rs / $rt`, `hi = $rs % $rt`, unsigned; no-op on `$rt == 0` |
| `mflo` | R | `$rd = lo` |
| `mfhi` | R | `$rd = hi` |
| `addi` | I | `$rt = $rs + sext16(imm)`, traps on signed overflow |
| `addiu` | I | `$rt = $rs + sext16(imm)`, wraps, never traps |
| `slti` | I | `$rt = ($rs < sext16(imm)) ? 1 : 0`, signed compare |
| `sltiu` | I | `$rt = ($rs < sext16(imm)) ? 1 : 0`, unsigned compare on sign-extended imm |
| `andi` | I | `$rt = $rs & zext16(imm)` |
| `ori` | I | `$rt = $rs \| zext16(imm)` |
| `xori` | I | `$rt = $rs ^ zext16(imm)` |
| `lui` | I | `$rt = imm << 16` (low 16 bits zero) |
| `lw` | I | `$rt = MEM32[$rs + offset]`, word-aligned |
| `sw` | I | `MEM32[$rs + offset] = $rt`, word-aligned |
| `lb` | I | `$rt = sext8(MEM8[$rs + offset])` |
| `lbu` | I | `$rt = zext8(MEM8[$rs + offset])` |
| `lh` | I | `$rt = sext16(MEM16[$rs + offset])`, halfword-aligned |
| `lhu` | I | `$rt = zext16(MEM16[$rs + offset])`, halfword-aligned |
| `sh` | I | `MEM16[$rs + offset] = $rt[15:0]`, halfword-aligned |
| `j` | J | `PC = (PC_next & 0xF0000000) \| (target << 2)` |
| `jal` | J | `$ra = PC_next; PC = (PC_next & 0xF0000000) \| (target << 2)` |
| `beq` | I-branch | `if ($rs == $rt) PC = PC_next + (offset << 2)` |
| `bne` | I-branch | `if ($rs != $rt) PC = PC_next + (offset << 2)` |
| `blez` | I-branch | `if ($rs <= 0) PC = PC_next + (offset << 2)` |
| `bgtz` | I-branch | `if ($rs > 0) PC = PC_next + (offset << 2)` |
| `bltz` | I-branch (REGIMM) | `if ($rs < 0) PC = PC_next + (offset << 2)`, signed |
| `bgez` | I-branch (REGIMM) | `if ($rs >= 0) PC = PC_next + (offset << 2)`, signed |
| `bltzal` | I-branch (REGIMM) | `$ra = PC_next + 4` unconditionally; `if ($rs < 0) PC = PC_next + (offset << 2)` |
| `bgezal` | I-branch (REGIMM) | `$ra = PC_next + 4` unconditionally; `if ($rs >= 0) PC = PC_next + (offset << 2)` |
| syscall 1 | — | print signed decimal integer in `$a0` |
| syscall 4 | — | print null-terminated byte string starting at address `$a0` |
| syscall 10 | — | terminate program normally |
| syscall 11 | — | print low byte of `$a0` as a character |
| `teq` | R | `if ($rs == $rt) trap` |
| `tne` | R | `if ($rs != $rt) trap` |
| `tlt` | R | `if ($rs < $rt) trap`, signed |
| `tge` | R | `if ($rs >= $rt) trap`, signed |
| `tltu` | R | `if ($rs < $rt) trap`, unsigned |
| `tgeu` | R | `if ($rs >= $rt) trap`, unsigned |
| `break` | R | unconditional trap |
| `teqi` | I-branch (REGIMM) | `if ($rs == sext16(imm)) trap`, signed |
| `tnei` | I-branch (REGIMM) | `if ($rs != sext16(imm)) trap`, signed |
| `tgei` | I-branch (REGIMM) | `if ($rs >= sext16(imm)) trap`, signed |
| `tgeiu` | I-branch (REGIMM) | `if ($rs >= sext16(imm)) trap`, unsigned compare on sign-extended imm |
| `tlti` | I-branch (REGIMM) | `if ($rs < sext16(imm)) trap`, signed |
| `tltiu` | I-branch (REGIMM) | `if ($rs < sext16(imm)) trap`, unsigned compare on sign-extended imm |
| `mfc0` | R (COP0) | `$rt = ` CP0 register `(rd, sel)` (modeled registers only); CpU (CE 0) when CP0 is not usable |
| `mtc0` | R (COP0) | CP0 register `(rd, sel)` `:= $rt`, through its write mask; CpU (CE 0) when CP0 is not usable |
| `di` | R (COP0) | `$rt = Status; Status.IE := 0`; CpU (CE 0) when CP0 is not usable |
| `ei` | R (COP0) | `$rt = Status; Status.IE := 1`; CpU (CE 0) when CP0 is not usable |
| `eret` | R (COP0) | `PC := EPC; Status.EXL := 0` (or `ErrorEPC`/`ERL` when `Status.ERL = 1`) — no delay slot; CpU (CE 0) when CP0 is not usable |
| `wait` | R (COP0) | completes (`PC_next`) and enters standby: the following steps only advance `Count` until an interrupt request restarts the processor (an enabled one is taken with `EPC` = the instruction after `wait`); CpU (CE 0) when CP0 is not usable |
| `rdpgpr` | R (COP0, Release 2) | `$rd ← SGPR[SRSCtl.PSS, rt]` = `$rt` (only shadow set 0 exists, `SRSCtl.HSS = 0`); CpU (CE 0) when CP0 is not usable |
| `wrpgpr` | R (COP0, Release 2) | `SGPR[SRSCtl.PSS, rd] ← $rt`, i.e. `$rd ← $rt`; CpU (CE 0) when CP0 is not usable |
| `rdhwr` | R (SPECIAL3) | `$rt = HWR[rd]` for `rd` 0 `CPUNum` (0), 1 `SYNCI_Step` (0), 2 `CC` (`Count`), 3 `CCRes` (1), if CP0 is usable or `HWREna` bit `rd` is set; RI otherwise and for every other `rd` (MIPS32 Release 2) |
| `ll` | I | `$rt = MEM32[$rs + offset]`, word-aligned; sets `llBit`, records the address in `llAddr` |
| `sc` | I | if `llBit` and the address equals `llAddr` in bits 31..2: `MEM32[$rs + offset] = $rt`, `$rt := 1`; else `$rt := 0`; clears `llBit` either way |
| `pref` | I | no-op; never raises an exception |

`PC_next` denotes the program counter value *after* the fetched instruction
has been accounted for, i.e. `PC_at_fetch + 4` — see Global rule 1.

The coprocessor-1 instructions have their own table ("Encoding summary" in
the "Floating point (coprocessor 1)" section); the other later additions
have a table at the head of their section.

Pseudo-instructions (`li`, `la`, `move`, `nop` as written by the user, `ble`,
`bge`, etc.) are assembler sugar expanded per
`PseudoOps.txt` (MARS 4.5 source, not vendored); they are **not** documented here as machine
instructions.

---

## Global rules

### 1. PC update timing and per-class behavior

Source: `mars/simulator/Simulator.java`, lines 325–327
(fetch/increment loop) and `InstructionSet.java` lines 3265–3303
(`processBranch`, `processJump`, `processReturnAddress`).

- The simulator fetches the instruction at the current PC, **then
  increments PC by 4** (`RegisterFile.incrementPC()`, line 327), **then**
  calls `simulate()`. So by the time any instruction's semantics run, `PC`
  already holds the address of the sequentially-next instruction
  (`PC_next` in this document).
- **Non-control-flow instructions** (arith/logic/mem): PC is left at
  `PC_next`; execution continues there.
- **Branches** (`beq`,`bne`,`blez`,`bgtz`): the *target address formula* is
  `PC = PC_next + (displacement << 2)` (`InstructionSet.java` line ~3272,
  `processBranch`; `displacement` is the instruction's signed 16-bit offset
  field) — standard MIPS branch-target arithmetic, PC-relative to the
  instruction *after* the branch, scaled by 4. **Our semantics overrides
  MARS's *timing* of when this target is applied**: real MIPS32 always
  executes one delay-slot instruction first (see rule 3), so a taken branch
  *schedules* this target rather than jumping to it immediately (MARS's
  default `DelayedBranching=false` path jumps immediately instead; we do
  not follow that part of MARS).
- **Jumps** (`j`,`jal`): the *target address formula* is
  `targetAddress = (PC_next & 0xF0000000) | (target_field << 2)`
  (`InstructionSet.java` lines ~1207–1211, 1238–1240) — the top 4 bits come
  from `PC_next`, not from the jump instruction's own address. As with
  branches, our semantics *schedules* this target via the delay slot (rule
  3) rather than applying it immediately.
- **Link instructions** (`jal`): the address-*formula* source
  (`processReturnAddress(31)`, `InstructionSet.java` lines 3309–3315) sets
  `$ra = PC_next` only when delayed branching is disabled (MARS's default).
  **Our semantics does not follow that**: since we always execute one
  delay-slot instruction, `$ra` must be `PC_next + 4` (`pc + 8` relative to
  `jal`'s own address) — the address *after* the delay slot — matching real
  MIPS32, not MARS's no-delay-slot default (see rule 3).

### 2. `$zero` is write-ignored

Source: `mars/mips/hardware/RegisterFile.java`,
`updateRegister(int num, int val)`, lines 95–119: when `num == 0` the method
takes the empty branch and returns `old = 0` without touching the register
array. Reads of register 0 always return `0` (it is initialized to 0 and
never written). Every instruction below that writes `$rd`/`$rt` is silently
a no-op if that operand is `$zero`.

### 3. Branch/jump delay slots (real MIPS32 semantics)

Ground truth: the real MIPS32 architecture (not MARS). Every branch and
jump — `beq bne blez bgtz bltz bgez bltzal bgezal j jal jr jalr bc1f bc1t`
and the taken branch-likely forms (including `bc1fl`/`bc1tl`) — has exactly
**one** delay slot: the
instruction immediately following it always executes, **whether or not the
branch is taken**, before control transfers.

Model (`Semantics/Step.lean`, `State.pendingBranch : Option W32`):
`pendingBranch = some t` *means* "the instruction at `pc` is in a delay
slot, and control goes to `t` after it".

- **Every branch/jump** moves to `pc + 4` and sets `pendingBranch`:
  **taken** → the real target; **not taken** → the fall-through address
  `pc + 8`. (Recording the not-taken case too is what lets exception entry
  set `EPC`/`Cause.BD` correctly for an instruction after a not-taken
  branch.)
- **The delay-slot instruction** (any non-control-transfer instruction)
  executes normally and its step commits the pending target to `pc`
  (`advance`/`mkNext`). StepSpec: `advance_in_delay_slot`,
  `execInstr_delay_slot`, `beq_taken_delay_slot_lands_on_target`.
- **If the delay-slot instruction raises an exception**, the pending target
  is abandoned, `EPC ←` the branch's address and `Cause.BD ← 1` (Global
  rule 6).
- **`jal`'s `$ra`** is `pc + 8` (past the delay slot), not `pc + 4`.
- **A control-transfer instruction in a delay slot** — any of the 12
  branches/jumps, the 8 branch-likelies, `bc1f`/`bc1t`/`bc1fl`/`bc1tl`,
  `eret` or `wait` (`isBranchLike`, 28 instructions). The architecture makes this
  UNPREDICTABLE for branches/jumps (MD00086 Rev 6.06 "BEQ", p. 72) and
  UNDEFINED for `eret` ("ERET", p. 177) and `wait` ("WAIT", p. 442).
  **Model pin:** `step` raises **Reserved Instruction**, taken in the delay
  slot (`EPC` = the branch, `Cause.BD = 1`), uniformly after taken *and*
  not-taken branches (StepSpec: `branch_in_delay_slot_reserved_instruction`).
  Justification: "UNPREDICTABLE operations may cause arbitrary exceptions"
  and "must not halt or hang the processor" (MD00086 §1.2.1, p.3-4);
  UNDEFINED operations "must not cause the processor to hang" (§1.2.2, p.4);
  Release 6 requires exactly this exception (MD00082 Vol I-A Rev 6.01
  §5.3.2.1, p.62). SPEC-NOTES §9 item 1.
- **Branch-likely, not taken**: the delay-slot instruction is nullified;
  see the "Branch likely" section.

This **overrides MARS's own default configuration**
(`mars/mips/instructions/InstructionSet.java`,
`processBranch`/`processJump`, lines 3265–3306, gated on
`Globals.getSettings().getDelayedBranchingEnabled()`;
`mars/Settings.java`'s `DelayedBranching` defaults to
`false`), under which a taken branch/jump updates `PC` to the target
*immediately*, with no delay-slot instruction executed at all. MARS is only
ever used by this project as a differential-testing oracle, not as the spec
source (`SPEC-NOTES.md` §9 item 1); on this point we deliberately diverge
from MARS's default to match the real architecture instead. (MARS *can*
model delay slots if `DelayedBranching` is enabled, which would then agree
with this rule — but that MARS setting is not why we implement it this
way.)

### 4. Big-endian load/store byte order

**The model is big-endian** (the classic MIPS convention): for a word at
address `A`, `A` holds bits `[31:24]`, `A+1` holds `[23:16]`, `A+2` holds
`[15:8]`, `A+3` holds `[7:0]`; halfwords likewise (`State.lean`
`readMemWord`/`writeMemWord`/`readMemHalf`/`writeMemHalf`).

**MARS 4.5 is LITTLE-endian by default** —
`mars/mips/hardware/Memory.java:90`,
`private static boolean byteOrder = LITTLE_ENDIAN;`, and `setByteOrder` is
never called in headless use. (An earlier version of this rule read the
`Memory.java` header comment "purely big-endian" as describing observable
behavior; that was wrong. See `SPEC-NOTES.md` §9 item 4.) This is a pinned
divergence: byte-order-sensitive probes (e.g. `lb` of one byte of a
`.word`) differ between MARS and this model by design, so the differential
corpus uses only endian-invariant access patterns.

### 5. Alignment requirements per access size

- Word access (`lw`, `sw`, `ll`, `sc`, `lwc1`, `swc1`, `lwxc1`, `swxc1`,
  instruction fetch): address must be a multiple of 4.
- Doubleword access (`ldc1`, `sdc1`, `ldxc1`, `sdxc1`): address must be a
  multiple of 8 (MD00086 Vol II-A Rev 6.06, LDC1 p.215, SDC1 p.362).
- Halfword access (`lh`, `lhu`, `sh`): address must be a multiple of 2.
- Byte access (`lb`, `lbu`, `sb`) and `lwl`/`lwr`/`swl`/`swr`: no
  requirement. `pref`/`prefx`/`synci` access no memory.
- A violation raises **Address Error** (and so does a kernel-segment reference from User Mode,
  Global rule 5a) — `AdEL` (ExcCode 4) for a load or
  an instruction fetch, `AdES` (ExcCode 5) for a store — with
  `BadVAddr ←` the failing address (MD00090 Vol III Rev 6.02 §6.2.9
  "Address Error Exception", p.92-93; Table 9.53, p.212). The destination
  register / memory is not written. (Like every exception entry, it
  clears `LLbit`.)

### 5a. Address translation and the User-Mode address check (the memory model)

Every address an instruction computes (`pc`, `base + offset`, `base + index`) is a **virtual**
address. The model's MMU is the Fixed Mapping MMU (`Config.MT = 3`; MD00090 Vol III Rev 6.02
Appendix A.1, p.313-317; SPEC-NOTES §9 item 27), applied by `translate` (`State.lean`) inside the six
`readMem*`/`writeMem*` functions — the manual's `AddressTranslation(vAddr, IorD, LorS)` (MD00086
Vol II-A Rev 6.06 §2.2.2.2.2, p.19). Instruction fetch, loads and stores use the same translation:

| Virtual range | Segment | From User Mode | Physical address (Kernel Mode) |
|---|---|---|---|
| `0x0000_0000`-`0x7FFF_FFFF` | useg/kuseg | legal | `VA + 0x4000_0000` (`Status.ERL = 0`), `VA` (`ERL = 1`) |
| `0x8000_0000`-`0x9FFF_FFFF` | kseg0 | Address Error | `VA - 0x8000_0000` |
| `0xA000_0000`-`0xBFFF_FFFF` | kseg1 | Address Error | `VA - 0xA000_0000` (same 512 MB as kseg0) |
| `0xC000_0000`-`0xDFFF_FFFF` | kseg2 (sseg/ksseg) | Address Error | `VA` |
| `0xE000_0000`-`0xFFFF_FFFF` | kseg3 | Address Error | `VA` |

(Table 4.1 p.28, Table 4.2 p.30, Table 4.3 p.31, Table A.1 p.313-314.) A reference to a kernel segment
from User Mode raises **Address Error** — AdEL for a load or an instruction fetch, AdES for a store —
with `BadVAddr ←` the virtual address, exactly like a misalignment ("A reference is made to a kernel
address space from User Mode", §6.2.9, p.92-93); nothing is read or written. This applies to every
load/store family including `lb`/`lbu`/`sb` (which cannot misalign), `lwl`/`lwr`/`swl`/`swr`, `ll`/`sc`
and the FP loads/stores; it does not apply to `pref`/`prefx` ("PREF does not cause addressing-related
exceptions", PREF p.321) or `synci` (its kernel-address AdEL is "implementation dependent", SYNCI p.412;
the model raises none). The Fixed Mapping MMU raises no TLB exception (there is no TLB) and the model's
memory system raises no Bus Error (every physical byte exists; unwritten bytes read 0). Physical memory
is `State.physMem`; kseg0 and kseg1 alias it (`kseg1_store_visible_through_kseg0`).

### 6. Exceptions are state transitions, not halts

Integer Overflow (`add`/`addi`/`sub`, ExcCode 12), Address Error (4/5),
Reserved Instruction (a word `decode` rejects, ExcCode 10), Coprocessor
Unusable (11), Floating Point (15), System Call (`syscall`, always,
ExcCode 8), Breakpoint (`break`, 9) and Trap (13) all go through the general
exception sequence (`Step.lean` `exceptionEntry`; details and manual
citations in the "Coprocessor 0 / traps and exceptions" section). `step`
returns the state at the exception vector; it has no halting case.

The hosted run (`Semantics/Env.lean`; an environment convention, not the
architecture, SPEC-NOTES §9 item 25) stops with a `HaltReason`:

| `HaltReason` | When |
|---|---|
| `exit` | hosted service 10: a `syscall` with `$v0 = 10` |
| `unhandledException code epc badVAddr` | `pc` is the exception vector with `Status.EXL = 1` and the loaded image has no word there — "an exception was taken and no handler was loaded". Carries `Cause.ExcCode`, `EPC`, `BadVAddr`. |
| `noInstruction pc` | an aligned `pc` outside the loaded image (ran off the program), other than the case above |

**Instruction fetch reads `State.physMem`** (`readMemWord s s.pc`, through the MMU, Global rule 5a), the memory
loads and stores use: a store to the instruction stream changes what is
executed (self-modifying code works; MD00086 Vol II-A Rev 6.06, SYNCI,
p.412), and a load from a text address sees the instruction word. Memory
that was never written reads as 0 (a pin, SPEC-NOTES §9 item 6).

**Strict decoding (a model pin).** `decode` accepts only canonical
encodings: a word with a nonzero must-be-zero field does not decode and
raises Reserved Instruction (or Coprocessor Unusable, for a word in a
coprocessor's encoding space — see the floating-point section). The manual
does not mandate this: a nonzero reserved field makes the instruction
UNPREDICTABLE (MD00086 Vol II-A Rev 6.06 §2.1.1, p.12), and UNPREDICTABLE
operations "may cause arbitrary exceptions" (p.3) — Reserved Instruction is
the model's pinned choice among the legal outcomes. Software fields are **carried in the constructors**, so
they round-trip exactly: `syscall code` and `break code` (20 bits, 25..6),
`teq`/`tne`/`tlt`/`tge`/`tltu`/`tgeu rs rt code` (10 bits, 15..6),
`sync stype` (bits 10..6), `wait code` (19 bits, 24..6: "A value of zero for
code bits is the default and must be valid in all implementations", MD00086
Vol II-A Rev 6.06, WAIT, p.442), `mfc0`/`mtc0 rt rd sel`, and the `cc`
fields of the FP compares, conditional moves and branches. There is **no
tolerated don't-care field** (since 7R): the `hint` field of `jr`/`jalr`
(bits 10..6) is 0 for `jr`/`jalr`, `10000` for `jr.hb`/`jalr.hb` (their own
constructors), and any other value does not decode. `sll` with `rd = 0` (`nop`/`ssnop`/`ehb`) is an
ordinary `sll`. UNPREDICTABLE encodings (`clz`/`clo` with `rt ≠ rd`, `ext`
with `lsb+msbd > 31`, `ins` with `msb < lsb`) are rejected too. `mfc0`/
`mtc0` decode only with bits 10..3 zero and a modeled `(rd, sel)`. Round
trip: `Semantics/Specs/DecodeSpec.lean` (`decode_encode`,
`decode_wellFormed`).

---

## R-type arithmetic / logic

### add (R)
- **Encoding**: `opcode=000000`, `funct=100000` (0x20). Fields:
  `000000 sssss ttttt fffff 00000 100000` → `rs=sssss`($t2/src1),
  `rt=ttttt`($t3/src2), `rd=fffff`($t1/dest), `shamt=00000`.
- **Semantics**: `sum = $rs + $rt` computed as 32-bit signed Java `int`
  addition. If `$rd != $zero`, write `sum` to `$rd`. No memory access, no
  hi/lo update. PC already advanced to `PC_next` (rule 1); unaffected
  otherwise.
- **Errors/halts**: overflow check: `(rs>=0 && rt>=0 && sum<0) ||
  (rs<0 && rt<0 && sum>=0)` → throws `ProcessingException` with message
  `"arithmetic overflow"` and code `Exceptions.ARITHMETIC_OVERFLOW_EXCEPTION`
  (12). **Model:** raises Integer Overflow (ExcCode 12, Global rule 6);
  `$rd` is not written (MD00086 "ADD": "the destination register is not
  modified and an Integer Overflow exception occurs").
- **MARS note**: none — matches textbook MIPS (`add` traps on signed
  overflow; this is a deliberate design point of real MIPS too, not a MARS
  deviation).
- **Source**: `InstructionSet.java`, `add` instruction object, lines 94–116.

### addu (R)
- **Encoding**: `opcode=000000`, `funct=100001` (0x21). Same field layout as
  `add`.
- **Semantics**: `$rd = $rs + $rt` with plain Java `int` addition
  (two's-complement wraparound on overflow, no check). If `$rd == $zero`,
  write is discarded.
- **Errors/halts**: none from this instruction.
- **MARS note**: none — matches textbook MIPS (`addu` never traps).
- **Source**: `InstructionSet.java`, lines 163–177.

### sub (R)
- **Encoding**: `opcode=000000`, `funct=100010` (0x22). Fields:
  `rs=sssss`($t2/minuend), `rt=ttttt`($t3/subtrahend), `rd=fffff`($t1/dest).
- **Semantics**: `dif = $rs - $rt` (32-bit signed). If `$rd != $zero`, write
  `dif`.
- **Errors/halts**: overflow check: `(rs>=0 && rt<0 && dif<0) ||
  (rs<0 && rt>=0 && dif>=0)` → `ProcessingException("arithmetic overflow",
  ARITHMETIC_OVERFLOW_EXCEPTION)`. **Model:** raises Integer Overflow
  (ExcCode 12); `$rd` is not written.
- **MARS note**: none — matches textbook MIPS (traps on signed overflow).
- **Source**: `InstructionSet.java`, lines 117–139.

### subu (R)
- **Encoding**: `opcode=000000`, `funct=100011` (0x23).
- **Semantics**: `$rd = $rs - $rt`, plain wraparound subtraction, no check.
- **Errors/halts**: none.
- **MARS note**: none — matches textbook MIPS.
- **Source**: `InstructionSet.java`, lines 178–192.

### and (R)
- **Encoding**: `opcode=000000`, `funct=100100` (0x24). `rs=sssss`($t2),
  `rt=ttttt`($t3), `rd=fffff`($t1).
- **Semantics**: `$rd = $rs & $rt`, bitwise, no overflow concept.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 448–462.

### or (R)
- **Encoding**: `opcode=000000`, `funct=100101` (0x25).
- **Semantics**: `$rd = $rs | $rt`.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 463–477.

### xor (R)
- **Encoding**: `opcode=000000`, `funct=100110` (0x26).
- **Semantics**: `$rd = $rs ^ $rt`.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 525–539.

### nor (R)
- **Encoding**: `opcode=000000`, `funct=100111` (0x27).
- **Semantics**: `$rd = ~($rs | $rt)` (bitwise NOR, full 32-bit complement).
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 510–524.

### sll (R)
- **Encoding**: `opcode=000000`, `funct=000000`. Fields:
  `000000 00000 sssss fffff ttttt 000000` → `rs=00000`(unused),
  `rt=sssss`($t2/src), `rd=fffff`($t1/dest), `shamt=ttttt`(5-bit immediate
  shift amount, 0–31).
- **Semantics**: `$rd = $rt << shamt` using Java `<<` on `int` (logical
  left shift, zero-fills low bits). The shift amount is the 5-bit `sa`
  field (`s ← sa`, MD00086 Vol II-A Rev 6.06, SLL p.376): `step` shifts by
  `shamt mod 32` (7R; `srl`, `sra`, `rotr` likewise), which `decode` always
  produces below 32.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 556–569.

### srl (R)
- **Encoding**: `opcode=000000`, `funct=000010` (0x02). Same layout as
  `sll`.
- **Semantics**: `$rd = $rt >>> shamt` — Java `>>>` is used explicitly
  (comment: "must zero-fill"), i.e. logical shift right, zero-fill.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 586–600.

### sra (R)
- **Encoding**: `opcode=000000`, `funct=000011` (0x03). Same layout as
  `sll`.
- **Semantics**: `$rd = $rt >> shamt` — Java `>>` is used explicitly
  (comment: "must sign-fill"), i.e. arithmetic shift right, sign-extend.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 601–614.

### slt (R)
- **Encoding**: `opcode=000000`, `funct=101010` (0x2a). `rs=sssss`($t2),
  `rt=ttttt`($t3), `rd=fffff`($t1).
- **Semantics**: `$rd = ($rs < $rt) ? 1 : 0`, using signed Java `int`
  comparison (`<`).
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 991–1007.

### sltu (R)
- **Encoding**: `opcode=000000`, `funct=101011` (0x2b). Same layout.
- **Semantics**: `$rd = ($rs <u $rt) ? 1 : 0`. Implemented via explicit
  sign-based case split rather than Java unsigned compare intrinsics: if
  both operands are non-negative or both negative, compare directly with
  `<`; otherwise the non-negative one is unsigned-smaller
  (`first >= 0 ? 1 : 0`). This is a correct hand-rolled unsigned-less-than
  on 32-bit two's-complement values.
- **Errors/halts**: none.
- **MARS note**: none — result is equivalent to a true unsigned compare.
- **Source**: `InstructionSet.java`, lines 1008–1030.

---

## Multiply / divide

### mult (R)
- **Encoding**: `opcode=000000`, `funct=011000` (0x18). Fields:
  `000000 fffff sssss 00000 00000 011000` → `rs=fffff`($t1/operand0),
  `rt=sssss`($t2/operand1); `rd`/`shamt` unused (always 0).
- **Semantics**: `product = (int64)$rs * (int64)$rt` computed as a signed
  64-bit Java `long` product of the two sign-extended 32-bit operands.
  `hi` (register 33) = high-order 32 bits of `product`; `lo` (register 34) =
  low-order 32 bits. No GPR is written.
- **Errors/halts**: none; MARS never traps on multiply overflow (there is no
  overflow concept — the full 64-bit result is always captured in hi:lo).
- **MARS note**: none — matches textbook MIPS (`mult` does not trap).
- **Source**: `InstructionSet.java`, lines 208–224.

### multu (R)
- **Encoding**: `opcode=000000`, `funct=011001` (0x19). Same layout.
- **Semantics**: both operands are zero-extended to 64 bits (`<<32>>>32` on
  the `long` cast) before multiplying; `hi:lo` = unsigned 64-bit product,
  split the same way as `mult`.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 225–240.

### div (R)
- **Pin (divide by zero).** MD00086 Rev 6.06 "DIV" (p. 165): "If the
  divisor in GPR rt is zero, the arithmetic result value is
  UNPREDICTABLE"; "No arithmetic exception occurs under any
  circumstances." Leaving `HI`/`LO` unchanged is the model's pinned choice
  of that UNPREDICTABLE result (it is also what MARS does); the same holds
  for `divu`.
- **Encoding**: `opcode=000000`, `funct=011010` (0x1a). Fields:
  `000000 fffff sssss 00000 00000 011010` → `rs=fffff`($t1/dividend),
  `rt=sssss`($t2/divisor).
- **Semantics**: if `$rt != 0`: `hi (reg 33) = $rs % $rt` (signed Java `%`,
  remainder takes the sign of the dividend); `lo (reg 34) = $rs / $rt`
  (signed Java `/`, truncating toward zero). Both are ordinary 32-bit
  signed operations; no overflow check even for the `INT_MIN / -1` edge
  case (Java `int` division wraps `Integer.MIN_VALUE / -1` back to
  `Integer.MIN_VALUE`, matching two's-complement wraparound, and this is
  passed through silently).
- **Errors/halts**: **if `$rt == 0`, the method returns immediately without
  writing `hi` or `lo` at all** — they retain whatever value they held
  before the instruction executed. No exception is thrown.
- **MARS note**: **DEVIATION / explicit source comment.** The source
  contains an explicit comment at this exact spot: *"Note: no exceptions
  and undefined results for zero div. COD3 Appendix A says 'with overflow'
  but MIPS 32 instruction set specification says 'no arithmetic exception
  under any circumstances'."* MARS follows the MIPS32 spec reading here,
  not the Patterson & Hennessy (COD3) "divide with overflow" framing many
  textbooks use. A `Exceptions.DIVIDE_BY_ZERO_EXCEPTION` constant (value 15)
  exists in `mars/simulator/Exceptions.java` (line 63) but
  is **never thrown** by `div`/`divu` — it is dead/vestigial code. Decision
  for the Lean spec: model `div`/`divu` by zero as **hi/lo unchanged, no
  halt**, matching this source exactly.
- **Source**: `InstructionSet.java`, lines 341–367 (zero-check and comment
  at lines ~352–358).

### divu (R)
- **Encoding**: `opcode=000000`, `funct=011011` (0x1b). Same layout as
  `div`.
- **Semantics**: operands are zero-extended to 64-bit `long` first
  (`<<32>>>32`); if divisor `!= 0`: `hi = (unsigned $rs) % (unsigned $rt)`,
  `lo = (unsigned $rs) / (unsigned $rt)`, each truncated back to 32 bits via
  `(int)(... << 32 >> 32)`.
- **Errors/halts**: same as `div` — if `$rt == 0`, returns with hi/lo
  unchanged, no exception.
- **MARS note**: same DEVIATION as `div` — no exception on zero divisor;
  see `div` entry above for the exact source comment.
- **Source**: `InstructionSet.java`, lines 368–391.

### mfhi (R)
- **Encoding**: `opcode=000000`, `funct=010000` (0x10). Fields:
  `000000 00000 00000 fffff 00000 010000` → `rd=fffff`($t1/dest); `rs`,
  `rt` fields unused (must be 0 for this exact match-mask).
- **Semantics**: `$rd = hi` (register 33). No flags, no PC effect beyond
  normal advance.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 392–405.

### mflo (R)
- **Encoding**: `opcode=000000`, `funct=010010` (0x12). Same layout as
  `mfhi` with `rd=fffff`.
- **Semantics**: `$rd = lo` (register 34).
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 406–419.

---

## I-type immediate arithmetic / logic

### addi (I)
- **Encoding**: `opcode=001000` (0x08). Fields:
  `001000 sssss fffff tttttttttttttttt` → `rs=sssss`($t2/src),
  `rt=fffff`($t1/dest), `imm=tttt...`(16-bit field, operand index 2).
- **Semantics**: `imm16 = (operand << 16) >> 16` — Java sign-extension
  of the low 16 bits to 32 bits. `sum = $rs + imm16` (signed 32-bit add).
  If `$rt != $zero`, write `sum`.
- **Errors/halts**: same overflow test as `add`
  (`(rs>=0 && imm16>=0 && sum<0) || (rs<0 && imm16<0 && sum>=0)`) →
  `ProcessingException("arithmetic overflow", ARITHMETIC_OVERFLOW_EXCEPTION)`.
  **Model:** raises Integer Overflow (ExcCode 12); `$rt` is not written.
- **MARS note**: none — matches textbook MIPS (`addi` traps on signed
  overflow).
- **Source**: `InstructionSet.java`, lines 140–162.

### addiu (I)
- **Encoding**: `opcode=001001` (0x09). Same field layout as `addi`.
- **Semantics**: `$rt = $rs + sext16(imm)`, plain wraparound, no check.
  (Despite the "u" suffix, the immediate **is** sign-extended — only the
  overflow-trap behavior differs from `addi`, exactly as in real MIPS.)
- **Errors/halts**: none.
- **MARS note**: none — matches textbook MIPS (`addiu` sign-extends the
  immediate but never traps; this is the standard, sometimes-surprising,
  real-hardware behavior, not a MARS-specific quirk).
- **Source**: `InstructionSet.java`, lines 193–207.

### andi (I)
- **Encoding**: `opcode=001100` (0x0c). Fields:
  `001100 sssss fffff tttttttttttttttt` → `rs=sssss`(src), `rt=fffff`(dest),
  `imm=tttt...`.
- **Semantics**: `$rt = $rs & (imm & 0x0000FFFF)` — immediate is
  **zero-extended** (masked with `0x0000FFFF`), not sign-extended; comment
  in source explicitly states this.
- **Errors/halts**: none.
- **MARS note**: none — matches textbook MIPS (`andi` zero-extends).
- **Source**: `InstructionSet.java`, lines 478–493.

### ori (I)
- **Encoding**: `opcode=001101` (0x0d). Same layout as `andi`.
- **Semantics**: `$rt = $rs | (imm & 0x0000FFFF)`, zero-extended immediate.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 494–509.

### xori (I)
- **Encoding**: `opcode=001110` (0x0e). Same layout as `andi`.
- **Semantics**: `$rt = $rs ^ (imm & 0x0000FFFF)`, zero-extended immediate.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 540–555.

### lui (I)
- **Encoding**: `opcode=001111` (0x0f). Fields:
  `001111 00000 fffff ssssssssssssssss` → `rs=00000`(unused, fixed 0),
  `rt=fffff`($t1/dest), `imm=ssss...`(operand index 1).
- **Semantics**: `$rt = imm << 16` (Java `int` left shift; low 16 bits of
  `$rt` become 0, high 16 bits become the 16-bit immediate). No sign
  extension of the immediate is applied before the shift (none is needed —
  shifting left by 16 discards any sign-extended high bits anyway).
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 845–857.

### slti (I)
- **Encoding**: `opcode=001010` (0x0a). Fields:
  `001010 sssss fffff tttttttttttttttt` → `rs=sssss`(src), `rt=fffff`(dest),
  `imm=tttt...`.
- **Semantics**: `$rt = ($rs < sext16(imm)) ? 1 : 0`, signed comparison.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 1032–1049.

### sltiu (I)
- **Encoding**: `opcode=001011` (0x0b). Same layout as `slti`.
- **Semantics**: the 16-bit immediate is **sign-extended** first
  (`operands[2] << 16 >> 16`, explicit in source), *then* the comparison
  `$rs <u imm32` is performed unsigned (same hand-rolled case-split as
  `sltu`). This matches real MIPS: `sltiu`'s "u" affects only the
  comparison, not the immediate's extension.
- **Errors/halts**: none.
- **MARS note**: none — this is standard, if easily misremembered, real
  MIPS behavior (immediate sign-extended even for the "unsigned" compare),
  not a MARS-specific deviation.
- **Source**: `InstructionSet.java`, lines 1050–1073.

---

## Memory access

### lw (I)
- **Encoding**: `opcode=100011` (0x23). Fields:
  `100011 ttttt fffff ssssssssssssssss` → `base=ttttt`($t2, operand index
  2), `rt=fffff`($t1/dest, operand index 0), `offset=ssss...`(operand index
  1).
- **Semantics**: `addr = $base + offset`; `$rt = MEM32[addr]` (4 bytes,
  big-endian — see Global rule 4), full 32-bit word including sign.
- **Errors/halts**: `addr % 4 != 0` → `AddressErrorException` ("fetch
  address not aligned on word boundary", `ADDRESS_EXCEPTION_LOAD`).
  **Model:** raises AdEL (ExcCode 4), `BadVAddr = addr` (Global rule 5).
- **MARS note**: **SOURCE AMBIGUITY, decision-relevant.** The `simulate()`
  body computes `addr` as `RegisterFile.getValue(operands[2]) + operands[1]`
  with **no explicit sign-extension** of `operands[1]`
  (contrast `lb`/`lh`/`lhu`/`lbu`/`sh`/`addi`/`slti` which all do
  `operands[1 or 2] << 16 >> 16` inline). For instructions built by the
  assembler from source text, `operands[1]` already carries the correctly
  signed Java `int` value of the offset token (see
  `ProgramStatement.buildBasicStatementFromBasicInstruction`,
  `mars/ProgramStatement.java` lines ~245–300), so this is
  invisible in normal assembled-and-run programs. But for instructions
  constructed by decoding a raw 32-bit encoding
  (`ProgramStatement(int binaryStatement, int textAddress)`,
  `ProgramStatement.java` lines 102–146), **only the I_BRANCH_FORMAT's
  3rd operand is sign-extended at decode time** (line 132); a plain
  `I_FORMAT` offset field (as used by `lw`/`sw`) is left as a raw unsigned
  0–65535 value. Combined with `lw`'s lack of an inline sign-extend, a
  negative word offset decoded straight from a 32-bit encoding would be
  treated as a large positive offset by MARS's own source — unlike `lb`,
  `lh`, etc., which defensively re-extend inline and so get it right either
  way. **We could not resolve from source whether this is an intentional
  simplification (offsets are always non-negative in practice for `lw`/`sw`
  generated code) or a latent bug; the Lean `step` function must pick one
  behavior explicitly (uniform sign-extension for all I-format
  loads/stores, matching `lb`/`lh`, is recommended for consistency) rather
  than silently inheriting this asymmetry.**
- **Source**: `InstructionSet.java`, lines 648–668 (`simulate()` body at
  659–667); decode path `ProgramStatement.java` lines 102–146, especially
  126–136.

### sw (I)
- **Encoding**: `opcode=101011` (0x2b). Same field layout as `lw`, with
  `rt=fffff`($t1/source register to store, operand index 0).
- **Semantics**: `addr = $base + offset`; `MEM32[addr] = $rt` (4 bytes,
  big-endian).
- **Errors/halts**: `addr % 4 != 0` → `AddressErrorException` ("store
  address not aligned on word boundary", `ADDRESS_EXCEPTION_STORE`).
  **Model:** raises AdES (ExcCode 5), `BadVAddr = addr`; memory unchanged.
- **MARS note**: same SOURCE AMBIGUITY as `lw` — `operands[1]` (offset) is
  used raw with no inline sign-extension in `sw`'s `simulate()` body either.
  See `lw` entry for the full explanation; same decision is required for
  the Lean spec.
- **Source**: `InstructionSet.java`, lines 750–770 (`simulate()` body at
  758–768).

### lb (I)
- **Encoding**: `opcode=100000` (0x20). Fields:
  `100000 ttttt fffff ssssssssssssssss` → `base=ttttt`(operand 2),
  `rt=fffff`(dest, operand 0), `offset=ssss...`(operand 1).
- **Semantics**: `addr = $base + sext16(offset)` (explicit
  `operands[1] << 16 >> 16` inline); `byteVal = MEM8[addr]`;
  `$rt = sext8(byteVal)` (`<<24 >>24` to sign-extend the byte to 32 bits).
- **Errors/halts**: no alignment requirement for byte access; only
  out-of-range address throws `AddressErrorException`
  (`ADDRESS_EXCEPTION_LOAD`) in MARS. In the model: Address Error (AdEL) only for a kernel address
  from User Mode (Global rule 5a).
- **MARS note**: none — this instruction does sign-extend its offset
  inline, unlike `lw`/`sw` (see above).
- **Source**: `InstructionSet.java`, lines 1272–1296.

### lbu (I)
- **Encoding**: `opcode=100100` (0x24). Same layout as `lb`.
- **Semantics**: `addr = $base + sext16(offset)`; `$rt = zext8(MEM8[addr])`
  (masked with `& 0x000000ff`, no sign extension of the loaded byte).
- **Errors/halts**: none beyond out-of-range address.
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 1347–1370.

### lh (I)
- **Encoding**: `opcode=100001` (0x21). Same field layout as `lb` (offset
  at operand 1, base at operand 2, dest at operand 0).
- **Semantics**: `addr = $base + sext16(offset)`; `halfVal = MEM16[addr]`
  (2 bytes, big-endian); `$rt = sext16(halfVal)` (`<<16 >>16`).
- **Errors/halts**: `addr % 2 != 0` → `AddressErrorException` ("...not
  aligned on halfword boundary", `ADDRESS_EXCEPTION_LOAD`).
- **MARS note**: none — sign-extends offset inline, consistent with `lb`.
- **Source**: `InstructionSet.java`, lines 1297–1321.

### lhu (I)
- **Encoding**: `opcode=100101` (0x25). Same layout as `lh`.
- **Semantics**: `addr = $base + sext16(offset)` (comment: "offset is
  sign-extended and loaded halfword value is zero-extended");
  `$rt = zext16(MEM16[addr])` (masked `& 0x0000ffff`).
- **Errors/halts**: `addr % 2 != 0` → `AddressErrorException`
  (`ADDRESS_EXCEPTION_LOAD`).
- **MARS note**: none.
- **Source**: `InstructionSet.java`, lines 1322–1346.

### sh (I)
- **Encoding**: `opcode=101001` (0x29). Fields: `base` at operand 2, `rt`
  (source register) at operand 0, `offset` at operand 1.
- **Semantics**: `addr = $base + sext16(offset)`;
  `MEM16[addr] = $rt & 0x0000ffff` (low 16 bits of `$rt` stored,
  big-endian byte order).
- **Errors/halts**: `addr % 2 != 0` → `AddressErrorException` ("store
  address not aligned on halfword boundary", `ADDRESS_EXCEPTION_STORE`).
  **Model:** raises AdES (ExcCode 5), `BadVAddr = addr`.
- **MARS note**: none — sign-extends offset inline, unlike `sw`.
- **Source**: `InstructionSet.java`, lines 1395–1416.

### sb (I)
- **Encoding**: `opcode=101000` (0x28), `base` (rs), `rt`, 16-bit `offset`
  (MD00086 "SB": `SB rt, offset(base)`).
- **Semantics**: `addr = $base + sext16(offset)`;
  `MEM8[addr] = $rt[7:0]` (MD00086 "SB" Operation:
  `StoreMemory(CCA, BYTE, dataword, pAddr, vAddr, DATA)` with the
  least-significant byte of `GPR[rt]`). Exactly one byte of physical memory changes, at the
  translated address (Global rule 5a).
  Clears `State.llBit`, like every store in this model (the pinned choice
  described under "The `LLbit` model").
- **Errors/halts**: no alignment requirement, so no misalignment Address Error; a kernel address
  from User Mode raises Address Error (AdES, `BadVAddr` = the address; Global rule 5a).
- **Lean**: `Instruction.sb`, `Step.lean` `.sb` arm; `sb_spec_raw`.
  The assembler mnemonic is owned by `Asm.lean`.

---

## Control flow

### j (J)
- **Encoding**: `opcode=000010` (0x02). Fields:
  `000010 ffffffffffffffffffffffffff` → `target=ffff...`(26-bit field,
  operand index 0; assembled from an absolute word address shifted right 2,
  per `ProgramStatement.java` line ~357).
- **Semantics**: schedules `PC = (PC_next & 0xF0000000) | (target << 2)`
  as the delay-slot transfer (Global rule 3) rather than applying it
  immediately; `j` itself falls through to `PC_next` so the delay-slot
  instruction executes first. `PC_next` is the PC *after* this
  instruction's fetch-increment (rule 1), so the top 4 bits of the jump
  target come from the region containing the instruction *after* `j`, not
  `j` itself (normal MIPS pseudo-direct jump semantics). `target` is the
  26-bit `instr_index` field ("I+1: PC ← PC_{GPRLEN-1..28} || instr_index ||
  0^2", MD00086 Vol II-A Rev 6.06, J, p.194; JAL, p.195): the model uses
  `target &&& 0x3FFFFFF` (7C; `decode` never produces wider values, a
  hand-built `Instruction` may).
- **Errors/halts**: none directly; a bad target can later cause an
  instruction-fetch `AddressErrorException` on the next fetch; a branch/jump
  occupying `j`'s own delay slot raises Reserved Instruction
  (Global rule 3).
- **MARS note**: our semantics **overrides MARS's default**
  (`DelayedBranching=false`) and executes one delay-slot instruction before
  `PC` becomes the target, matching real MIPS hardware's architecturally
  mandated delay-slot semantics (Global rule 3) rather than MARS's
  immediate-jump default.
- **Source**: `InstructionSet.java`, lines 1200–1216;
  `processJump` at lines 3288–3298.

### jal (J)
- **Encoding**: `opcode=000011` (0x03). Same field layout as `j`.
- **Semantics**: `$ra ($31) = PC_next + 4` (i.e. `pc + 8`, the address
  *after* the delay slot — see Global rule 1/3, since the delay-slot
  instruction still executes before `jal` can return); then schedules
  `PC = (PC_next & 0xF0000000) | (target << 2)` as the delay-slot transfer,
  identical target computation to `j`. `jal` itself falls through to
  `PC_next` so the delay-slot instruction executes first.
- **Errors/halts**: none directly; a branch/jump occupying `jal`'s own
  delay slot raises Reserved Instruction (Global rule 3).
- **MARS note**: our semantics **overrides MARS's default**
  (`DelayedBranching=false`, under which `$ra = PC_next` with no delay slot
  executed) to match real MIPS32: one delay-slot instruction always
  executes, so `$ra` must be `PC_next + 4` rather than `PC_next` (Global
  rule 1/3).
- **Source**: `InstructionSet.java`, lines 1228–1244;
  `processReturnAddress` at lines 3309–3316.

### beq (I-branch)
- **Encoding**: `opcode=000100` (0x04). Fields:
  `000100 fffff sssss tttttttttttttttt` → `rs=fffff`($t1, operand 0),
  `rt=sssss`($t2, operand 1), `offset=tttt...`(operand 2, 16-bit signed
  word displacement).
- **Semantics**: if `$rs == $rt` (32-bit equality), schedules
  `PC = PC_next + (offset << 2)` as the delay-slot transfer (Global rule 3)
  — `beq` itself still falls through to `PC_next` so the delay-slot
  instruction executes first; otherwise PC stays at `PC_next` with no
  scheduled transfer (ordinary fallthrough).
- **Errors/halts**: none directly from the comparison; a bad target can
  cause a later fetch error; a branch/jump occupying `beq`'s own delay slot
  (only possible when `beq` is taken) raises Reserved Instruction (Global rule 3).
- **MARS note**: our semantics **overrides MARS's default**
  (`DelayedBranching=false`) and executes one delay-slot instruction before
  the target takes effect, matching real MIPS hardware (Global rule 3)
  rather than MARS's immediate-branch default.
- **Source**: `InstructionSet.java`, lines 858–875;
  `processBranch` at lines 3265–3281.

### bne (I-branch)
- **Encoding**: `opcode=000101` (0x05). Same layout as `beq`.
- **Semantics**: if `$rs != $rt`, schedules `PC = PC_next + (offset << 2)`
  as the delay-slot transfer, same as `beq` (Global rule 3).
- **Errors/halts**: none directly; same delay-slot rule as `beq`.
- **MARS note**: same real-MIPS32 delay-slot override as `beq` (Global
  rule 3).
- **Source**: `InstructionSet.java`, lines 876–891.

### blez (I-branch)
- **Encoding**: `opcode=000110` (0x06). Fields:
  `000110 fffff 00000 ssssssssssssssss` → `rs=fffff`($t1, operand 0),
  `rt=00000`(fixed/unused), `offset=ssss...`(operand 1).
- **Semantics**: if `$rs <= 0` (signed comparison, includes zero),
  schedules `PC = PC_next + (offset << 2)` as the delay-slot transfer, same
  as `beq` (Global rule 3).
- **Errors/halts**: none directly; same delay-slot rule as `beq`.
- **MARS note**: same real-MIPS32 delay-slot override as `beq` (Global
  rule 3).
- **Source**: `InstructionSet.java`, lines 942–958.

### bgtz (I-branch)
- **Encoding**: `opcode=000111` (0x07). Same layout as `blez`.
- **Semantics**: if `$rs > 0` (signed, strictly positive), schedules
  `PC = PC_next + (offset << 2)` as the delay-slot transfer, same as `beq`
  (Global rule 3).
- **Errors/halts**: none directly; same delay-slot rule as `beq`.
- **MARS note**: same real-MIPS32 delay-slot override as `beq` (Global
  rule 3).
- **Source**: `InstructionSet.java`, lines 926–941.

---

## Register-indirect jump/call (real MIPS32 ISA)

`jr` and `jalr` are real MIPS32 instructions that were missing from the
original MARS-grounded set (the first coverage analysis ranked this the
highest-priority gap), since without `jr` no compiled MIPS
function can return (`jr $ra`) and without `jalr` no function pointer /
dynamic-dispatch call can be made. Per this addition's house rule (same as
the "MIPS32 / MIPS32r2 additions" and "Coprocessor 0" sections below), their
semantics are grounded directly in the **standard MIPS32 architecture** --
"MIPS32 Architecture For Programmers, Volume II-A: The MIPS32 Instruction
Set" (MD00086 Vol II-A Rev 6.06, JR p.206-207, JALR p.196-197) -- not against
the MARS source; MARS is this project's differential-testing
oracle, not the spec source. Like every other branch/jump in this document,
both get exactly one architectural delay slot (Global rule 3): `pendingBranch`
schedules the register-read target, falling through to the delay-slot
instruction first, exactly like `j`/`jal`.

| Mnemonic | Format | One-line semantics |
|---|---|---|
| `jr` | R | `PC = $rs` |
| `jalr` | R | `$rd = PC_next + 4; PC = $rs` |
| `jr.hb` | R | `PC = $rs`, hazard barrier |
| `jalr.hb` | R | `$rd = PC_next + 4; PC = $rs`, hazard barrier |

### jr (R)
- **Encoding**: `opcode=000000` (SPECIAL), `funct=001000` (0x08). Fields:
  `000000 sssss 00000 00000 00000 001000` → `rs=sssss` (the only field
  that carries information); `rt`/`rd` must be zero (otherwise the word
  does not decode); bits 10..6 are the `hint` field, 0 for `jr` ("In
  release 1 of the architecture, the only defined hint field value is 0",
  JR p.207); hint `10000` is `jr.hb` (below); any other hint value does not
  decode (Reserved Instruction; an UNPREDICTABLE encoding, SPEC-NOTES §11).
- **Semantics**: Jump Register. Schedules `PC = $rs` -- the full raw 32-bit
  register value, *not* a 26-bit target field composed with `PC_next`'s top
  4 bits like `j` -- as the delay-slot transfer (Global rule 3); `jr`
  itself falls through to `PC_next` so the delay-slot instruction executes
  first. The canonical real-MIPS32 function-return idiom is `jr $ra`
  (return to the address `jal`/`jalr` linked into `$ra`); it is also used
  for compiled switch-statement jump tables and other computed branches.
- **Errors/halts**: none directly from `jr` itself. If `$rs` holds a value
  that is not 4-byte-aligned, this is **not** special-cased at the point
  `jr` schedules it: the delay slot executes, `pc` becomes the misaligned
  target, and the *next* `step` raises Address Error (AdEL) on the fetch
  with `EPC = BadVAddr =` that target (Global rule 5). A branch/jump
  occupying `jr`'s own delay slot raises Reserved Instruction
  (Global rule 3).
- **ISA note**: standard MIPS32 instruction (MIPS I onward); not MARS-
  sourced (see this section's header note). MARS itself does implement
  `jr`, but with its own default `DelayedBranching=false` no-delay-slot
  timing -- this spec instead gives it the real-MIPS32 one-delay-slot
  semantics, the same override every other branch/jump in this document
  already receives (Global rule 3).
- **Source**: MD00086 Vol II-A Rev 6.06, JR, p.206-207.

### jalr (R)
- **Pin (`rs = rd`).** MD00086 Vol II-A Rev 6.06, JALR, p.196: "Register
  specifiers rs and rd must not be equal, because such an instruction does
  not have the same effect when re-executed. The result of executing such
  an instruction is UNPREDICTABLE." The model's behaviour for `rs = rd`
  (the target is read from `$rs` first, then the link value is written to
  `$rd`) is a pinned choice, not architecturally defined.
- **Encoding**: `opcode=000000` (SPECIAL), `funct=001001` (0x09). Fields:
  `000000 sssss 00000 ddddd 00000 001001` → `rs=sssss` (jump target
  source), `rd=ddddd` (link destination); `rt` must be zero; bits 10..6
  are the `hint` field: 0 for `jalr` (JALR p.196), `10000` for `jalr.hb`,
  any other value does not decode, as for `jr`. Real MIPS32 assembly syntax also
  allows the one-operand form `jalr $rs` as sugar for `jalr $ra, $rs`
  (`rd` defaults to `31`); the assembler (`Asm.lean`) supports this sugar.
- **Semantics**: Jump and Link Register. `$rd = PC_next + 4` (i.e.
  `pc + 8`, the address *after* the delay slot -- same link-value
  convention as `jal`, Global rule 1/3, since the delay-slot instruction
  still executes before control can return to `$rd`); then schedules
  `PC = $rs` (the raw register value, same target computation as `jr`) as
  the delay-slot transfer. `jalr` itself falls through to `PC_next` so the
  delay-slot instruction executes first. If `rd == rs` (UNPREDICTABLE in
  the architecture, see the pin above), the jump target is read from `$rs`
  *before* `$rd` is overwritten with the link value, so `jalr $t9, $t9`
  jumps to the original `$t9` value in this model. Used for
  indirect procedure calls, dynamic linking stubs, and calls through a
  function pointer (the common real-MIPS32 ABI idiom `jalr $t9`).
- **Errors/halts**: same misaligned-`$rs`-target and delay-slot-in-delay-
  slot conditions as `jr` above.
- **ISA note**: standard MIPS32 instruction (MIPS I onward); not MARS-
  sourced (see this section's header note), same real-MIPS32 one-delay-slot
  override as `jr`/`j`/`jal` (Global rule 3).
- **Source**: MD00086 Vol II-A Rev 6.06, JALR, p.196-197.
## REGIMM zero-comparison branches (real MIPS32 ISA)

The four instructions in this section (`bltz`, `bgez`, `bltzal`, `bgezal`)
complete the zero-comparison conditional-branch family alongside `blez`/
`bgtz` above (missing from the original MARS-grounded set). Per this
addition's house rule (same precedent as the `movn`/`movz`/`clo`/`clz`/
`seb`/`seh` section below), their semantics/encodings are grounded directly
in the **real MIPS32 architecture** — MIPS32 Architecture For
Programmers, Volume II-A (MD00086 Vol II-A Rev 6.06: BLTZ p.97, BGEZ
p.75, BLTZAL p.98, BGEZAL p.76) — not
derived from `InstructionSet.java` line citations, even though MARS does
also implement all four.

All four share **opcode `0x01`** (the `REGIMM` major opcode): unlike every
other branch in this document, the opcode alone does not identify the
instruction — the 5-bit `rt` field (bits 20–16), which carries no
register operand here, instead selects which of the four REGIMM
instructions it is. Field layout: `000001 fffff ttttt ssssssssssssssss` →
`rs=fffff` (operand 0, the register tested), `rt=ttttt` (sub-opcode
selector, not a register), `offset=ssss...` (operand 1, 16-bit signed word
displacement, identical convention to `blez`/`bgtz`).

| Mnemonic | `rt` field | Semantics |
|---|---|---|
| `bltz` | `0x00` | `if ($rs < 0) PC = PC_next + (offset << 2)`, signed |
| `bgez` | `0x01` | `if ($rs >= 0) PC = PC_next + (offset << 2)`, signed |
| `bltzal` | `0x10` | `$ra = PC_next + 4`, unconditionally; then same condition as `bltz` |
| `bgezal` | `0x11` | `$ra = PC_next + 4`, unconditionally; then same condition as `bgez` |


### jr.hb (R, MIPS32 Release 2)
- **Encoding**: `000000 sssss 00000 00000 10000 001000`: `jr` with hint bit 10
  set ("JR.HB uses bit 10 of the instruction (the upper bit of the hint field)
  to denote the hazard barrier operation", JR.HB p.208). Constructor
  `jrHb (rs)`; assembler `jr.hb $rs`.
- **Semantics**: as `jr` (`I: temp ← GPR[rs]`, `I+1: PC ← temp`), then
  `ClearHazards()` (p.209). The model has no hazard state (a CP0 write is seen
  by the next instruction; SPEC-NOTES `EHB` pin), so the barrier changes
  nothing. A CTI in its delay slot raises Reserved Instruction (Global rule 3).
- **Source**: MD00086 Vol II-A Rev 6.06, JR.HB, p.208-209.

### jalr.hb (R, MIPS32 Release 2)
- **Encoding**: `000000 sssss 00000 ddddd 10000 001001`: `jalr` with hint
  bit 10 set (JALR.HB p.198). Constructor `jalrHb (rs rd)`; assembler
  `jalr.hb $rd, $rs` and `jalr.hb $rs` (`rd = 31`).
- **Semantics**: as `jalr` (the link `pc + 8` is written to `$rd`, the target
  is read from `$rs` first; `rs = rd` is UNPREDICTABLE, same pin as `jalr`),
  then `ClearHazards()`, which has no state in the model.
- **Source**: MD00086 Vol II-A Rev 6.06, JALR.HB, p.198-199.

### bltz (I-branch, REGIMM)
- **Encoding**: `opcode=000001` (0x01), `rt=00000` (0x00). Fields:
  `000001 fffff 00000 ssssssssssssssss` → `rs=fffff` (operand 0),
  `offset=ssss...` (operand 1).
- **Semantics**: if `$rs < 0` (signed), schedules
  `PC = PC_next + (offset << 2)` as the delay-slot transfer, same
  one-delay-slot discipline as `beq`/`blez`/`bgtz` (Global rule 3; this
  codebase's `State.pendingBranch` mechanism).
- **Errors/halts**: none directly; a branch/jump occupying `bltz`'s own
  delay slot raises Reserved Instruction (Global rule 3).
- **Source**: MD00086 Vol II-A Rev 6.06, BLTZ, p.97.

### bgez (I-branch, REGIMM)
- **Encoding**: `opcode=000001` (0x01), `rt=00001` (0x01). Same layout as
  `bltz`.
- **Semantics**: if `$rs >= 0` (signed, includes zero), schedules
  `PC = PC_next + (offset << 2)`, same delay-slot discipline as `bltz`.
- **Errors/halts**: none directly; same delay-slot rule as
  `bltz`.
- **Source**: MD00086 Vol II-A Rev 6.06, BGEZ, p.75.

### bltzal (I-branch, REGIMM)
- **Pin (`rs = 31`).** `bltzal`/`bgezal` (and `bltzall`/`bgezall`) with
  `rs = 31` are UNPREDICTABLE — the instruction would not be restartable
  (MD00086 Rev 6.06 "BLTZAL", pp. 97–98). The model links first-read
  semantics (`$rs` is read before `$ra` is written) as a pinned choice.
- **Encoding**: `opcode=000001` (0x01), `rt=10000` (0x10). Same field
  layout as `bltz`.
- **Semantics**: links `$ra = PC_next + 4` (i.e. `PC + 8`, past the delay
  slot, identical convention to `jal`'s link value) **unconditionally** —
  every execution of `bltzal` writes `$ra`, regardless of whether the
  branch itself is taken — then, independently, if `$rs < 0` (signed),
  schedules `PC = PC_next + (offset << 2)` as the delay-slot transfer, same
  as `bltz`. This two-part unconditional-link/conditional-branch structure
  is the real MIPS32 architectural definition (MD00086 Vol II-A Rev 6.06, BLTZAL p.98,
  pseudocode: `GPR[31] <- PC + 8` executes in the instruction's own cycle
  unconditionally; the branch condition on `GPR[rs]` is evaluated and
  applied one cycle later, at the delay slot), not an assumption — it was
  verified against the ISA pseudocode rather than inferred from `jal`.
- **Errors/halts**: none directly; same delay-slot rule as
  `bltz`.
- **UNPREDICTABLE case**: the real ISA pseudocode explicitly marks `rs = 31`
  ($ra) as **UNPREDICTABLE**, since the link into `$31` happens before the
  branch condition on `$rs` is tested, so testing `$ra` itself could
  legitimately observe either its old value or the just-written link value.
  This simulator resolves that UNPREDICTABLE case by testing the *pre-link*
  value of `$rs` (i.e. `Step.lean` reads `$rs` from the state as it was
  before `$ra`'s write is applied) — a documented, deliberate choice for
  an architecturally-unspecified input, not an oversight.
- **Source**: MD00086 Vol II-A Rev 6.06, BLTZAL, p.98.

### bgezal (I-branch, REGIMM)
- **Encoding**: `opcode=000001` (0x01), `rt=10001` (0x11). Same field
  layout and unconditional-link convention as `bltzal`.
- **Semantics**: links `$ra = PC_next + 4` unconditionally, then if
  `$rs >= 0` (signed), schedules `PC = PC_next + (offset << 2)`, same as
  `bgez`.
- **Errors/halts**: none directly; same delay-slot rule as
  `bltz`.
- **UNPREDICTABLE case**: same `rs = $ra` (31) UNPREDICTABLE case and
  pre-link-value resolution as `bltzal`.
- **Source**: MD00086 Vol II-A Rev 6.06, BGEZAL, p.76.

## REGIMM trap-immediate family (real MIPS32 ISA)

The six instructions in this section (`teqi`, `tnei`, `tgei`, `tgeiu`,
`tlti`, `tltiu`) are the sign-extended-16-bit-immediate counterpart of the
`teq`/`tne`/`tlt`/`tge`/`tltu`/`tgeu` register-register trap family
documented in the
["Coprocessor 0 / traps and exceptions"](#coprocessor-0--traps-and-exceptions-real-mips32-isa)
section below; they were missing from the original MARS-grounded set. Per this addition's
house rule (same precedent as the REGIMM zero-comparison branches above),
their semantics/encodings are grounded directly in the **real MIPS32
architecture** — MIPS32 Architecture For Programmers, Volume II-A
(MD00086 Vol II-A Rev 6.06: TEQI p.417, TNEI p.439, TGEI p.419, TGEIU
p.420, TLTI p.435, TLTIU p.436) — not
derived from `InstructionSet.java`, even though MARS does also implement
all six (per this track's process requirements, MARS is not consulted as
the spec source).

All six share **opcode `0x01`** (the same `REGIMM` major opcode as
`bltz`/`bgez`/`bltzal`/`bgezal`): the 5-bit `rt` field (bits 20–16) again
carries no register operand, instead selecting which of the ten REGIMM
instructions this is. Field layout: `000001 fffff ttttt ssssssssssssssss`
→ `rs=fffff` (operand 0, the register tested), `rt=ttttt` (sub-opcode
selector, not a register), `imm=ssss...` (operand 1, 16-bit immediate,
sign-extended — **not** a PC-relative branch displacement, unlike every
other REGIMM instruction's `offset` field of the same bit position).

| Mnemonic | `rt` field | Semantics |
|---|---|---|
| `teqi` | `0x0c` | `if ($rs == sext16(imm)) trap`, signed |
| `tnei` | `0x0e` | `if ($rs != sext16(imm)) trap`, signed |
| `tgei` | `0x08` | `if ($rs >= sext16(imm)) trap`, signed |
| `tgeiu` | `0x09` | `if ($rs >=u sext16(imm)) trap`, unsigned compare on sign-extended imm |
| `tlti` | `0x0a` | `if ($rs < sext16(imm)) trap`, signed |
| `tltiu` | `0x0b` | `if ($rs <u sext16(imm)) trap`, unsigned compare on sign-extended imm |

- **Semantics**: evaluate the named condition on `$rs` vs. `sext16(imm)` —
  `teqi`: `$rs == sext16(imm)`; `tnei`: `$rs != sext16(imm)`; `tgei`:
  `$rs >=s sext16(imm)` (signed); `tlti`: `$rs <s sext16(imm)` (signed).
  `tgeiu`/`tltiu` sign-extend the 16-bit immediate to 32 bits **first**,
  then compare the resulting bit pattern against `$rs` as **unsigned** —
  the same "sign-extend, then compare unsigned" convention this codebase's
  `sltiu` already uses (see the `slti`/`sltiu` section above), not a
  zero-extend. If the condition holds, take the exception described in the
  "Coprocessor 0 / traps and exceptions" section below with
  `excCode = excCodeTr` (identical mechanism to `teq`/`tne`/etc. —
  `Step.lean`'s `takeException` helper). If the condition does not hold,
  the instruction is a complete no-op other than the ordinary fall-through
  to `pc + 4` — no CP0 state is touched at all.
- **Errors/halts**: none beyond the exception transition itself (a state
  transition, not a halt).
- **MARS note**: not applicable — not part of the original MARS-grounded set;
  MARS does implement this family in its own `InstructionSet.java`, but per
  this track's process requirements the ground truth cited here is the real
  MIPS32 ISA, not MARS's implementation of it.
- **Source**: MD00086 Vol II-A Rev 6.06, TEQI p.417, TNEI p.439, TGEI
  p.419, TGEIU p.420, TLTI p.435, TLTIU p.436.

---

## MIPS32 / MIPS32r2 additions (beyond the MARS-matched baseline)

The six instructions in this section (`movn`, `movz`, `clo`, `clz`, `seb`,
`seh`) are real MIPS32/MIPS32r2 instructions that were out of the original
MARS-grounded set. Per this addition's house rule, their semantics are grounded
directly in the **standard MIPS32 architecture** (as specified in the MIPS32
Architecture Reference Manual, Volume II-A, the "CLO"/"CLZ"/"MOVN"/"MOVZ"/
"SEB"/"SEH" instruction pages), not against the MARS source —
MARS is this project's differential-testing oracle, not the spec source,
and (unlike the original MARS-grounded instructions above) these encodings/semantics are
pinned from the ISA directly rather than derived from `InstructionSet.java`
line citations.

| Mnemonic | Format | One-line semantics |
|---|---|---|
| `movn` | R | `if ($rt != 0) $rd = $rs` (else `$rd` unchanged) |
| `movz` | R | `if ($rt == 0) $rd = $rs` (else `$rd` unchanged) |
| `clo` | R (SPECIAL2) | `$rd = count of leading one bits in $rs` (32 if all-ones) |
| `clz` | R (SPECIAL2) | `$rd = count of leading zero bits in $rs` (32 if all-zero) |
| `seb` | R (SPECIAL3/BSHFL) | `$rd = sext8($rt[7:0])` |
| `seh` | R (SPECIAL3/BSHFL) | `$rd = sext16($rt[15:0])` |

### movn (R)
- **Encoding**: `opcode=000000` (SPECIAL), `funct=001011` (0x0b). Same
  `rs, rt, rd` field layout as `add`/`slt`/etc.
- **Semantics**: Move Conditional on Not Zero. If `$rt != 0`, `$rd = $rs`.
  **If `$rt == 0`, `$rd` is left completely unchanged** — this is a true
  conditional no-op on the destination register, not "write zero"; a
  common implementation mistake this spec deliberately avoids (see
  `Step.lean`'s `movn`/`movz` test cases, which pre-seed `$rd` with a
  sentinel value to catch exactly this bug).
- **Errors/halts**: none; no overflow concept.
- **ISA note**: standard MIPS32r2 instruction, present from MIPS32 Release 1
  onward alongside `movz`; commonly used to implement branch-free
  conditional-move idioms (e.g. `a = cond ? b : a`).

### movz (R)
- **Encoding**: `opcode=000000` (SPECIAL), `funct=001010` (0x0a). Same
  layout as `movn`.
- **Semantics**: Move Conditional on Zero. If `$rt == 0`, `$rd = $rs`;
  otherwise `$rd` is left unchanged (same "true no-op", not "write zero",
  caveat as `movn`).
- **Errors/halts**: none.
- **ISA note**: standard MIPS32r2 instruction.

### clo (R, SPECIAL2)
- **Encoding**: `opcode=011100` (0x1c, SPECIAL2), `funct=100001` (0x21).
  Fields: `011100 sssss ddddd ddddd 00000 100001` → `rs=sssss` (source),
  `rd=ddddd` (destination). **Encoding quirk**: the `rt` field (bits
  20..16) must carry the *same* register number as `rd`: "The operation of
  the instruction is UNPREDICTABLE if the rt and rd fields of the
  instruction contain different values" (MD00086 Vol II-A Rev 6.06, CLO,
  p.134). `decode` **rejects** a word with `rt ≠ rd` (→ Reserved
  Instruction, a pin among the legal outcomes); the constructor stores only
  `(rs, rd)` and `encode` writes `rd` into both fields.
- **Semantics**: Count Leading Ones. `$rd` = the number of consecutive `1`
  bits starting from the most-significant bit (bit 31) of `$rs`, stopping at
  the first `0` bit. If `$rs` is all-ones (`0xFFFFFFFF`), the result is `32`.
- **Errors/halts**: none; no overflow concept.
- **Source**: MD00086 Vol II-A Rev 6.06, CLO, p.134.

### clz (R, SPECIAL2)
- **Encoding**: `opcode=011100` (0x1c, SPECIAL2), `funct=100000` (0x20).
  Same field layout as `clo`, and the same rule: `rt ≠ rd` is
  UNPREDICTABLE (MD00086 Vol II-A Rev 6.06, CLZ, p.135) and does not
  decode.
- **Semantics**: Count Leading Zeros. `$rd` = the number of consecutive `0`
  bits starting from bit 31 of `$rs`, stopping at the first `1` bit. If
  `$rs` is all-zero, the result is `32`.
- **Errors/halts**: none.
- **ISA note**: standard MIPS32 instruction.

### seb (R, SPECIAL3/BSHFL)
- **Encoding**: `opcode=011111` (0x1f, SPECIAL3), `funct=100000` (0x20,
  the shared BSHFL sub-opcode family). Fields: `011111 00000 ttttt ddddd
  10000 100000` → `rs=00000` (unused/fixed 0), `rt=ttttt` (source),
  `rd=ddddd` (destination), and the 5-bit shamt-position sub-field fixed to
  `10000` (0x10) to select SEB specifically out of the BSHFL family (which
  also includes `wsbh`, `seh`, and others not in this scope — any other
  sub-field value under funct 0x20 decodes to `none` here).
- **Semantics**: Sign-Extend Byte. `$rd` = the low byte of `$rt`
  (`$rt[7:0]`), sign-extended to 32 bits.
- **Errors/halts**: none.
- **ISA note**: standard MIPS32r2 instruction.

### seh (R, SPECIAL3/BSHFL)
- **Encoding**: `opcode=011111` (0x1f, SPECIAL3), `funct=100000` (0x20).
  Same layout as `seb`, but the sub-field is `11000` (0x18).
- **Semantics**: Sign-Extend Halfword. `$rd` = the low halfword of `$rt`
  (`$rt[15:0]`), sign-extended to 32 bits.
- **Errors/halts**: none.
- **ISA note**: standard MIPS32r2 instruction.

---

## Syscalls (hosted services: 1, 4, 10, 11)

### syscall

- **Processor semantics** (MD00086 Vol II-A Rev 6.06, SYSCALL, p.415): "A
  system call exception occurs, immediately and unconditionally transferring
  control to the exception handler"; Operation `SignalException(SystemCall)`.
  `step` raises System Call (ExcCode 8, `EPC` = the `syscall`, or the branch
  with `Cause.BD = 1` in a delay slot) for **every** `$v0`. The 20-bit `code`
  field is carried in the constructor and ignored by execution ("may be
  retrieved by the exception handler by loading the contents of the memory
  word containing the instruction"). StepSpec: `syscall_spec_raw`.
- **Hosted services (environment, not architecture).** The hosted run
  (`Semantics/Env.lean`, `MipsRun` by default, `DiffHarness`,
  `EquivHarness`, the QEMU harness's default handler) performs the MARS/SPIM
  services 1, 4, 10, 11 *instead of* stepping when the instruction at `pc` is
  a `syscall` and `$v0` selects one — as if an operating system had served
  the exception and returned (`pc + 4`, or the pending branch target in a
  delay slot; no register changes); `exit` (10) stops the run. Any other
  `$v0` is executed by the processor (the System Call exception); with no
  handler loaded the hosted run stops with `unhandledException 8 …`.
  `MipsRun --bare` performs no service. StepSpec (`Specs/Hosted.lean`):
  `hostStep_syscall_spec`, `hosted_print_int`, `hosted_exit`,
  `hostStep_eq_step`. SPEC-NOTES §9 items 9 and 25.

Dispatch source: `InstructionSet.java` `findAndSimulateSyscall`
(lines 3237–3246), invoked from the `syscall` basic instruction's
`simulate()` with `RegisterFile.getValue(2)` (i.e. `$v0`) as the service
number (see the `"syscall"` instruction entry around line 1195). Argument
convention: `$v0` = service number, `$a0` = register 4 (first argument).

### syscall 1 — PrintInt
- **Encoding**: not a machine opcode; selected via `$v0 = 1` then the
  `syscall` instruction (`opcode=000000`, `funct=001100`).
- **Semantics**: reads `$a0` (register 4) as a signed 32-bit int, converts
  with `Integer.toString` (decimal, signed), writes to the console via
  `SystemIO.printString` to `System.out.print` (`SyscallPrintInt.java:53`).
  **No trailing newline is appended** -- confirmed both by the source
  (`print`, not `println`) and empirically (a program printing 42 then 99
  produces exactly `"4299"`, concatenated with no separator). No registers
  or memory are modified by the syscall itself.
- **Errors/halts**: none specific; a missing/invalid service number more
  generally throws `ProcessingException(..., SYSCALL_EXCEPTION)` from
  `findAndSimulateSyscall`, but service 1 is always registered.
- **MARS note**: none.
- **Source**: `mars/mips/instructions/syscalls/SyscallPrintInt.java`,
  class `SyscallPrintInt`, constructor registers service number 1
  (`super(1, "PrintInt")`), `simulate()` method (entire ~15-line file).

### syscall 4 — PrintString
- **Encoding**: not a machine opcode; selected via `$v0 = 4` then the `syscall`
  instruction (`opcode=000000`, `funct=001100`).
- **Semantics**: reads `$a0` (register 4) as a byte address; repeatedly
  calls `Globals.memory.getByte(addr)`, printing each byte as a `char` via
  `SystemIO.printString`, incrementing `addr` by 1 each iteration, **until
  a `0x00` byte is read** (null-terminated C-style string; the loop
  condition is literally `while (ch != 0)`). The terminating null byte
  itself is not printed.
- **Errors/halts**: any `AddressErrorException` while scanning (e.g.
  running off the end of mapped memory, or an unmapped byte) is rethrown as
  a `ProcessingException`, halting the program (no alignment requirement
  for byte reads, so this is only an out-of-range condition). If the string
  is never null-terminated within valid memory, this is effectively an
  infinite scan until such an error occurs.
- **MARS note**: none beyond the above — straightforward byte-at-a-time
  scan, no bulk/word-level read optimization.
- **Source**: `mars/mips/instructions/syscalls/SyscallPrintString.java`,
  class `SyscallPrintString`, constructor registers service number 4,
  `simulate()` method (entire file, ~20 lines of logic).

### syscall 10 — Exit
- **Encoding**: not a machine opcode; selected via `$v0 = 10` then the
  `syscall` instruction (`opcode=000000`, `funct=001100`).
- **Semantics**: unconditionally throws `new ProcessingException()` — the
  **zero-argument constructor**, which sets `errs = null`
  (`mars/ProcessingException.java` lines 117–120, with the
  doc comment "No parameter and thus no error list. Use this for normal
  MIPS program termination"). No registers, memory, or `$a0` are
  inspected or modified — this syscall ignores any argument registers.
- **Errors/halts**: this *is* the halt signal. The dispatcher in
  `Simulator.java` special-cases `pe.errors() == null` (line 353) to set
  `constructReturnReason = NORMAL_TERMINATION` and stop cleanly — distinct
  from the `EXCEPTION` return reason used for all error conditions
  elsewhere in this document.
- **MARS note**: **behaviorally notable, not a deviation** — exit code /
  status value is not modeled by this syscall at all (contrast MARS's
  `syscall 17`, `Exit2`, which does read an exit code from `$a0`; that
  syscall is not modeled). In the Lean model "exit" is a hosted-run stop
  (`HaltReason.exit`, `Env.lean`) with no register/memory side effect.
- **Source**: `mars/mips/instructions/syscalls/SyscallExit.java`
  (entire file, ~12 lines of logic); halt dispatch in
  `mars/simulator/Simulator.java`, lines 352–358;
  `ProcessingException()` zero-arg constructor in
  `mars/ProcessingException.java`, lines 117–120.

### syscall 11 — PrintChar
- **Encoding**: not a machine opcode; selected via `$v0 = 11` then the
  `syscall` instruction (`opcode=000000`, `funct=001100`).
- **Semantics**: reads `$a0` (register 4), masks to the low byte
  (`& 0x000000ff`), casts to Java `char`, prints via
  `SystemIO.printString(Character.toString(t))`. Only one byte/character is
  ever printed per call; the upper 24 bits of `$a0` are ignored.
- **Errors/halts**: none.
- **MARS note**: none.
- **Source**: `mars/mips/instructions/syscalls/SyscallPrintChar.java`
  (entire file, ~15 lines of logic).

---

## Coprocessor 0 / traps and exceptions (real MIPS32 ISA)

This section is grounded in the MIPS32 architecture, not in MARS (whose
exception handling is a simulator shortcut, not a model of CP0 state):
MD00090 Vol III Rev 6.02 for the registers and the exception sequence,
MD00086 Vol II-A Rev 6.06 for the instructions.

### Coprocessor 0 state modeled (and what is deliberately out of scope)

Fourteen registers (`isModeledCp0Reg`; `Types.lean`, `Step.lean`):

| `(rd, sel)` | Register | Model |
|---|---|---|
| (7, 0) | `HWREna` (`cp0HWREna`) | bits 3..0 read/write (enable `rdhwr` registers 0..3 outside Kernel Mode); every other bit reads 0 and ignores writes ("If RDHWR register ‘n’ is not implemented, bit ‘n’ of this field returns a zero and is ignored on a write"); reset 0 (MD00090 Vol III Rev 6.02 §9.23, Table 9.39, p.175; §6.2.5, p.89) |
| (8, 0) | `BadVAddr` (`cp0BadVAddr`) | set on AdEL/AdES; read-only — `mtc0` to it is ignored (MD00090 Vol III Rev 6.02 §9.24, Table 9.41, p.177) |
| (9, 0) | `Count` (`cp0Count`) | read/write; advances by one per `step` unless `Cause.DC = 1` (`timerTick`; the rate is implementation-dependent, §9.27, Table 9.44, p.183: pin, SPEC-NOTES §9 item 28); reset value undefined (0 at power-on, kept by the Reset exception) |
| (11, 0) | `Compare` (`cp0Compare`) | read/write; when `Count` equals it `Cause.TI` is set; a write clears `Cause.TI` (§9.30, Table 9.46, p.187) |
| (12, 0) | `Status` (`cp0Status`) | bits with model meaning, and the only bits `mtc0` can write (`statusWriteMask = 0x3040FF17`): `IE` (0), `EXL` (1), `ERL` (2), `UM` (4), `IM7..IM0` (15..8), `BEV` (22), `CU0` (28), `CU1` (29). All other bits read as zero (bit 3, `R0`: no Supervisor Mode; MD00090 Vol III Rev 6.02 §9.32, Table 9.47, p.190-196). |
| (12, 1) | `IntCtl` | constant `0xE000_0000` (`intCtlValue`): `IPTI` = 7 (the timer request is merged into `IP7`), `IPPCI` = 0 ("If performance counters are not implemented (Config1PC = 0), this field returns zero on read", p.200), `IPFDC` = 0 (no EJTAG FDC), `VS` = 0 ("If neither EIC interrupt mode nor VI mode are implemented (Config3VEIC = 0 and Config3VInt = 0), this field is ignored on write and reads as zero", p.201); no writable field, so `mtc0` is ignored (MD00090 Vol III Rev 6.02 §9.33, Table 9.48, p.199-201) |
| (12, 2) | `SRSCtl` | constant 0 (`srsCtlValue`): `HSS` = 0 ("A value of zero in this field indicates that only the normal GPRs are implemented"), `EICSS` = 0 (no EIC), `ESS` = `PSS` = `CSS` = 0. `ESS`/`PSS` are R/W, but with `HSS = 0` 0 is the only value they can hold ("The operation of the processor is UNDEFINED if a value larger than the one in this field is written"): pin, `mtc0` is ignored (§9.34, Table 9.49, p.203-204). Exception entry and `eret` never change it (their shadow-set updates are guarded by `SRSCtlHSS ≠ 0`, §6.2.3 p.88, ERET p.177) |
| (13, 0) | `Cause` (`cp0Cause`) | exception entry writes `ExcCode` (6..2), `CE` (29..28) and, if `EXL` was 0, `BD` (31). `mtc0` can write `DC` (27), `IV` (23) and `IP1..IP0` (9..8) only (`causeWriteMask = 0x08800300`) — "With the exception of the IP1..0, DC, IV, and WP fields, all fields in the Cause register are read-only" (§9.36, p.209; Table 9.52, p.209-212). `DC` ("Disable Count register") stops `Count`. `TI` (30, `cp0TimerInt`) is set by the timer and cleared by a write to `Compare`; `mfc0` reads it in bit 30 and, merged as the timer request (`IntCtl.IPTI = 7` pin, Table 6.2 p.73), in `IP7` (bit 15) (`causeValue`). `IP7..IP2` also show the six hardware interrupt lines (`State.hwInt`, inputs the environment holds deasserted). `WP` (22) is not writable: the model has no watch registers. |
| (14, 0) | `EPC` (`cp0Epc`) | read/write (§9.38, Table 9.55, p.217) |
| (15, 0) | `PRId` | constant `0x00010000` (`prIdValue`): Company ID 1, Company Options, Processor ID and Revision 0 — an environment constant naming no real product; read-only (§9.40, Table 9.57, p.221) |
| (15, 1) | `EBase` (`cp0EBase`) | bits 31..30 read `10`; the Exception Base field (bits 29..12) is read/write (`ebaseWriteMask = 0x3FFFF000`); bits 11..0 (incl. `CPUNum`) read zero; no write gate. Reset and initial value `0x8000_0000` (§9.41, Figure 9.42 / Table 9.58, p.223-224) |
| (16, 0) | `Config` | `0x80008580 | K23<<28 | KU<<25 | K0` (`configValue s`): `M` = 1 (Config1 present), `BE` = 1 (big-endian), `AT` = 0 (MIPS32), `AR` = 1 (Release 2), `MT` = 3 (Fixed Mapping MMU), `K23`, `KU`, `K0` Read/Write, reset 2 (stored and read back, no effect: there is no cache); the other fields are read-only (§9.45, Table 9.64, p.233-235; Table A.2, p.317) |
| (16, 1) | `Config1` | constant `0x80000001` (`config1Value`): `M` = 1 (Config2 present: "If the Config2 register is implemented, this bit should read as a 1", p.237), `FP` = 1 (FPU implemented), everything else 0 — no caches, coprocessor 2, watch registers, MIPS16e, EJTAG; read-only (§9.46, Table 9.65, p.237-240) |
| (16, 2) | `Config2` | constant `0x80000000` (`config2Value`): `M` = 1 (Config3 present: "If the Config3 register is implemented, this bit should read as a 1", p.241), no level 2/3 cache (`SL` = `TL` = 0, "No cache present", p.242-243), `SS`/`SA`/`TS`/`TA` 0; `TU`/`SU` not implemented ("If this field is not implemented it should read as zero and be ignored on write", p.241-242), so `mtc0` is ignored. Present because Config2 is "Required if ... the Config3 register is required" (§9.47, Table 9.66, p.241-243) |
| (16, 3) | `Config3` | constant `0` (`config3Value`): Config3 is "Required if any optional feature described by this register is implemented: Release 2 of the Architecture, ..." (§9.48, p.245) and the model is Release 2; every field is 0 — `M` = 0 (no Config4), `ISA` = 0 ("Only MIPS32 Instruction Set is implemented", p.248), `ULRI` = 0 (no UserLocal), `VInt` = `VEIC` = 0 (no vectored/EIC interrupts), `LPA` = 0, no DSP/MT/MSA/VZ/SmartMIPS/CDMM/trace, ... (Table 9.67, p.245-251); "All fields in the Config3 register are read-only" (p.245), so `mtc0` is ignored |
| (30, 0) | `ErrorEPC` (`cp0ErrorEpc`) | read/write; written by `mtc0` and by the Reset exception (the restart PC) (§9.68, Table 9.83, p.307; §6.2.5, p.89-90) |

Pinned divergences / not modeled:

- **Operating modes and the CP0 access rule.** Kernel Mode is `Status.UM = 0`
  or `EXL = 1` or `ERL = 1` (MD00090 Vol III Rev 6.02 §3.2, p.21; with no
  Supervisor Mode `KSU = UM ‖ 0`, Table 9.47 p.195); User Mode is `UM = 1`,
  `EXL = 0`, `ERL = 0` (§3.4, p.22). Coprocessor 0 is usable in Kernel Mode or
  when `CU0 = 1` (§3.5.3, p.23). **Every CP0 instruction — `mfc0`, `mtc0`, `di`,
  `ei`, `eret`, `wait`, `rdpgpr`, `wrpgpr` — executed when coprocessor 0 is not usable raises
  Coprocessor Unusable with `Cause.CE = 0`** and does nothing else (§6.2.22,
  p.100; each page lists "Coprocessor Unusable": MFC0 p.266, MTC0 p.291, DI p.164,
  EI p.176, ERET p.178, WAIT p.443, RDPGPR p.335, WRPGPR p.444). The same holds for every COP0 word that does
  not decode (TLB instructions, `DERET`, reserved encodings)
  and for `CACHE` (opcode `0x2f`): Coprocessor Unusable instead of Reserved
  Instruction when coprocessor 0 is not usable (§6.2.21, p.99; "the Coprocessor
  Unusable Exception takes priority over the Reserved Instruction Exception",
  Table 6.6, p.83), Reserved Instruction otherwise. Pin: `eret`/`wait` in a
  delay slot raise Reserved Instruction in every mode (Global rule 3).
  Exception entry sets `EXL` (Kernel Mode) and keeps `UM`; `eret` clears `EXL`,
  returning to User Mode when `UM = 1`. Not yet modeled: the User-Mode address
  checks (Address Error for a kernel-segment reference from User Mode, Table 4.2
  p.30), see SPEC-NOTES §9 item 10. `RP`, `FR`, `RE`, `MX`, `PX`, `TS`, `SR`,
  `NMI`, `CU2`, `CU3` read as zero.
- **Interrupts** (interrupt compatibility mode only; MD00090 Vol III Rev 6.02 §6.1-6.1.1.1, p.71-73):
  request `i` is `Cause.IPi & Status.IMi` (Table 6.2, p.73), taken when `IE = 1`, `EXL = ERL = 0`
  (§6.1, p.72), before the fetch of the instruction at `pc` (Table 6.6/6.7, p.83-84), with `ExcCode = 0`,
  `EPC` = that instruction (the branch, `BD = 1`, in a delay slot), vector `0x180` (`IV = 0`) or `0x200`
  (`IV = 1`) (§6.2.26, p.102; Table 6.10, p.86). Sources: `IP1..IP0` (software, `mtc0`), the timer (`TI`
  into `IP7`), the hardware lines (`hwInt`, never asserted by this environment). Hazards (Table 6.5, p.82)
  are cleared at once (pin). No watch exception (no watch registers).
- **Reset** (`resetException`, `resetState`; §6.2.5 "Reset Exception",
  p.89-90): `PC ← 0xBFC0_0000`, `Status.BEV ← 1`, `Status.ERL ← 1`,
  `Cause.DC ← 0`, `HWREna ← 0`, `EBase` reads `0x8000_0000`, `Config.K0 ← 2`, `ErrorEPC ←`
  restart PC. Registers without a defined reset state keep their value (pin);
  for a power-on reset they are 0 (`powerOnState`), so `resetState` has
  `Status = 0x0040_0004`, `ErrorEPC = 0`. See SPEC-NOTES §9 item 10.
- **Hosted start state (environment convention, `Env.lean`)**: reset followed
  by the boot convention `bootConvention textBase`: `Status = 0x2000_0000` —
  only `CU1` set (Kernel Mode, `BEV = ERL = 0`), so programs can use the FPU —
  `$sp = 0x7FFF_EFFC`, `pc = 0x0040_0000`. `Cause`, `EPC`, `BadVAddr`,
  `ErrorEPC`, `Count`, `Compare`, `HWREna` are 0; `EBase` is `0x8000_0000`. `MipsRun --reset` starts at the
  reset vector instead.
- Any other CP0 register does not decode → Reserved Instruction (a pin:
  the architecture leaves access to an unimplemented CP0 register
  implementation-dependent).

### Exception mechanism — the general exception sequence

MD00090 Vol III Rev 6.02 §6.2.3 "General Exception Processing" (p.86-88),
restricted to non-TLB exceptions, as implemented by
`Step.lean` `exceptionEntry` (the Interrupt exception is `exceptionEntry` with `ExcCode = 0`
followed by its own vector, `takeInterrupt`):

```
if Status.EXL = 0 then
    if InstructionInBranchDelaySlot then EPC ← PC of branch/jump (PC − 4); Cause.BD ← 1
    else                                 EPC ← PC of instruction;          Cause.BD ← 0
    endif
endif                      /* Status.EXL = 1: neither EPC nor Cause.BD is modified */
Cause.CE ← coprocessor unit number   /* bits 29..28; 0 unless Coprocessor Unusable */
Cause.ExcCode ← ExceptionType        /* bits 6..2; all other Cause bits unchanged */
Status.EXL ← 1
PC ← vectorBase + 0x180
```

- `InstructionInBranchDelaySlot` is `State.pendingBranch.isSome` — true
  after a taken *or* not-taken branch (Global rule 3).
- **The pending branch is abandoned** (`pendingBranch := none`): the
  handler runs sequentially from the vector; `eret` to `EPC` re-executes
  the branch.
- **`Cause.CE`** is written on every exception entry: the coprocessor unit
  number (1 or 2) for Coprocessor Unusable (§6.2.22, p.100), and 0 for
  every other exception. For those the manual says "The CE field is loaded,
  but not defined" (§6.2.3, p.87); loading 0 is a model pin.
- **`LLbit ← 0`** on every exception entry (MD00086 Vol II-A Rev 6.06, SC,
  p.350: "Exceptions between the LL and SC cause SC to fail"). StepSpec:
  `exception_clears_llBit`.
- With `Status.EXL = 1` at entry, `EPC` and `Cause.BD` are not written but
  `CE` and `ExcCode` still are, and the vector offset is still `0x180`
  (§6.2.3, p.87-88).
- **Vector** (`exceptionVector`; §6.2.2 "Exception Vector Locations",
  p.84-86; §6.2.3, p.88; §9.41, p.223-224): the general exception offset is
  `0x180`. With `Status.BEV = 0` the base is `EBase` (bits 31..12, low 12
  bits zero), so the vector is `EBase | 0x180` — `0x8000_0180` while
  `EBase` holds its reset value. With `Status.BEV = 1` the vector is
  `0xBFC0_0380` (base `0xBFC0_0200`), independent of `EBase`.
- **ExcCode values raised by the model** (Table 9.53, p.212-213):

  | ExcCode | Name | Raised by |
  |---|---|---|
  | 0 | `Int` | an enabled interrupt request, before the instruction at `pc` (`takeInterrupt`; vector offset `0x180`, or `0x200` with `Cause.IV = 1`; §6.2.26, p.102) |
  | 4 | `AdEL` | misaligned load or instruction fetch; `BadVAddr ←` the address (§6.2.9, p.92-93) |
  | 5 | `AdES` | misaligned store; `BadVAddr ←` the address (§6.2.9, p.92-93) |
  | 8 | `Sys` | `syscall`, always (§6.2.19, p.98; the hosted run performs services 1/4/10/11 instead of stepping) |
  | 9 | `Bp` | `break` (§6.2.20, p.99) |
  | 10 | `RI` | a word that does not decode (§6.2.21, p.99); a control transfer in a delay slot (pin, Global rule 3) |
  | 11 | `CpU` | a coprocessor-1 instruction with `Status.CU1 = 0` (`CE = 1`); any coprocessor-2 word (`CE = 2`) (§6.2.22, p.100) |
  | 12 | `Ov` | `add`/`addi`/`sub` signed overflow (§6.2.17, p.98) |
  | 13 | `Tr` | a trap instruction whose condition holds (§6.2.18, p.98) |
  | 15 | `FPE` | an enabled IEEE exception of an FP instruction, or `ctc1` leaving an enabled `Cause` bit or `Cause.E` set (§6.2.23, p.100) |

- On a misaligned fetch both `EPC` and `BadVAddr` hold the unaligned
  instruction address (§6.2.9, p.93).
- **No handler loaded** (hosted-run convention, `Env.lean`): when `pc` is
  the vector with `EXL = 1` and the loaded image has no word there, the
  hosted run stops with `HaltReason.unhandledException ExcCode EPC BadVAddr`.
  The processor itself would go on fetching (unloaded memory reads as 0).

StepSpec: `exceptionEntry_always`, `exceptionEntry_exl0_not_in_delay_slot`,
`exceptionEntry_exl0_in_delay_slot`, `exceptionEntry_exl1`,
`exceptionEntry_excCode`, `exceptionEntry_cause_other_bits`,
`step_misaligned_pc`, `step_reserved_instruction`,
`step_reserved_cop1_unusable`, `step_fetches_from_memory`; hosted:
`hostStep_stop`.

### teq / tne / tlt / tge / tltu / tgeu (R, trap-on-condition)

- **Encoding**: `000000 rs rt code funct` — `rs` = bits 25..21, `rt` =
  bits 20..16, **`code` = bits 15..6** (10 bits), `funct`: `tge` = `0x30`,
  `tgeu` = `0x31`, `tlt` = `0x32`, `tltu` = `0x33`, `teq` = `0x34`, `tne` =
  `0x36`. Constructors `teq` `tne` `tlt` `tge` `tltu` `tgeu`
  `(rs rt code)`. Every `code` value decodes and round-trips; "The contents
  of the code field are ignored by hardware and may be used to encode
  information for system software" (TEQ p.416), and execution ignores it.
- **Semantics**: evaluate the condition on `$rs`/`$rt` — `teq`: `==`;
  `tne`: `!=`; `tlt`: signed `<`; `tge`: signed `>=`; `tltu`: unsigned `<`;
  `tgeu`: unsigned `>=`. If it holds, take the Trap exception (ExcCode 13).
  Otherwise fall through to `pc + 4` with no CP0 state touched.
- **Errors/halts**: none beyond the exception transition (a state
  transition, not a halt).
- **Source**: MD00086 Vol II-A Rev 6.06, TEQ p.416, TGE p.418, TGEU p.421,
  TLT p.434, TLTU p.437, TNE p.438.

### break (R, unconditional trap)

- **Encoding**: `000000 code 001101` — **`code` = bits 25..6** (20 bits),
  funct `0x0d`. Constructor `break (code)`. Every `code` value decodes and
  round-trips; it is "available for use as software parameters" (BREAK
  p.109) and has no effect on execution. (`syscall (code)`, funct `0x0c`,
  carries the same 20-bit field; SYSCALL p.415.)
- **Semantics**: unconditionally takes the Breakpoint exception
  (ExcCode 9).
- **Errors/halts**: none beyond the exception transition.
- **Source**: MD00086 Vol II-A Rev 6.06, BREAK p.109.

### mfc0 / mtc0 (R, COP0 generic register move)

- **Encoding**: `010000 sub rt rd 00000000 sel` — `sub` = `00000` (`MF`) /
  `00100` (`MT`), bits 10..3 zero, `sel` = bits 2..0. Constructors `mfc0` /
  `mtc0` `(rt rd sel)`. **Decode requires bits 10..3 = 0 and `(rd, sel)` in
  the table above**; anything else (e.g. `mfc0 $t0, $12, 3` = `SRSMap`,
  word `0x40086003`) does not decode → Reserved Instruction.
- **`mfc0 rt, rd, sel`**: `$rt ←` the register's value (`PRId`, `Config1`, `Config2`, `Config3`,
  and all of `Config` except `K23`/`KU`/`K0` are the constants above; `EBase` reads `10 ‖ ExceptionBase ‖
  0^12`; `Cause` reads `TI`/`IP7` from the timer; `Count` reads the value the step started with).
- **`mtc0 rt, rd, sel`**: writes through the register's write mask:
  `Status ← $rt & 0x3040FF17` (writes `UM` and `CU0` too);
  `Cause ← (Cause & ~0x08800300) | ($rt & 0x08800300)`; `EPC ← $rt`;
  `ErrorEPC ← $rt`; `EBase ← 0x80000000 | ($rt & 0x3FFFF000)`;
  `Config ← K23 = $rt[30:28], KU = $rt[27:25], K0 = $rt[2:0]` (all other `Config` bits ignored);
  `Count ← $rt` (then the step's timer tick advances it unless `DC = 1`);
  `Compare ← $rt` and `Cause.TI ← 0` ("Writing a value to the Compare register, as a side
  effect, clears the timer interrupt", MD00090 Vol III Rev 6.02 §9.30, p.187);
  `HWREna ← $rt & 0xF`; `BadVAddr`, `PRId`, `Config1`, `Config2`, `Config3`: ignored (read-only).
- **Errors/halts**: Coprocessor Unusable (`Cause.CE = 0`) when coprocessor 0 is not usable
  (User Mode with `Status.CU0 = 0`; MD00090 Vol III Rev 6.02 §3.5.3 p.23,
  §6.2.22 p.100; this page: "Exceptions: Coprocessor Unusable", MFC0
  p.266, MTC0 p.291; `cp0_instruction_user_mode_unusable`). Unmodeled `(rd, sel)`:
  Reserved Instruction in Kernel Mode, Coprocessor Unusable when CP0 is not usable
  (the word does not decode; `step_reserved_cop0_unusable`). `SRSMap` (12,3) does not decode: with `SRSCtl.HSS = 0`
  "the results of a software read or write of this register are UNPREDICTABLE" (MD00090 Vol III Rev 6.02 §9.35, p.207),
  and Reserved Instruction is one such result (pin, SPEC-NOTES).
- **Lean**: `mfc0_spec_raw`, `mtc0_spec_raw` (Kernel Mode or `CU0 = 1`:

  `hcp0 : cp0Usable s = true`), `mtc0_status_enters_user_mode`; timer registers:
  `mtc0_count_spec`, `mtc0_compare_clears_ti`, `hwrena_write_masked`, `causeValue_timer` (`Timer.lean`).
- **Tests**: `tests/oracle/timer_count_compare.asm` (Count/Compare R/W, DC, TI and IP7, Compare write
  clears TI; QEMU 24Kf PASS), `rdhwr_kernel.asm` (HWREna write mask), `irq_timer.asm` (IntCtl, SRSCtl reads),
  `rdpgpr_wrpgpr.asm` (SRSCtl write of 0).
- **Source**: MD00086 Vol II-A Rev 6.06, MFC0 p.266, MTC0 p.290-291.

### rdhwr (R, SPECIAL3, Release 2)

- **Encoding**: `011111 00000 rt rd 00000 111011` (SPECIAL3, `rs` = 0, bits 10..6 = 0, funct `0x3b`;
  MD00086 Vol II-A Rev 6.06, RDHWR, p.332; the Release 6 `sel` field in bits 8..6 does not exist before
  Release 6, Rev 2.50 RDHWR p.229, so a nonzero value does not decode). Constructor `rdhwr (rt rd)`;
  assembler `rdhwr $rt, $rd` (`rdhwr $3, $29` = `0x7c03e83b`).
- **Semantics**: `GPR[rt] ← HWR[rd]` when register `rd` is implemented and access is allowed (`hwrValue`,
  `rdhwrAllowed`, `Step.lean`):

  | `rd` | Register | Value in the model |
  |---|---|---|
  | 0 | `CPUNum` | `EBase.CPUNum` = 0 (one processor) |
  | 1 | `SYNCI_Step` | 0: "zero if no caches need be synchronized" (p.332); the model has no caches (`Config1.IL = DL = 0`) |
  | 2 | `CC` | `Count`, the value the step started with |
  | 3 | `CCRes` | 1: `Count` advances once per step and one step is the model's cycle ("1: CC register increments every CPU cycle", p.332) |
  | 4, 5 | `PerfCtr`, `XNP` | Release 6 only: Reserved Instruction |
  | 6..28 | reserved | "Access results in a Reserved Instruction Exception" (p.333) |
  | 29 | `ULR` | UserLocal is not implemented (pre-Release 6 "Recommended", MD00090 Vol III Rev 6.02 §9.11, p.143; it "only exists if the Config3ULRI register field is set", and the model's Config3 reads 0, `ULRI` = 0): Reserved Instruction |
  | 30, 31 | implementation-dependent | none implemented: Reserved Instruction (p.333) |

- **Access** (Restrictions, p.333): "Access to the specified hardware register is enabled if Coprocessor 0
  is enabled, or if the corresponding bit is set in the HWREna register. If access is not allowed or the
  register is not implemented, a Reserved Instruction Exception is signaled." Coprocessor 0 is enabled in
  Kernel Mode or with `Status.CU0 = 1` (`cp0Usable`; MD00090 Vol III Rev 6.02 §3.5.3, p.23). RDHWR is not a
  coprocessor-0 instruction: it never raises Coprocessor Unusable ("Exceptions: Reserved Instruction", p.334).
- **Lean**: `rdhwr_spec_raw`, `rdhwr_reserved_unimplemented`, `rdhwr_reserved_not_enabled`, `rdhwr_allowed`,
  `rdhwr_cc_reads_count`, `hwrValue_cpuNum`, `hwrValue_synciStep`, `hwrValue_cc`, `hwrValue_ccRes`,
  `hwrValue_unimplemented` (`Semantics/Specs/Timer.lean`).
- **Tests**: `tests/oracle/rdhwr_kernel.asm`, `rdhwr_user_hwrena.asm`, `rdhwr_user_cu0.asm` (QEMU 24Kf; QEMU
  returns a value for `rd` 29 in Kernel Mode with Config3 = 0: declared deviation, SPEC-NOTES §10);
  `Semantics/Tests/StepExceptionTests.lean`, `AsmTests.lean`.
- **Source**: MD00086 Vol II-A Rev 6.06, RDHWR, p.332-334; MD00090 Vol III Rev 6.02 §9.23 HWREna,
  Table 9.39-9.40, p.175-176.

### di / ei (R, COP0 `MFMC0`, Release 2)

- **Encoding**: `010000 01011 rt 01100 00000 sc 00 000` — `rd` = 12
  (`Status`), bit 5 = `sc`: 0 for `di` (`0x41606000 | rt << 16`), 1 for
  `ei` (`0x41606020 | rt << 16`); all other low bits zero. Constructors
  `di (rt)`, `ei (rt)`.
- **Semantics**: `$rt ← Status` (the value *before* the change), then
  `Status.IE ← 0` (`di`) / `1` (`ei`). With `rt = 0` the old value is
  discarded. `IE = 1` enables interrupts; the change is seen by the next step's interrupt check
  (the execution hazard of MD00090 Vol III Rev 6.02 Table 6.5, p.82, cleared at once: pin), so after `ei`
  a pending, unmasked request is taken before the next instruction (`tests/oracle/irq_software.asm`).
- **Errors/halts**: Coprocessor Unusable (`Cause.CE = 0`) when coprocessor 0 is not usable
  (User Mode with `Status.CU0 = 0`; MD00090 Vol III Rev 6.02 §3.5.3 p.23,
  §6.2.22 p.100; this page: "Exceptions: Coprocessor Unusable", DI
  p.164, EI p.176; "If access to Coprocessor 0 is not enabled, a Coprocessor
  Unusable Exception is signaled", DI p.164).
- **Lean**: `di_spec_raw`, `ei_spec_raw`.
- **Source**: MD00086 Vol II-A Rev 6.06, DI p.164, EI p.176.

### eret (R, COP0 exception return)

- **Encoding**: `010000 1 000 0000 0000 0000 0000 011000` (`0x42000018`);
  bits 24..6 must be zero.
- **Semantics** (MD00086 Vol II-A Rev 6.06, ERET, p.177-178, Operation;
  the Release 5 `eretnc` variant is not modeled):
  ```
  if Status.ERL = 1 then PC ← ErrorEPC; Status.ERL ← 0
  else                   PC ← EPC;      Status.EXL ← 0
  LLbit ← 0
  ```
  ("An ERET placed between an LL and SC instruction will always cause the
  SC to fail.") No delay slot: `pc` changes in this step. The shadow-set step
  "if (ArchitectureRevision() ≥ 2) and (SRSCtlHSS ≠ 0) and (StatusBEV = 0) then SRSCtlCSS ← SRSCtlPSS"
  (p.177) never applies: `SRSCtl.HSS = 0` (and `CSS = PSS = 0`).
- **Errors/halts**: `eret` in a branch delay slot is UNDEFINED in the
  architecture ("Pre-Release 6: The operation of the processor is UNDEFINED
  if an ERET is executed in the delay slot of a branch or jump
  instruction", p.177); the model raises Reserved Instruction (Global
  rule 3), in every mode. Outside a delay slot: Coprocessor Unusable (`Cause.CE = 0`) when coprocessor 0 is not usable
  (User Mode with `Status.CU0 = 0`; MD00090 Vol III Rev 6.02 §3.5.3 p.23,
  §6.2.22 p.100; this page: "Exceptions: Coprocessor Unusable", p.178).
  `eret` with `Status.ERL = 0`, `EXL = 1`, `UM = 1` returns to User Mode.
- **Lean**: `eret_spec_raw`, `eret_clears_llBit`,
  `eret_in_delay_slot_reserved_instruction`, `eret_to_user_mode`.

### wait (R, COP0 enter standby mode)

Ground truth: MD00086 Vol II-A Rev 6.06, WAIT, p.442-443.

- **Encoding**: `opcode=010000` (COP0), bit 25 (`CO`) = 1, bits 24..6 =
  implementation-dependent `code`, `funct=100000` (0x20). Every `code`
  value decodes ("A value of zero for code bits is the default and must be
  valid in all implementations") and is carried in the constructor
  `wait (code)`, so it round-trips (`code = 0` is `0x42000020`). Execution
  ignores it.
- **Semantics**: "The WAIT instruction is implemented by stalling the pipeline at the completion of
  the instruction and entering a lower power mode. The pipeline is restarted when an external event,
  such as an interrupt or external request occurs, and execution continues with the instruction
  following the WAIT instruction" (p.442); pre-Release 6 Operation "I: Enter implementation dependent
  lower power mode / I+1: Potential interrupt taken here" (p.442). The model: `wait` completes
  (`PC ← PC_next`) and sets `State.standby`. While in standby `step` executes nothing; `Count` keeps
  counting (pin: "Prior to Release 6, whether Count is disabled was implementation-dependent", p.442).
  An enabled interrupt is taken from standby with `EPC` = the instruction after `wait` ("EPC for the
  interrupt points at the instruction following the WAIT instruction", p.442). A request that is
  pending and not masked (`Cause.IP & Status.IM ≠ 0`) but not enabled (`IE = 0`, `EXL` or `ERL`)
  restarts the pipeline ("It is implementation-dependent whether the pipeline restarts when a
  non-enabled interrupt is requested", p.442; pin: it does, the Release 6 rule of p.443); without a
  request the processor stays in standby. Reset leaves standby. The 19-bit code selects nothing.
  (`wait_spec_raw`, `step_standby_stays`, `step_standby_restarts`, `step_standby_interrupt`;
  SPEC-NOTES §9 item 23.)
- **Errors/halts**: `wait` in a branch delay slot is UNDEFINED in the
  architecture (p. 442); the model raises Reserved Instruction (Global
  rule 3), in every mode. Outside a delay slot: Coprocessor Unusable (`Cause.CE = 0`) when coprocessor 0 is not usable
  (User Mode with `Status.CU0 = 0`; MD00090 Vol III Rev 6.02 §3.5.3 p.23,
  §6.2.22 p.100; this page: "Exceptions: Coprocessor Unusable", p.443).

### rdpgpr / wrpgpr (R, COP0, Release 2)

- **Encoding**: `010000 01010 rt rd 00000 000000` (`rdpgpr`, `rs` = `RDPGPR` = 0x0a) and
  `010000 01110 rt rd 00000 000000` (`wrpgpr`, `rs` = `WRPGPR` = 0x0e); bits 10..0 must be zero.
  Constructors `rdpgpr (rd rt)`, `wrpgpr (rd rt)`; assembler `rdpgpr $rd, $rt`, `wrpgpr $rd, $rt`
  (`rdpgpr $t0, $t1` = `0x41494000`, `wrpgpr $t0, $t1` = `0x41c94000`; llvm-mc 21 accepts them only for
  microMIPS, so the encoding oracle compares against the word built from the page).
- **Semantics**: RDPGPR "GPR[rd] ← SGPR[SRSCtlPSS, rt]" (MD00086 Vol II-A Rev 6.06, RDPGPR, p.335);
  WRPGPR "SGPR[SRSCtlPSS, rd] ← GPR[rt]" (WRPGPR, p.444). Both are "MIPS32 Release 2" and "In implementations
  prior to Release 2 of the Architecture, this instruction resulted in a Reserved Instruction exception",
  so a Release 2 processor executes them. The model implements only the normal GPRs (`SRSCtl.HSS = 0`, "only
  the normal GPRs are implemented", MD00090 Vol III Rev 6.02 Table 9.49, p.203), which "are logically
  considered shadow set zero" (§7, p.103), and `PSS = 0`: both instructions are `$rd ← $rt` (a write to
  `$zero` is ignored, `SGPR[0, 0]` being `$zero`).
- **Errors/halts**: Coprocessor Unusable (`Cause.CE = 0`) when coprocessor 0 is not usable (both pages list
  "Coprocessor Unusable"; MD00090 Vol III Rev 6.02 §6.2.22, p.100). The pages also list Reserved Instruction
  (the pre-Release-2 behaviour); a word with nonzero bits 10..0 does not decode and raises it.
- **Lean**: `rdpgpr_spec_raw`, `wrpgpr_spec_raw` (`Semantics/Specs/Cp0.lean`), `cp0_instruction_user_mode_unusable`.
- **Tests**: `tests/oracle/rdpgpr_wrpgpr.asm` (QEMU 24Kf PASS); `Semantics/Tests/StepExceptionTests.lean`,
  `InstructionTests.lean`, `AsmTests.lean`.
- **Source**: MD00086 Vol II-A Rev 6.06, RDPGPR p.335, WRPGPR p.444.

## Flagged MARS deviations (summary)

1. **`div`/`divu` by zero**: no exception, `hi`/`lo` left unchanged
   (explicit source comment citing the MIPS32 spec over the COD3 textbook
   framing). `Exceptions.DIVIDE_BY_ZERO_EXCEPTION` exists but is dead code.
2. **Branch delay slots** (`j`, `jal`, `beq`, `bne`, `blez`, `bgtz`):
   MARS's `DelayedBranching` setting defaults to `false`, so by default PC
   jumps to the target immediately with no delay-slot instruction executed.
   Our semantics does **not** follow that default: it implements real
   MIPS32's architecturally-mandated one-instruction delay slot instead
   (Global rule 3; SPEC-NOTES \u00a79 item 1) — the one case in this reference
   where we deliberately diverge from MARS's default configuration rather
   than documenting it as a quirk to match.
3. **`lw`/`sw` offset sign-extension asymmetry** (flagged as a source
   ambiguity requiring a Lean-spec decision, not a confirmed intentional
   deviation): unlike `lb`/`lh`/`lhu`/`lbu`/`sh`/`addi`/`addiu`/`slti`/
   `sltiu`, which all inline `operands[n] << 16 >> 16` to sign-extend their
   immediate/offset field defensively, `lw` and `sw`'s `simulate()` bodies
   use the raw operand value with no inline sign-extension. This is
   invisible for assembler-produced programs (the operand is already a
   correctly-signed Java `int` by the time `simulate()` runs) but would
   zero-extend instead of sign-extend a negative offset for an instruction
   constructed directly from a raw 32-bit encoding (self-modifying code /
   direct binary loading), since `ProgramStatement`'s binary-decode
   constructor only sign-extends the branch-displacement operand, not
   generic I-format offsets.

Everything else checked (`add`/`addi`/`sub` overflow trapping, `addu`/
`subu`/`mult`/`multu` never trapping, `andi`/`ori`/`xori` zero-extending,
`sltiu` sign-extending its immediate, `$zero` write-ignore, big-endian
memory) matches textbook/ISA-spec MIPS behavior and is marked "none" above.

---

## Floating point (coprocessor 1)

Ground truth: MD00086 Vol II-A Rev 6.06 (instruction pages, cited per
entry), MD00082 Vol I-A Rev 6.01 chapter 6 "FPU Programming Model" and
MD00090 Vol III Rev 6.02 (exceptions). Profile: a 32-bit FPU in the
even/odd register-pair model (`Status.FR = 0`; Vol I-A §6.4.1, p.84),
single (S), double (D) and word (W) data types, legacy NaN encoding and
arithmetic `abs`/`neg` (`FIR.Has2008 = 0`). Model: `Semantics/FpOps.lean`
(`Mips.Fp`, arithmetic on bit patterns; no host float is involved) and the
`.mfc1` … `.bc1tl` arms of `execInstr` in `Semantics/Step.lean`.

### FPU state

- **`State.fpRegs`** — 32 raw 32-bit words `FPR[0..31]`; none is hardwired
  to zero. A single uses one register. A double named `fN` occupies the
  pair `FPR[N]` (low word) / `FPR[N+1]` (high word). An odd `N` for a
  double is UNPREDICTABLE in the architecture; the model uses the pair
  `(N, N+1 mod 32)` regardless (pin; `readFpD`/`writeFpD`).
- **`State.fcsr`** — the Floating Point Control and Status Register, CP1
  control register 31 (Vol I-A §6.5.4, Figure 6.14 / Table 6.8, p.92-95):

  | Bits | Field | Model |
  |---|---|---|
  | 31..25 | `FCC7..FCC1` | condition codes 7..1 |
  | 24 | `FS` | flush to zero (see "Rounding and exceptions") |
  | 23 | `FCC0` | condition code 0 |
  | 22..18 | `Impl`, reserved, `ABS2008`/`NAN2008` | read as zero, ignore writes |
  | 17..12 | `Cause` (`E V Z O U I`) | exceptions of the most recent arithmetic operation |
  | 11..7 | `Enables` (`V Z O U I`) | trap enables |
  | 6..2 | `Flags` (`V Z O U I`) | sticky flags |
  | 1..0 | `RM` | 0 nearest-even, 1 toward zero, 2 toward +∞, 3 toward −∞ |

- **Initial values (environment conventions, `initialState`)**: all FPRs 0;
  `FCSR = 0` (round to nearest, nothing enabled, flags, cause and all eight
  condition codes clear, `FS = 0`) — the manual makes the reset state of
  every FCSR field "Undefined" (Table 6.8, p.92-95); `Status = 0x2000_0000`
  (`CU1 = 1`), so programs can use the FPU without first enabling it.

### Coprocessor Unusable

Every COP1 and COP1X instruction (including `prefx`), `lwc1`/`swc1`/`ldc1`/
`sdc1`, and the GPR conditional moves `movf`/`movt` (SPECIAL `MOVCI`) raise
**Coprocessor Unusable** (ExcCode 11, `Cause.CE = 1`) and do nothing else
when `Status.CU1 = 0` (MD00090 Vol III Rev 6.02 §6.2.22, p.100; `usesCop1`,
`takeCoprocessorUnusable`). The check precedes everything else the
instruction does (alignment, FCSR update), but comes after the
delay-slot rule (Reserved Instruction) for an FP branch in a delay slot.

Words that do not decode:

- COP1 (opcode `0x11`), COP1X (`0x13`) or SPECIAL/`MOVCI` (funct `0x01`)
  space (`isCop1Word`): Coprocessor Unusable (`CE = 1`) when `CU1 = 0`,
  Reserved Instruction when `CU1 = 1` (Vol III §6.2.21, p.99: "… assuming
  that access to the coprocessor is allowed. If access to the coprocessor is
  not allowed, a Coprocessor Unusable Exception occurs instead"). StepSpec:
  `step_reserved_cop1_unusable`.
- Coprocessor 2 space — opcodes `0x12` (COP2), `0x32` (LWC2), `0x36`
  (LDC2), `0x3a` (SWC2), `0x3e` (SDC2) (`isCop2Word`): always Coprocessor
  Unusable with `Cause.CE = 2` (Vol III §6.2.22, p.100). The model has no
  coprocessor 2 (`Config1.C2 = 0`) and `Status.CU2` reads 0.

### Rounding and exceptions

Every arithmetic instruction computes the exact result and rounds it once
to the destination format under `FCSR.RM` (`Format.roundCore`,
`Format.roundEnv`), then finishes through `fpFinishS`/`fpFinishD`/
`fpFinishCmp` (`Mips.Fp.fpUpdate`):

- `FCSR.Cause` ← exactly the IEEE exceptions this operation raised
  (`E` cleared; an operation raising nothing clears `Cause`). Vol I-A
  §6.7.1, p.99: "The Cause bits are written during each floating point
  arithmetic operation".
- If one of them has its `Enables` bit set: **Floating Point exception**
  (ExcCode 15, MD00090 Vol III Rev 6.02 §6.2.23, p.100) through the general
  exception sequence. The destination (FPR or condition code) is **not
  written** and `FCSR.Flags` is unchanged (Vol I-A §6.7.1, p.98-99: "a trap
  occurs before the instruction that causes the trap … can complete and
  write its results"; "instructions that trap do not update the Flag bits").
- Otherwise the exceptions are ORed into `FCSR.Flags`, the IEEE default
  result is written and execution continues.

Exception conditions (Vol I-A §6.7.2, p.99-102):

| Flag | Raised when | Default result |
|---|---|---|
| V Invalid | an SNaN operand; ∞ − ∞; 0 × ∞; 0/0; ∞/∞; `sqrt` of a value below 0 (−0 excepted); a signaling compare with any NaN; float→word of NaN, ±∞ or an out-of-range value; `abs`/`neg` of any NaN (§6.7.2.1, p.100) | a quiet NaN (float→word: `0x7FFFFFFF`; compare: the Boolean result) |
| Z Divide by zero | finite nonzero ÷ zero (§6.7.2.2, p.100) | correctly signed ∞ |
| O Overflow | the result rounded with unbounded exponent exceeds the largest finite number (§6.7.2.5, p.102) | ±∞ or ± largest finite, by rounding direction (Table 6.14, p.100) |
| U Underflow | the result is tiny — tininess detected **after rounding** — and inexact; or tiny, when the Underflow trap is enabled (§6.7.2.3, p.101) | the rounded (possibly denormal or zero) result |
| I Inexact | the rounded result differs from the exact one; or overflow without an Overflow trap (§6.7.2.6, p.102) | the rounded result |

- **`FS = 1`** (§6.7.2.4, p.101-102): a tiny nonzero result (tininess
  detected before rounding) is replaced by a zero of the same sign and
  reported as Underflow and Inexact. Denormal *operands* are never flushed
  (implementation-dependent in the manual; pin).
- **Unimplemented Operation (`Cause.E`) is never raised by arithmetic** —
  every modeled operation is fully implemented. `Cause.E` can be set only
  by `ctc1`.

**NaN rule** (legacy encoding: a NaN whose fraction MSB is 1 is signaling,
0 is quiet). Vol I-A §6.3.1.4 (p.81): "SNaN operands cause the Invalid
Operation exception for arithmetic operations". §6.3.1.5 (p.82): a QNaN
operand makes the operation "supply a QNaN result. When possible, this QNaN
result is one of the operand QNaN values". Model (`Format.nanResult`,
`Format.nanFlags`): if any operand is a NaN, Invalid is raised iff some
operand is signaling, and the result is the **first quiet-NaN operand in
operand order (`fs` before `ft`), copied unchanged**; if no operand is a
quiet NaN, the default QNaN `0x7FBFFFFF` (single) / `0x7FF7FFFF_FFFFFFFF`
(double) (Table 6.3, p.82). The same default QNaN is the result of the
invalid operations in the table above. "First operand wins" is a model pin:
the manual does not say which operand is chosen when two are quiet NaNs.

Not arithmetic (no FCSR change, no IEEE exception): `mfc1`, `mtc1`,
`mfhc1`, `mthc1`, `cfc1`, the loads/stores, `mov.fmt`, `movf.fmt`/
`movt.fmt`/`movn.fmt`/`movz.fmt`, `movf`/`movt`, `prefx`, and the FP
branches.

### Encoding summary

COP1 words are `010001 fmt ft fs fd funct` (opcode `0x11`); the `fmt`/`rs`
field is `S` = `0x10`, `D` = `0x11`, `W` = `0x14`, or a sub-opcode: `MF`
`0x00`, `CF` `0x02`, `MFH` `0x03`, `MT` `0x04`, `CT` `0x06`, `MTH` `0x07`,
`BC` `0x08`. COP1X words are opcode `0x13`. A `cvt` instruction's `fmt`
names the *source* format. Unary operations require `ft = 0`, the moves
between GPRs and the FPU require bits 10..0 zero, `C.cond.fmt` requires
bits 7..6 zero and `MOVCI`/`MOVCF` bit 17 zero; a word violating this does
not decode. "Page" is the printed page of MD00086 Vol II-A Rev 6.06.

| Mnemonic | Constructor | Encoding | Semantics | Page |
|---|---|---|---|---|
| `mfc1 rt, fs` | `mfc1` | COP1, `MF` | `$rt ← FPR[fs]` | MFC1 p.267 |
| `mtc1 rt, fs` | `mtc1` | COP1, `MT` | `FPR[fs] ← $rt` | MTC1 p.292 |
| `mfhc1 rt, fs` | `mfhc1` | COP1, `MFH` | `$rt ← FPR[fs+1]` | MFHC1 p.271 |
| `mthc1 rt, fs` | `mthc1` | COP1, `MTH` | `FPR[fs+1] ← $rt` | MTHC1 p.295 |
| `cfc1 rt, fs` | `cfc1` | COP1, `CF` | `$rt ← FP_Control[fs]` | CFC1 p.129-130 |
| `ctc1 rt, fs` | `ctc1` | COP1, `CT` | `FP_Control[fs] ← $rt`; CheckFPException | CTC1 p.149-151 |
| `lwc1 ft, off(base)` | `lwc1` | opcode `0x31` | `FPR[ft] ← MEM32[addr]` | LWC1 p.236 |
| `swc1 ft, off(base)` | `swc1` | opcode `0x39` | `MEM32[addr] ← FPR[ft]` | SWC1 p.393 |
| `ldc1 ft, off(base)` | `ldc1` | opcode `0x35` | `{FPR[ft+1],FPR[ft]} ← MEM64[addr]` | LDC1 p.215 |
| `sdc1 ft, off(base)` | `sdc1` | opcode `0x3d` | `MEM64[addr] ← {FPR[ft+1],FPR[ft]}` | SDC1 p.362 |
| `lwxc1 fd, index(base)` | `lwxc1` | COP1X, funct `0x00` | `FPR[fd] ← MEM32[$base + $index]` | LWXC1 p.254 |
| `ldxc1 fd, index(base)` | `ldxc1` | COP1X, funct `0x01` | `{FPR[fd+1],FPR[fd]} ← MEM64[$base + $index]` | LDXC1 p.218 |
| `swxc1 fs, index(base)` | `swxc1` | COP1X, funct `0x08` | `MEM32[$base + $index] ← FPR[fs]` | SWXC1 p.406 |
| `sdxc1 fs, index(base)` | `sdxc1` | COP1X, funct `0x09` | `MEM64[$base + $index] ← {FPR[fs+1],FPR[fs]}` | SDXC1 p.364 |
| `prefx hint, index(base)` | `prefx` | COP1X, funct `0x0f` | no-op | PREFX p.329 |
| `add.s fd, fs, ft` | `addS` | fmt S, funct `0x00` | `fd ← fs + ft` | ADD.fmt p.34 |
| `sub.s fd, fs, ft` | `subS` | fmt S, funct `0x01` | `fd ← fs − ft` | SUB.fmt p.389 |
| `mul.s fd, fs, ft` | `mulS` | fmt S, funct `0x02` | `fd ← fs × ft` | MUL.fmt p.302 |
| `div.s fd, fs, ft` | `divS` | fmt S, funct `0x03` | `fd ← fs / ft` | DIV.fmt p.170 |
| `sqrt.s fd, fs` | `sqrtS` | fmt S, funct `0x04` | `fd ← √fs` | SQRT.fmt p.382 |
| `abs.s fd, fs` | `absS` | fmt S, funct `0x05` | `fd ← \|fs\|`, arithmetic | ABS.fmt p.32 |
| `mov.s fd, fs` | `movS` | fmt S, funct `0x06` | `fd ← fs`, raw copy | MOV.fmt p.275 |
| `neg.s fd, fs` | `negS` | fmt S, funct `0x07` | `fd ← −fs`, arithmetic | NEG.fmt p.307 |
| `round.w.s fd, fs` | `roundWS` | fmt S, funct `0x0c` | single → word, nearest-even | ROUND.W.fmt p.342 |
| `trunc.w.s fd, fs` | `truncWS` | fmt S, funct `0x0d` | single → word, toward zero | TRUNC.W.fmt p.441 |
| `ceil.w.s fd, fs` | `ceilWS` | fmt S, funct `0x0e` | single → word, toward +∞ | CEIL.W.fmt p.128 |
| `floor.w.s fd, fs` | `floorWS` | fmt S, funct `0x0f` | single → word, toward −∞ | FLOOR.W.fmt p.186 |
| `movf.s fd, fs, cc` | `movfS` | fmt S, funct `0x11`, `tf` = 0 | `if FCC[cc] = 0 then fd ← fs` | MOVF.fmt p.277 |
| `movt.s fd, fs, cc` | `movtS` | fmt S, funct `0x11`, `tf` = 1 | `if FCC[cc] = 1 then fd ← fs` | MOVT.fmt p.282 |
| `movz.s fd, fs, rt` | `movzS` | fmt S, funct `0x12` | `if $rt = 0 then fd ← fs` | MOVZ.fmt p.285 |
| `movn.s fd, fs, rt` | `movnS` | fmt S, funct `0x13` | `if $rt ≠ 0 then fd ← fs` | MOVN.fmt p.280 |
| `recip.s fd, fs` | `recipS` | fmt S, funct `0x15` | `fd ← 1.0 / fs` | RECIP.fmt p.336 |
| `rsqrt.s fd, fs` | `rsqrtS` | fmt S, funct `0x16` | `fd ← 1.0 / √fs` | RSQRT.fmt p.343 |
| `cvt.d.s fd, fs` | `cvtDS` | fmt S, funct `0x21` | single → double | CVT.D.fmt p.153 |
| `cvt.w.s fd, fs` | `cvtWS` | fmt S, funct `0x24` | single → word, per `FCSR.RM` | CVT.W.fmt p.160 |
| `c.cond.s cc, fs, ft` | `cCondS` | fmt S, funct `0x30 \| cond`, `cc` = bits 10..8 | `FCC[cc] ← fs cond ft` | C.cond.fmt p.110-113 |
| `cvt.s.w fd, fs` | `cvtSW` | fmt W, funct `0x20` | word → single, per `FCSR.RM` | CVT.S.fmt p.159 |
| `cvt.d.w fd, fs` | `cvtDW` | fmt W, funct `0x21` | word → double, exact | CVT.D.fmt p.153 |
| `add.d fd, fs, ft` | `addD` | fmt D, funct `0x00` | `fd ← fs + ft` | ADD.fmt p.34 |
| `sub.d fd, fs, ft` | `subD` | fmt D, funct `0x01` | `fd ← fs − ft` | SUB.fmt p.389 |
| `mul.d fd, fs, ft` | `mulD` | fmt D, funct `0x02` | `fd ← fs × ft` | MUL.fmt p.302 |
| `div.d fd, fs, ft` | `divD` | fmt D, funct `0x03` | `fd ← fs / ft` | DIV.fmt p.170 |
| `sqrt.d fd, fs` | `sqrtD` | fmt D, funct `0x04` | `fd ← √fs` | SQRT.fmt p.382 |
| `abs.d fd, fs` | `absD` | fmt D, funct `0x05` | `fd ← \|fs\|`, arithmetic | ABS.fmt p.32 |
| `mov.d fd, fs` | `movD` | fmt D, funct `0x06` | `fd ← fs`, raw pair copy | MOV.fmt p.275 |
| `neg.d fd, fs` | `negD` | fmt D, funct `0x07` | `fd ← −fs`, arithmetic | NEG.fmt p.307 |
| `round.w.d fd, fs` | `roundWD` | fmt D, funct `0x0c` | double → word, nearest-even | ROUND.W.fmt p.342 |
| `trunc.w.d fd, fs` | `truncWD` | fmt D, funct `0x0d` | double → word, toward zero | TRUNC.W.fmt p.441 |
| `ceil.w.d fd, fs` | `ceilWD` | fmt D, funct `0x0e` | double → word, toward +∞ | CEIL.W.fmt p.128 |
| `floor.w.d fd, fs` | `floorWD` | fmt D, funct `0x0f` | double → word, toward −∞ | FLOOR.W.fmt p.186 |
| `movf.d fd, fs, cc` | `movfD` | fmt D, funct `0x11`, `tf` = 0 | `if FCC[cc] = 0 then fd ← fs` | MOVF.fmt p.277 |
| `movt.d fd, fs, cc` | `movtD` | fmt D, funct `0x11`, `tf` = 1 | `if FCC[cc] = 1 then fd ← fs` | MOVT.fmt p.282 |
| `movz.d fd, fs, rt` | `movzD` | fmt D, funct `0x12` | `if $rt = 0 then fd ← fs` | MOVZ.fmt p.285 |
| `movn.d fd, fs, rt` | `movnD` | fmt D, funct `0x13` | `if $rt ≠ 0 then fd ← fs` | MOVN.fmt p.280 |
| `recip.d fd, fs` | `recipD` | fmt D, funct `0x15` | `fd ← 1.0 / fs` | RECIP.fmt p.336 |
| `rsqrt.d fd, fs` | `rsqrtD` | fmt D, funct `0x16` | `fd ← 1.0 / √fs` | RSQRT.fmt p.343 |
| `cvt.s.d fd, fs` | `cvtSD` | fmt D, funct `0x20` | double → single, per `FCSR.RM` | CVT.S.fmt p.159 |
| `cvt.w.d fd, fs` | `cvtWD` | fmt D, funct `0x24` | double → word, per `FCSR.RM` | CVT.W.fmt p.160 |
| `c.cond.d cc, fs, ft` | `cCondD` | fmt D, funct `0x30 \| cond`, `cc` = bits 10..8 | `FCC[cc] ← fs cond ft` | C.cond.fmt p.110-113 |
| `movf rd, rs, cc` | `movf` | SPECIAL, funct `0x01`, `tf` = 0 | `if FCC[cc] = 0 then $rd ← $rs` | MOVF p.276 |
| `movt rd, rs, cc` | `movt` | SPECIAL, funct `0x01`, `tf` = 1 | `if FCC[cc] = 1 then $rd ← $rs` | MOVT p.281 |
| `madd.s fd, fr, fs, ft` | `maddS` | COP1X, funct `0x20` | `fd ← (fs × ft) + fr` | MADD.fmt p.256-258 |
| `madd.d fd, fr, fs, ft` | `maddD` | COP1X, funct `0x21` | as `madd.s`, double | MADD.fmt p.256-258 |
| `msub.s fd, fr, fs, ft` | `msubS` | COP1X, funct `0x28` | `fd ← (fs × ft) − fr` | MSUB.fmt p.287-288 |
| `msub.d fd, fr, fs, ft` | `msubD` | COP1X, funct `0x29` | as `msub.s`, double | MSUB.fmt p.287-288 |
| `nmadd.s fd, fr, fs, ft` | `nmaddS` | COP1X, funct `0x30` | `fd ← −((fs × ft) + fr)` | NMADD.fmt p.308-309 |
| `nmadd.d fd, fr, fs, ft` | `nmaddD` | COP1X, funct `0x31` | as `nmadd.s`, double | NMADD.fmt p.308-309 |
| `nmsub.s fd, fr, fs, ft` | `nmsubS` | COP1X, funct `0x38` | `fd ← −((fs × ft) − fr)` | NMSUB.fmt p.310-311 |
| `nmsub.d fd, fr, fs, ft` | `nmsubD` | COP1X, funct `0x39` | as `nmsub.s`, double | NMSUB.fmt p.310-311 |
| `bc1f cc, offset` | `bc1f` | COP1, `BC`, `nd` = 0, `tf` = 0 | branch if `FCC[cc] = 0` | BC1F p.56-57 |
| `bc1t cc, offset` | `bc1t` | COP1, `BC`, `nd` = 0, `tf` = 1 | branch if `FCC[cc] = 1` | BC1T p.60-61 |
| `bc1fl cc, offset` | `bc1fl` | COP1, `BC`, `nd` = 1, `tf` = 0 | branch-likely if `FCC[cc] = 0` | BC1FL p.58-59 |
| `bc1tl cc, offset` | `bc1tl` | COP1, `BC`, `nd` = 1, `tf` = 1 | branch-likely if `FCC[cc] = 1` | BC1TL p.62-63 |

Every row raises Coprocessor Unusable when `Status.CU1 = 0`.

### mfc1 / mtc1 / mfhc1 / mthc1 (COP1 register moves)

- **Encoding**: `010001 sub rt fs 00000 000000`, `sub` = `MF` `00000`,
  `MT` `00100`, `MFH` `00011`, `MTH` `00111`; bits 10..0 must be zero.
  Constructors `mfc1`/`mtc1`/`mfhc1`/`mthc1` `(rt fs)`.
- **Semantics**: raw 32-bit moves, no conversion, FCSR untouched.
  `mfc1`: `$rt ← FPR[fs]`; `mtc1`: `FPR[fs] ← $rt`. `mfhc1`/`mthc1`
  (Release 2) access the high word of the double in `fs`, which is
  `FPR[fs+1]` with `FR = 0`: `$rt ← FPR[fs+1]` / `FPR[fs+1] ← $rt`
  (`mthc1` leaves `FPR[fs]` unchanged). "The results are UNPREDICTABLE if
  StatusFR = 0 and fs is odd" (MFHC1 p.271, MTHC1 p.295); the model uses
  `FPR[fs+1 mod 32]` regardless (pin).
- **Exceptions**: Coprocessor Unusable.
- **Source**: MD00086 Vol II-A Rev 6.06, MFC1 p.267, MTC1 p.292, MFHC1
  p.271, MTHC1 p.295.

### cfc1 / ctc1 (COP1 control register moves)

- **Encoding**: `010001 00010 rt fs 00000 000000` (`cfc1`, `CF`),
  `010001 00110 rt fs 00000 000000` (`ctc1`, `CT`); bits 10..0 must be
  zero. Constructors `cfc1`/`ctc1` `(rt fs)`; `fs` is a control register
  number.
- **Registers** (`Mips.Fp.readControl`/`writeControl`; views of the one
  `State.fcsr`):

  | `fs` | Register | `cfc1` reads | `ctc1` writes |
  |---|---|---|---|
  | 0 | `FIR` | `0x00330000` | ignored (read-only) |
  | 25 | `FCCR` | `FCC7..FCC0` in bits 7..0 | the eight condition codes, from bits 7..0 |
  | 26 | `FEXR` | `Cause` (bits 17..12) and `Flags` (6..2) | `Cause` and `Flags` |
  | 28 | `FENR` | `Enables` (11..7), `FS` (bit 2), `RM` (1..0) | `Enables`, `FS`, `RM` |
  | 31 | `FCSR` | the whole register | every bit except 22..18 |

- **`ctc1`**: after the write, `CheckFPException`: if `Cause.E` is set, or
  some `Cause` bit is set whose `Enables` bit is set, the Floating Point
  exception (ExcCode 15) is taken — "The register is written before the
  exception occurs" (CTC1 p.149): the new FCSR value is kept, and `EPC`
  addresses the `ctc1` (or the branch, in a delay slot). Otherwise
  execution continues.
- **Pins**: any other `fs` is UNPREDICTABLE before Release 6 ("the result
  is UNPREDICTABLE if fs specifies a register that does not exist", CFC1
  p.129, CTC1 p.149) — `cfc1` reads 0 and `ctc1` writes nothing; the
  Operation's `CheckFPException()` after the UNPREDICTABLE arm still runs
  (CTC1 p.150: only the `UFR`/`UNFR` arm ends the instruction), so an FCSR
  already holding an enabled Cause bit (or `Cause.E`) traps. Nonzero bits outside the written field (FCCR bits
  31..8, FEXR/FENR bits outside the fields above, FCSR bits 22..18) make
  the write UNPREDICTABLE in the manual (CTC1 p.150); the model ignores
  those bits.
- **`FIR`** (Vol I-A §6.5.1, p.87-90) = `0x00330000`: `S` (bit 16), `D`
  (17), `W` (20) and `L` (21) implemented; `F64` (22) = 0, a 32-bit FPU;
  `Has2008` (23) = 0; `PS`, `3D`, `UFRP`, `FREP`, `Impl`, `ProcessorID`,
  `Revision` zero. **`L` = 1 because the allowed subsets require it** (Vol II-A
  Rev 6.06 §3.1 p.30; Vol I-A Rev 6.01 Table 6.4 p.85: "FIRD=1 and FIRL=1
  required"), although the L-format instruction pages call the result
  "UNPREDICTABLE if the processor is executing in the FR=0 32-bit FPU
  register model" (CVT.L.fmt, p.154); the L-format instructions stay
  undecoded (Reserved Instruction), a pin of that UNPREDICTABLE result
  (SPEC-NOTES §9 item 13).
- **Exceptions**: Coprocessor Unusable; Floating Point (`ctc1`).
- **Source**: MD00086 Vol II-A Rev 6.06, CFC1 p.129-130, CTC1 p.149-151;
  MD00082 Vol I-A Rev 6.01 §6.5.5-6.5.7 (FCCR, FEXR, FENR), p.96-97.

### lwc1 / swc1 / ldc1 / sdc1 (FP load/store)

- **Encoding**: I-type, `opcode base ft offset`; opcodes `0x31` (`lwc1`),
  `0x39` (`swc1`), `0x35` (`ldc1`), `0x3d` (`sdc1`). Constructors
  `(rs ft imm)`.
- **Semantics**: `addr = $base + sext16(offset)`; raw bits, FCSR untouched.
  `lwc1`/`swc1` move one word to/from `FPR[ft]`. `ldc1`/`sdc1` move a
  big-endian doubleword: the word at `addr` is the high half (`FPR[ft+1]`),
  the word at `addr + 4` the low half (`FPR[ft]`). The stores clear `LLbit`
  (pin, see the `ll`/`sc` section).
- **Exceptions**: Coprocessor Unusable. Address Error (`AdEL` for loads,
  `AdES` for stores, `BadVAddr = addr`): `lwc1`/`swc1` when `addr mod 4 ≠
  0`; `ldc1`/`sdc1` when `addr mod 8 ≠ 0` — "An Address Error exception
  occurs if EffectiveAddress2..0 ≠ 0 (not doubleword-aligned)" (LDC1 p.215,
  SDC1 p.362). On an exception nothing is written.
- **Source**: MD00086 Vol II-A Rev 6.06, LWC1 p.236, SWC1 p.393, LDC1
  p.215, SDC1 p.362.

### lwxc1 / ldxc1 / swxc1 / sdxc1 / prefx (COP1X indexed)

- **Encoding** (opcode `010011`, Release 2): loads `base index 00000 fd
  funct` (`lwxc1` `000000`, `ldxc1` `000001`); stores `base index fs 00000
  funct` (`swxc1` `001000`, `sdxc1` `001001`); `prefx` `base index hint
  00000 001111`. The `00000` field must be zero. Constructors `lwxc1`/
  `ldxc1` `(fd index base)`, `swxc1`/`sdxc1` `(fs index base)`, `prefx`
  `(hint index base)`.
- **Semantics**: as `lwc1`/`ldc1`/`swc1`/`sdc1` with `addr = $base +
  $index`. `prefx` is a no-op: no address is formed and no state changes.
- **Exceptions**: Coprocessor Unusable (all five, `prefx` included: it is a
  COP1X instruction). Address Error as for the displacement forms: word
  alignment for `lwxc1`/`swxc1`, doubleword alignment for `ldxc1`/`sdxc1`
  (LDXC1 p.218, SDXC1 p.364). `prefx` never raises an addressing exception.
- **Source**: MD00086 Vol II-A Rev 6.06, LWXC1 p.254, LDXC1 p.218, SWXC1
  p.406, SDXC1 p.364, PREFX p.329.

### add.s / sub.s / mul.s / div.s / sqrt.s / add.d / sub.d / mul.d / div.d / sqrt.d (COP1 arithmetic)

- **Encoding**: `010001 fmt ft fs fd funct`, funct `0x00` add, `0x01` sub,
  `0x02` mul, `0x03` div, `0x04` sqrt (`ft = 0`). Constructors `addS`
  `subS` `mulS` `divS` `(fd fs ft)`, `sqrtS` `(fd fs)`, and the `D` forms.
- **Semantics**: the exact result, rounded once under `FCSR.RM`; flags,
  traps and NaN handling as in "Rounding and exceptions". Special cases:
  ∞ − ∞, 0 × ∞, 0/0, ∞/∞ → default QNaN with Invalid; finite nonzero ÷ 0 →
  correctly signed ∞ with Divide by zero; `sqrt(−0) = −0`, `sqrt` of any
  other negative value → default QNaN with Invalid ("If the value in FPR fs
  corresponds to −0, the result is −0", "If the value in FPR fs is less
  than 0, an Invalid Operation condition is raised", SQRT.fmt p.382). An
  exact zero sum of operands of opposite sign is `+0`, or `−0` when
  rounding toward −∞.
- **Exceptions**: Coprocessor Unusable; Floating Point (enabled V, Z, O, U
  or I).
- **Source**: MD00086 Vol II-A Rev 6.06, ADD.fmt p.34, SUB.fmt p.389,
  MUL.fmt p.302, DIV.fmt p.170, SQRT.fmt p.382.

### abs.s / neg.s / abs.d / neg.d (COP1, arithmetic)

- **Encoding**: fmt S/D, funct `0x05` (abs), `0x07` (neg), `ft = 0`.
  Constructors `absS` `negS` `absD` `negD` `(fd fs)`.
- **Semantics**: with `FIR.Has2008 = 0` "this operation is arithmetic. For
  this case, any NaN operand signals invalid operation" (ABS.fmt p.32;
  NEG.fmt p.307). **Any** NaN operand, quiet or signaling, raises Invalid;
  untrapped, a quiet NaN gives the operand with its sign bit cleared (abs)
  or flipped (neg) — "The value is negated by changing the sign bit value"
  (p.307), reading A′ of SPEC-NOTES §9 item 21 (since 7R; the operand was
  returned unchanged before) — and a signaling NaN gives the default QNaN.
  Otherwise the sign bit is cleared (abs) or flipped (neg); for a double that
  is bit 31 of `FPR[fs+1]`.
- **Exceptions**: Coprocessor Unusable; Floating Point (enabled V).
- **Source**: MD00086 Vol II-A Rev 6.06, ABS.fmt p.32, NEG.fmt p.307.

### recip.s / recip.d / rsqrt.s / rsqrt.d (COP1, Release 2)

- **Encoding**: fmt S/D, funct `0x15` (recip), `0x16` (rsqrt), `ft = 0`.
  Constructors `recipS` `recipD` `rsqrtS` `rsqrtD` `(fd fs)`.
- **Semantics (pin)**: the manual leaves the accuracy
  implementation-dependent (within one ULP for `recip`, two for `rsqrt`)
  and says it "is implementation dependent whether the result is affected
  by the current rounding mode" (RECIP.fmt p.336; RSQRT.fmt p.343). The
  model computes `recip x` as `1.0 / x` with `div.fmt`, and `rsqrt x` as
  `sqrt.fmt` followed by `1.0 / ·` with `div.fmt` (two roundings, flags of
  both steps ORed), under the current FCSR. So `recip(±0) = ±∞` with Divide
  by zero, `rsqrt(±0) = ±∞` with Divide by zero, `rsqrt` of a negative
  nonzero value is the default QNaN with Invalid.
- **Exceptions**: Coprocessor Unusable; Floating Point.
- **Source**: MD00086 Vol II-A Rev 6.06, RECIP.fmt p.336, RSQRT.fmt p.343.

### madd.s / msub.s / nmadd.s / nmsub.s / madd.d / msub.d / nmadd.d / nmsub.d (COP1X, Release 2)

- **Encoding**: `010011 fr ft fs fd funct`, funct = operation (bits 5..3:
  `100` madd, `101` msub, `110` nmadd, `111` nmsub) ‖ format (bits 2..0:
  `000` S, `001` D). Constructors `maddS` `msubS` `nmaddS` `nmsubS`
  `maddD` `msubD` `nmaddD` `nmsubD` `(fd fr fs ft)`.
- **Semantics**: **unfused, separate operations** ("The results and flags
  are as if separate floating-point multiply and add instructions were
  executed", MADD.fmt p.256; "... and negate", NMADD.fmt p.308). Printed
  operand order: `madd` `(fs × ft) + fr`, `msub` `(fs × ft) − fr`, `nmadd`
  `−(fr + (fs × ft))`, `nmsub` `−((fs × ft) − fr)`. The product is rounded
  under `FCSR.RM` with the multiply's result and exception conditions; then
  the add/subtract of the rounded product, rounded, the same way;
  `nmadd`/`nmsub` then the arithmetic `neg.fmt` (a NaN sum raises Invalid
  and its sign is flipped). The FCSR is per instruction (Wave 12a, audit
  B1/B2): after each operation Cause = the union of the conditions of the
  operations so far ("set to 1 if the corresponding exception condition
  arises during the execution of an instruction", MD00082 Vol I-A Rev 6.01
  Table 6.8, p.94) and the trap check is made; a trapping operation stops
  the instruction with no FPR written and Flags unchanged ("instructions
  that trap do not update the Flag bits", §6.7.1, p.99); otherwise, after
  the last operation, Flags |= Cause ("The Cause bits are ORed into the Flag
  bits if no exception is taken", MADD.fmt p.256). Model: `fpStep` +
  `fpFinishS/D`, `Mips.Fp.accFlags`; reference `Mips.Fp.MaddSpec`. (7R–Wave 11:
  Cause was the last operation's and Flags were ORed per operation.) NaN
  operand order (first QNaN): `fs`, `ft` for the multiply, then
  the printed order of the add/subtract.
- **Exceptions**: Coprocessor Unusable; Floating Point.
- **Source**: MD00086 Vol II-A Rev 6.06, MADD.fmt p.256-258, MSUB.fmt
  p.287-288, NMADD.fmt p.308-309, NMSUB.fmt p.310-311.

### cvt.w.s / cvt.w.d / round.w.s / round.w.d / trunc.w.s / trunc.w.d / ceil.w.s / ceil.w.d / floor.w.s / floor.w.d (COP1 float → word)

- **Encoding**: fmt S/D, `ft = 0`, funct `0x24` (cvt.w), `0x0c` (round.w),
  `0x0d` (trunc.w), `0x0e` (ceil.w), `0x0f` (floor.w). Constructors `cvtWS`
  `roundWS` `truncWS` `ceilWS` `floorWS` and `cvtWD` `roundWD` `truncWD`
  `ceilWD` `floorWD` `(fd fs)`.
- **Semantics** (`Format.toW32`): the source is rounded to an integer —
  `cvt.w` in the direction of `FCSR.RM`, `round.w` to nearest-even,
  `trunc.w` toward zero, `ceil.w` toward +∞, `floor.w` toward −∞ — and the
  32-bit two's-complement result is written to `FPR[fd]` (one register,
  also for a double source). Inexact is raised iff the source was not an
  integer. If the source is a NaN or ±∞, or the rounded value is outside
  `[−2^31, 2^31 − 1]` (either sign), Invalid is raised and the result is
  `0x7FFFFFFF` (Vol I-A Table 6.3, p.82; ROUND.W.fmt p.342: on cores with
  `FCSR.NAN2008 = 0` the default result is 2^31−1).
- **Manual typo**: CVT.W.fmt p.160 prints that default result as 2^63−1.
  That is the longword value; it cannot be stored in a word. ROUND.W.fmt
  p.342, TRUNC.W.fmt p.441, CEIL.W.fmt p.128, FLOOR.W.fmt p.186 and Vol I-A
  Table 6.3 all say 2^31−1 (`0x7FFFFFFF`), which the model uses.
- **MARS divergence**: MARS 4.5's `cvt.w.s` is a Java `(int)` cast
  (`mars/mips/instructions/InstructionSet.java` in `vendor/mars/Mars4_5.jar`,
  line 2421), i.e. it always truncates; the model follows `FCSR.RM`
  (round to nearest-even by default).
- **Exceptions**: Coprocessor Unusable; Floating Point (enabled V or I).
- **Source**: MD00086 Vol II-A Rev 6.06, CVT.W.fmt p.160, ROUND.W.fmt
  p.342, TRUNC.W.fmt p.441, CEIL.W.fmt p.128, FLOOR.W.fmt p.186.

### cvt.s.d / cvt.d.s / cvt.s.w / cvt.d.w (COP1 format conversion)

- **Encoding**: `cvt.s.d` fmt D funct `0x20`; `cvt.d.s` fmt S funct `0x21`;
  `cvt.s.w` fmt W funct `0x20`; `cvt.d.w` fmt W funct `0x21`; `ft = 0`.
  Constructors `cvtSD` `cvtDS` `cvtSW` `cvtDW` `(fd fs)`.
- **Semantics**: `cvt.d.s` is exact for every non-NaN input. `cvt.s.d`
  rounds under `FCSR.RM` and can raise Overflow, Underflow and Inexact.
  `cvt.s.w` converts the signed word in `FPR[fs]`, rounding under `FCSR.RM`
  (Inexact when the value needs more than 24 significant bits). `cvt.d.w`
  is exact and raises nothing. ±∞ converts to ±∞.
- **NaN**: a signaling NaN gives the destination's default QNaN with
  Invalid. A quiet NaN is propagated without an exception, keeping its sign
  and the most significant fraction bits (widening appends zeros, narrowing
  drops the low bits) — "Propagation of the diagnostic information requires
  information contained in a QNaN to be preserved through arithmetic
  operations and floating-point format conversions" (Vol I-A §6.3.1.5,
  p.82). If the narrowed fraction would be zero (the pattern of an
  infinity), the default QNaN is supplied instead (model pin).
- **Exceptions**: Coprocessor Unusable; Floating Point.
- **Source**: MD00086 Vol II-A Rev 6.06, CVT.S.fmt p.159, CVT.D.fmt p.153.

### c.cond.s / c.cond.d (COP1 compare)

- **Encoding**: `010001 fmt ft fs cc 00 11 cond` — `cc` = bits 10..8,
  bits 7..6 zero, bits 5..4 = `11`, `cond` = bits 3..0 (funct = `0x30 |
  cond`). One constructor per format: `cCondS` / `cCondD`
  `(cond cc fs ft)`, covering all sixteen predicates and all eight
  condition codes.
- **Semantics** (`fpCompare`, `fpCompareInvalid`): let *unordered* = an
  operand is a NaN, *less* = `fs < ft`, *equal* = `fs = ft` (`−0 = +0`).
  `FCC[cc] ← (cond₀ ∧ unordered) ∨ (cond₁ ∧ equal) ∨ (cond₂ ∧ less)`.
  Invalid is raised if an operand is a signaling NaN, or if `cond₃ = 1` and
  the operands are unordered (so also for a quiet NaN). "If the Invalid
  Operation Enable bit is set in the FCSR, no result is written and an
  Invalid Operation exception is taken immediately. Otherwise, the Boolean
  result is written into condition code CC" (C.cond.fmt p.110). `FCSR.Cause`
  is updated as for any arithmetic operation.

  | `cond` | Mnemonics | True when | Invalid on QNaN |
  |---|---|---|---|
  | 0 | `c.f.s` `c.f.d` | never | no |
  | 1 | `c.un.s` `c.un.d` | unordered | no |
  | 2 | `c.eq.s` `c.eq.d` | equal | no |
  | 3 | `c.ueq.s` `c.ueq.d` | unordered or equal | no |
  | 4 | `c.olt.s` `c.olt.d` | less | no |
  | 5 | `c.ult.s` `c.ult.d` | unordered or less | no |
  | 6 | `c.ole.s` `c.ole.d` | less or equal | no |
  | 7 | `c.ule.s` `c.ule.d` | unordered, less or equal | no |
  | 8 | `c.sf.s` `c.sf.d` | never | yes |
  | 9 | `c.ngle.s` `c.ngle.d` | unordered | yes |
  | 10 | `c.seq.s` `c.seq.d` | equal | yes |
  | 11 | `c.ngl.s` `c.ngl.d` | unordered or equal | yes |
  | 12 | `c.lt.s` `c.lt.d` | less | yes |
  | 13 | `c.nge.s` `c.nge.d` | unordered or less | yes |
  | 14 | `c.le.s` `c.le.d` | less or equal | yes |
  | 15 | `c.ngt.s` `c.ngt.d` | unordered, less or equal | yes |

- **Exceptions**: Coprocessor Unusable; Floating Point (enabled V).
- **Source**: MD00086 Vol II-A Rev 6.06, C.cond.fmt p.110-113 (Table 3.1
  p.111, Table 3.2 p.112).

### mov.s / mov.d / movf.s / movt.s / movf.d / movt.d / movn.s / movz.s / movn.d / movz.d (COP1 moves, non-arithmetic)

- **Encoding**: `mov.fmt`: fmt S/D, `ft = 0`, funct `0x06`. `movf.fmt`/
  `movt.fmt` (`MOVCF`): `010001 fmt cc 0 tf fs fd 010001`, `tf` = 0 for
  `movf`, 1 for `movt`. `movz.fmt`/`movn.fmt`: `010001 fmt rt fs fd funct`,
  funct `0x12` (`movz`), `0x13` (`movn`). Constructors `movS` `movD`
  `(fd fs)`; `movfS` `movtS` `movfD` `movtD` `(fd fs cc)`; `movnS` `movzS`
  `movnD` `movzD` `(fd fs rt)`.
- **Semantics**: raw copy of one register (S) or the pair (D) —
  unconditionally (`mov`), if `FCC[cc] = 0` (`movf`) / `= 1` (`movt`), if
  `$rt ≠ 0` (`movn`) / `$rt = 0` (`movz`). Otherwise `fd` keeps its value.
  "The move is non-arithmetic; it causes no IEEE 754 exceptions, and the
  FCSRCause and FCSRFlags fields are not modified" (MOV.fmt p.275, MOVF.fmt
  p.277): NaNs are copied bit for bit.
- **Exceptions**: Coprocessor Unusable.
- **Source**: MD00086 Vol II-A Rev 6.06, MOV.fmt p.275, MOVF.fmt p.277-278,
  MOVT.fmt p.282-283, MOVN.fmt p.280, MOVZ.fmt p.285.

### movf / movt (R, SPECIAL `MOVCI`)

- **Encoding**: `000000 rs cc 0 tf rd 00000 000001`, `tf` = 0 (`movf`) /
  1 (`movt`); bit 17 and bits 10..6 must be zero. Constructors `movf`
  `movt` `(rs cc rd)`.
- **Semantics**: `if FCC[cc] = tf then $rd ← $rs`; otherwise `$rd` is
  unchanged.
- **Exceptions**: Coprocessor Unusable when `Status.CU1 = 0` — these are
  integer moves, but they read the FPU condition codes (Vol III §6.2.22,
  p.100 lists `MOVCI`).
- **Source**: MD00086 Vol II-A Rev 6.06, MOVF p.276, MOVT p.281.

### bc1f / bc1t / bc1fl / bc1tl (COP1 branches)

- **Encoding**: `010001 01000 cc nd tf offset` — `cc` = bits 20..18, `nd`
  = bit 17 (1 = likely), `tf` = bit 16. `bc1f` `nd tf` = `00`, `bc1t` `01`,
  `bc1fl` `10`, `bc1tl` `11`. Constructors `bc1f` `bc1t` `bc1fl` `bc1tl`
  `(cc imm)`.
- **Semantics**: the condition is `FCC[cc] = tf`; the target is `PC_next +
  (sext16(offset) << 2)`. `bc1f`/`bc1t` have an ordinary delay slot,
  exactly like `beq`/`bne` (Global rule 3): the delay-slot instruction
  always executes. `bc1fl`/`bc1tl` are branch-likely: when the branch is
  not taken the delay-slot instruction is nullified ("If the branch is not
  taken, the instruction in the delay slot is not executed", BC1FL p.58) —
  the slot is marked `nullified` and consumed by the next step (see the "Branch likely" section).
  FCSR is not modified.
- **Exceptions/halts**: Coprocessor Unusable. In a delay slot: Reserved
  Instruction (Global rule 3; checked before `CU1`).
- **Source**: MD00086 Vol II-A Rev 6.06, BC1F p.56-57, BC1FL p.58-59,
  BC1T p.60-61, BC1TL p.62-63.

### Not modeled

The L (64-bit fixed point) format — `cvt.l.fmt`, `round.l.fmt`,
`trunc.l.fmt`, `ceil.l.fmt`, `floor.l.fmt`, `cvt.s.l`, `cvt.d.l` — the
unaligned indexed `luxc1`/`suxc1`, and paired-single (`PS`). Their result
"is UNPREDICTABLE if the processor is executing in the FR=0 32-bit FPU
register model" (MD00086 Vol II-A Rev 6.06, CVT.L.fmt p.154; LUXC1 p.234).
These words do not decode: Reserved Instruction with `CU1 = 1`, Coprocessor
Unusable with `CU1 = 0`. The Release 6 FPU instructions (`CMP.cond.fmt`,
`MADDF`, `SEL`, `CLASS`, …) are out of scope.

---

## MIPS32 GPR multiply and variable shifts

This section documents four more real MIPS32 instructions
(`mul`, `sllv`, `srlv`, `srav`) added after the original MARS-grounded set and the "MIPS32 /
MIPS32r2 additions" section above. They were chosen because real-world compilers
(GCC/Clang) essentially never emit this project's existing `mult`+`mflo`
sequence for plain 32-bit multiplication, and the existing `sll`/`srl`/`sra`
only support a *compile-time-constant* shift amount — any C `x << y` / `x >> y`
with a runtime-valued `y` needs `sllv`/`srlv`/`srav` instead. **Grounding
note**: like the "MIPS32 / MIPS32r2 additions" and floating-point sections
above, these four are grounded directly in the **standard MIPS32
architecture** — MD00086 Vol II-A Rev 6.06, MUL p.299, SLLV p.377, SRLV
p.386, SRAV p.384 — not MARS-specific behavior; MARS is this
project's differential-testing oracle, not the spec source.

| Mnemonic | Format | One-line semantics |
|---|---|---|
| `mul` | R (SPECIAL2) | `$rd = ` low 32 bits of `$rs * $rt`, signed; `hi`/`lo` unchanged |
| `sllv` | R | `$rd = $rt << ($rs & 0x1f)` (logical, zero-fill) |
| `srlv` | R | `$rd = $rt >> ($rs & 0x1f)` (logical, zero-fill) |
| `srav` | R | `$rd = $rt >> ($rs & 0x1f)` (arithmetic, sign-fill) |

### mul (R, SPECIAL2)

- **Encoding**: `opcode=011100` (0x1c, SPECIAL2, same opcode as `clo`/`clz`),
  `funct=000010` (0x02). Fields: `011100 sssss ttttt ddddd 00000 000010` →
  `rs=sssss`, `rt=ttttt`, `rd=ddddd` — a plain, undupicated `rs`/`rt`/`rd`
  R-type shape (unlike `clo`/`clz`, there is no rt-duplicates-rd encoding
  quirk here).
- **Semantics**: Multiply Word to GPR. `$rd` = the low 32 bits of the signed
  64-bit product `$rs * $rt` — i.e. exactly the bit pattern the existing
  `mult` instruction would leave in `lo` (two's-complement multiplication's
  low 32 bits are identical whether the operands are read as signed or
  unsigned, so this is also exactly what `multu`+`mflo` would produce).
- **`hi`/`lo` dialect decision**: Real MIPS32 hardware leaves `hi` and `lo`
  **architecturally unpredictable** after `mul` (MD00086 Vol II-A Rev 6.06,
  MUL, p.299: the pseudocode marks them `UNPREDICTABLE`, in contrast to `mult`'s
  well-defined `{hi,lo} = $rs * $rt`). Since this is a *deterministic*
  simulator (`State` has no notion of "unpredictable" register content),
  this project pins the simplest, most defensible choice: **`hi`/`lo` are
  left completely unchanged** by `mul`. This is a deliberate dialect
  decision, not a spec gap — any program relying on `hi`/`lo`'s value after
  `mul` is already relying on undefined real-hardware behavior, so no
  simulator choice here could be "more correct" against the real ISA; this
  one is simply the easiest to state, implement, and test (`$rd`'s own
  write is the only observable effect).
- **Errors/halts**: none; no overflow concept (this is the entire point of
  `mul` over `add`'s trapping behavior — compilers use it precisely because
  32-bit multiplication has no architecturally-defined overflow trap).
- **ISA note**: standard MIPS32 instruction (present since MIPS32 Release 1).
  Real compilers (GCC/Clang `-O0` and above) emit `mul rd, rs, rt` for every
  plain `int * int` 32-bit multiplication; the `mult`/`mflo` pair is
  essentially never generated by a modern compiler for this purpose.

### sllv (R)

- **Encoding**: `opcode=000000` (SPECIAL), `funct=000100` (0x04). Fields:
  `000000 sssss ttttt ddddd 00000 000100` → `rs=sssss` (shift-amount
  register), `rt=ttttt` (value to shift), `rd=ddddd` (destination); the
  5-bit shamt-position field (bits 10-6) is unused/fixed `0` in the encoding
  — unlike `sll`, the shift amount is *not* read from this field.
- **Semantics**: Shift Word Left Logical Variable. `$rd = $rt << ($rs &
  0x1f)` — the shift amount is the **low 5 bits of register `$rs`**, masked
  (not clamped or modulo'd in any other way); e.g. `$rs = 33` (`0b100001`)
  behaves identically to `$rs = 1`, and `$rs = 32` behaves identically to
  `$rs = 0` (a full no-op shift, not an all-zero result — a common
  implementation mistake this spec deliberately avoids testing for). Fill
  is logical (zero-fill from the right), matching `sll`.
- **Errors/halts**: none.
- **ISA note**: standard MIPS32 instruction (MIPS I onward). Emitted by every
  compiler for `x << y` in C whenever `y` is not a compile-time constant
  (MD00086 Vol II-A Rev 6.06, SLLV, p.377).

### srlv (R)

- **Encoding**: `opcode=000000` (SPECIAL), `funct=000110` (0x06). Same field
  layout as `sllv`.
- **Semantics**: Shift Word Right Logical Variable. `$rd = $rt >> ($rs &
  0x1f)`, logical (zero-fill from the left), matching `srl`. Same low-5-bit
  masking behavior as `sllv`.
- **Errors/halts**: none.
- **ISA note**: standard MIPS32 instruction. Emitted for `(unsigned)x >> y`
  in C with a non-constant `y`.

### srav (R)

- **Encoding**: `opcode=000000` (SPECIAL), `funct=000111` (0x07). Same field
  layout as `sllv`/`srlv`.
- **Semantics**: Shift Word Right Arithmetic Variable. `$rd = $rt >> ($rs &
  0x1f)`, arithmetic (sign-extending fill from the left, replicating bit 31
  of `$rt`), matching `sra`. Same low-5-bit masking behavior as `sllv`.
- **Errors/halts**: none.
- **ISA note**: standard MIPS32 instruction. Emitted for `(signed)x >> y` in
  C with a non-constant `y`.

### Citation

MD00086 Vol II-A Rev 6.06: MUL p.299 (SPECIAL2, funct `0x02`; "HI and LO
are UNPREDICTABLE after the operation"), SLLV p.377, SRLV p.386, SRAV p.384
(SPECIAL, funct `0x04`/`0x06`/`0x07`; shift amount `GPR[rs]4..0`).

## Atomic synchronization (`ll`/`sc`)

This section documents the real MIPS32 load-linked/store-
conditional pair (`ll`/`sc`), the standard MIPS mechanism for lock-free
algorithms, spinlocks, and mutexes. **Grounding note**: like the
Coprocessor 0 and floating-point additions above, this section is grounded
directly in the **real MIPS32 architecture** — MD00086 Vol II-A Rev 6.06,
LL p.223-224 and SC p.347-350 — not against MARS, which is only this
project's differential-testing oracle.

### The `LLbit` model

Two state fields: `State.llBit` (the link bit) and `State.llAddr` (the
effective address of the most recent `ll`, meaningful while `llBit` is
set). `ll` sets `llBit` and records `llAddr`. `llBit` is cleared by:

- **`sc`**, success or failure — **a pin.** A second `sc` without a new
  `ll` therefore fails; the manual makes that case not predictable
  ("Execution of SC must have been preceded by execution of an LL
  instruction", else "the result of the SC is not predictable", MD00086
  Vol II-A Rev 6.06, SC, p.348).
- **Every exception entry** ("Exceptions between the LL and SC cause SC to
  fail", SC, p.350) — including the Address Error of a misaligned store.
- **`eret`** ("An ERET instruction is executed" is one of the events after
  which "the SC fails", SC, p.347).
- **Any store that completes** — `sb`, `sh`, `sw`, `swl`, `swr`, `swc1`,
  `sdc1`, `swxc1`, `sdxc1`, to any address. **This is a pinned choice, not
  an architectural mandate.** SC, p.347: a same-processor store to the LL
  block makes the SC fail "if Config5LLB=1; else whether such a store
  causes the SC to fail is not predictable"; a same-processor load "will
  not cause the SC to fail (if Config5LLB=1; else such a load may cause the
  SC to fail)". (`Config5.LLB` is a Release 5 feature, absent from the
  Release 2 profile.) Failing after a store is one legal outcome (the
  conservative one); letting `sc` succeed after an intervening load or
  `pref` — which the model does — is equally legal.

**Address match.** "an SC must always compare its address against that of
the LL. An SC will fail if the aligned address of the SC does not match
that of the preceding LL" (SC, p.347). The model implements this: `sc`
succeeds only if `llBit` is set **and** its effective address equals
`llAddr` in bits 31..2 (the aligned word; bits 1..0 are ignored).

The remaining architectural clearing events (a coherent store by another
processor, cache effects) have no counterpart in a single-processor model,
and `sc` never fails spuriously.

### ll (I)
- **Encoding**: `opcode=110000` (0x30), `base rt offset`, as `lw`.
  Constructor `ll (rs rt imm)`.
- **Semantics**: `addr = $base + sext16(offset)`; `$rt = MEM32[addr]`
  (big-endian, identical to `lw`); `llBit := true`; `llAddr := addr`.
- **Errors/halts**: `addr mod 4 ≠ 0` → Address Error (AdEL, `BadVAddr =
  addr`); nothing else changes except what exception entry does (which
  clears `llBit`).
- **Lean**: `ll_spec_raw`.
- **Source**: MD00086 Vol II-A Rev 6.06, LL, p.223-224.

### sc (I)
- **Encoding**: `opcode=111000` (0x38), `base rt offset`, as `sw`.
  Constructor `sc (rs rt imm)`.
- **Semantics**: `addr = $base + sext16(offset)`. The alignment check is
  unconditional (as for `sw`), whatever `llBit` holds. Then:
  1. If `llBit` is set **and** `llAddr[31..2] = addr[31..2]`: `MEM32[addr] = $rt` (the
     value of `$rt` before this instruction), then `$rt := 1`.
  2. Otherwise: no store; `$rt := 0`.
  3. Either way `llBit := false`.
- **Errors/halts**: `addr mod 4 ≠ 0` → Address Error (AdES, `BadVAddr =
  addr`), regardless of `llBit`; memory and `$rt` are unchanged.
- **Lean**: `sc_spec_raw`.
- **Source**: MD00086 Vol II-A Rev 6.06, SC, p.347-350.

### Encoding summary

| Mnemonic | Format | One-line semantics |
|---|---|---|
| `ll $rt, offset($rs)` | I, opcode 0x30 | `$rt = MEM32[$rs + offset]`; `llBit := true`; `llAddr := $rs + offset` |
| `sc $rt, offset($rs)` | I, opcode 0x38 | if `llBit` and `llAddr[31..2] = ($rs + offset)[31..2]`: `MEM32[$rs + offset] = $rt`, `$rt := 1`; else `$rt := 0`; either way `llBit := false` |

### Citation

MD00086 Vol II-A Rev 6.06: LL p.223-224 (opcode `0x30`), SC p.347-350
(opcode `0x38`).

## Integer multiply-accumulate and HI/LO register moves

This section documents the real MIPS32 integer multiply-
accumulate family (`madd`, `maddu`, `msub`, `msubu`) and the write-direction
HI/LO register moves (`mthi`, `mtlo` — the counterparts to the existing
`mfhi`/`mflo`). `madd`/`maddu`/
`msub`/`msubu` are the core loop instruction in DSP filters, vector
dot-products, and numerical libraries, and `mthi`/`mtlo` are mandatory for OS
context switching and setjmp/longjmp to save/restore the `hi`/`lo` registers
(this project already modeled the read direction, `mfhi`/`mflo`, but not the
write direction). **Grounding note**: like the other sections added after the original set,
all six are grounded directly in the **standard MIPS32 architecture** —
MD00086 Vol II-A Rev 6.06, MADD p.255, MADDU p.261, MSUB p.286, MSUBU
p.289, MTHI p.297, MTLO p.298 — not MARS-specific behavior; MARS is this
project's differential-testing oracle, not the spec source.

| Mnemonic | Format | One-line semantics |
|---|---|---|
| `madd $rs, $rt` | R (SPECIAL2) | `{hi,lo} += $rs * $rt`, signed 64-bit |
| `maddu $rs, $rt` | R (SPECIAL2) | `{hi,lo} += $rs * $rt`, unsigned 64-bit |
| `msub $rs, $rt` | R (SPECIAL2) | `{hi,lo} -= $rs * $rt`, signed 64-bit |
| `msubu $rs, $rt` | R (SPECIAL2) | `{hi,lo} -= $rs * $rt`, unsigned 64-bit |
| `mthi $rs` | R (SPECIAL) | `hi = $rs` |
| `mtlo $rs` | R (SPECIAL) | `lo = $rs` |

### madd (R, SPECIAL2)

- **Encoding**: `opcode=011100` (0x1c, SPECIAL2, same opcode as `clo`/`clz`/
  `mul`), `funct=000000` (0x00). Fields: `011100 sssss ttttt 00000 00000
  000000` → `rs=sssss`, `rt=ttttt`; `rd`/`shamt` unused (always 0) — the
  same `rs, rt`-only shape as the existing `mult`/`div` (no `rd` field is
  written directly).
- **Semantics**: Multiply and Add Word to HI/LO. Forms the signed 64-bit
  product `$rs * $rt` exactly like `mult` does (both operands sign-extended
  to 64 bits before multiplying), then **adds** that product to the
  *existing* `{hi,lo}` 64-bit pair, rather than overwriting it the way
  `mult` does: `{hi,lo} := {hi,lo} + ($rs * $rt)` as a 64-bit addition,
  with `hi` the high 32 bits and `lo` the low 32 bits of the result.
- **Errors/halts**: none; no overflow trap. Matching `mult`'s existing
  non-trapping precedent (see `mult` entry above), the 64-bit accumulator
  wraps on overflow like any other fixed-width arithmetic in this model —
  real MIPS32 hardware has no overflow-trap concept for this instruction
  either.
- **ISA note**: standard MIPS32 instruction (present since MIPS32 Release 1).
  The canonical use is a DSP-style multiply-accumulate loop (`for` loop
  computing a dot product or FIR filter tap), where each iteration's
  `madd $a, $b` adds one more product into a running 64-bit sum without an
  intervening `mflo`/`add`/`mthi` round trip through a GPR.

### maddu (R, SPECIAL2)

- **Encoding**: `opcode=011100` (0x1c), `funct=000001` (0x01). Same field
  layout as `madd`.
- **Semantics**: Multiply and Add Unsigned Word to HI/LO. Same as `madd`,
  but the product is formed from the **unsigned** 64-bit zero-extension of
  `$rs`/`$rt` (mirroring `multu`): `{hi,lo} := {hi,lo} + (unsigned($rs) *
  unsigned($rt))`. The addition itself is plain 64-bit wraparound arithmetic
  either way — only the product's formation differs between the signed and
  unsigned variants.
- **Errors/halts**: none; same non-trapping precedent as `madd`/`multu`.
- **ISA note**: standard MIPS32 instruction. Used for unsigned dot-products
  and big-integer multiply-accumulate routines.

### msub (R, SPECIAL2)

- **Encoding**: `opcode=011100` (0x1c), `funct=000100` (0x04). Same field
  layout as `madd`.
- **Semantics**: Multiply and Subtract Word to HI/LO. Forms the signed
  64-bit product `$rs * $rt` exactly like `madd`, but **subtracts** it from
  the existing `{hi,lo}` pair instead of adding: `{hi,lo} := {hi,lo} -
  ($rs * $rt)`, a 64-bit subtraction with the same wraparound-on-underflow
  behavior as `madd`'s wraparound-on-overflow.
- **Errors/halts**: none; same non-trapping precedent as `madd`.
- **ISA note**: standard MIPS32 instruction. Used in DSP filter routines
  that need to subtract a tap's contribution from a running accumulator.

### msubu (R, SPECIAL2)

- **Encoding**: `opcode=011100` (0x1c), `funct=000101` (0x05). Same field
  layout as `madd`.
- **Semantics**: Multiply and Subtract Unsigned Word to HI/LO. Same as
  `msub`, but the product is formed unsigned, mirroring `maddu`/`multu`:
  `{hi,lo} := {hi,lo} - (unsigned($rs) * unsigned($rt))`.
- **Errors/halts**: none; same non-trapping precedent as `msub`.
- **ISA note**: standard MIPS32 instruction. Unsigned counterpart to `msub`.

### mthi (R)

- **Encoding**: `opcode=000000` (SPECIAL), `funct=010001` (0x11 — the next
  funct value immediately after `mfhi`'s 0x10, the same kind of adjacency
  as `syscall`'s 0x0c/`break`'s 0x0d). Fields: `000000 sssss 00000 00000
  00000 010001` → `rs=sssss`(source register); `rt`/`rd`/`shamt` unused
  (always 0) — the same one-operand `rs`-only shape as `jr`.
- **Semantics**: Move to HI Register. `hi := $rs`. No GPR is written; `lo`
  is left unchanged.
- **Errors/halts**: none.
- **ISA note**: standard MIPS32 instruction (present since MIPS I). The
  write-direction counterpart to the already-implemented `mfhi`. Mandatory
  for OS context-switch code and `setjmp`/`longjmp` implementations that
  must save and later restore the `hi`/`lo` registers around arbitrary
  multiply/divide usage elsewhere in a program (MD00086 Vol II-A Rev 6.06,
  MTHI, p.297).

### mtlo (R)

- **Encoding**: `opcode=000000` (SPECIAL), `funct=010011` (0x13 — the next
  funct value immediately after `mflo`'s 0x12). Same field layout as
  `mthi`.
- **Semantics**: Move to LO Register. `lo := $rs`. No GPR is written; `hi`
  is left unchanged.
- **Errors/halts**: none.
- **ISA note**: standard MIPS32 instruction. The write-direction counterpart
  to `mflo`, same context-switch/`setjmp`/`longjmp` rationale as `mthi`.
## MIPS32r2 rotate and bitfield extract/insert

This section documents five real MIPS32r2 instructions
(`rotr`, `rotrv`, `ext`, `ins`, `wsbh`) added after the original MARS-grounded set.
`ext`/`ins` are ubiquitous in MIPS32r2-compiled C for struct bitfields
and protocol decoding, `rotr`/`rotrv` are common in cryptographic hash
implementations, and `wsbh` is common in endianness-conversion pipelines.
**Grounding note**: like the other later sections, this is grounded
directly in the **real MIPS32r2 architecture** — MD00086 Vol II-A Rev 6.06,
ROTR p.339, ROTRV p.340, EXT p.183-184, INS p.192-193, WSBH p.445 — not
MARS-specific behavior.

| Mnemonic | Format | One-line semantics |
|---|---|---|
| `rotr $rd, $rt, sa` | R (overloaded `srl`) | `$rd = $rt` rotated right by constant `sa` |
| `rotrv $rd, $rt, $rs` | R (overloaded `srlv`) | `$rd = $rt` rotated right by `$rs & 0x1f` |
| `ext $rt, $rs, pos, size` | R (SPECIAL3) | `$rt = zext($rs[pos+size-1 .. pos])` |
| `ins $rt, $rs, pos, size` | R (SPECIAL3) | `$rt[pos+size-1 .. pos] = $rs[size-1 .. 0]`, rest of `$rt` unchanged |
| `wsbh $rd, $rt` | R (SPECIAL3/BSHFL) | swap bytes within each halfword of `$rt` independently |

### rotr (R) / rotrv (R)

- **Encoding**: `rotr` shares `srl`'s opcode (`000000`, SPECIAL) and funct
  (`000010`, 0x02); `rotrv` shares `srlv`'s opcode (SPECIAL) and funct
  (`000110`, 0x06). Real MIPS32r2 distinguishes rotate from shift by
  overloading a field that is otherwise unused/fixed-zero in the plain-shift
  encodings: for `rotr` (shift-by-constant format), the normally-`00000`
  `rs` field (bits 25-21) is set to `00001`; for `rotrv` (shift-by-register
  format), the normally-`00000` `shamt` field (bits 10-6) is set to `00001`.
  Everything else matches `srl`/`srlv`'s field layout exactly (`rotr`:
  `rd rt sa`; `rotrv`: `rd rt rs`). This is a **new decode/encode branch
  added alongside** the existing `srl`/`srlv` handling, not a replacement —
  a word with `rs=0`/`shamt=0` still decodes to plain `srl`/`srlv`.
- **Semantics**: Rotate Word Right (`rotr`) / Rotate Word Right Variable
  (`rotrv`). Bits shifted off the bottom wrap around to fill the top — this
  is the one bit that distinguishes rotate from `srl`/`srlv`'s **zero-fill**
  on the exact same input. Worked example: `rotr $t0, $t1, 4` with
  `$t1 = 0x12345678` gives `$t0 = 0x81234567` (the low nibble `0x8` wraps
  around to the top byte), whereas `srl $t0, $t1, 4` on the same input gives
  `$t0 = 0x01234567` (zero-fill instead). `rotrv`'s rotate amount is `$rs`'s
  low 5 bits, masked exactly like `sllv`/`srlv`/`srav`'s shift amount (e.g.
  `$rs = 36` behaves identically to `$rs = 4`).
- **Errors/halts**: none.
- **Source**: MD00086 Vol II-A Rev 6.06, ROTR p.339, ROTRV p.340 (MIPS32
  Release 2).

### ext (R, SPECIAL3)

- **Encoding**: `opcode=011111` (0x1f, SPECIAL3), `funct=000000` (0x00).
  Fields: `011111 sssss ttttt mmmmm lllll 000000` → `rs=sssss` (source),
  `rt=ttttt` (destination), and two compile-time constants packed into the
  remaining fields: `lsb` (bits 10-6, this project's `shamt`-position field)
  is `pos` directly; `msbd` (bits 15-11, this project's `rd`-position field)
  is `size - 1` — **not** `size` itself (the real MIPS32 ISA pseudocode
  computes `size = msbd + 1`, so `Instruction.decode`/`encode` do this `±1`
  arithmetic so that `Step.lean` only ever sees the semantic `pos`/`size`
  pair directly, the same way this codebase already hides `clo`/`clz`'s
  duplicated-rt-field quirk).
- **Semantics**: Extract Bit Field. `$rt = zero-extend($rs[pos+size-1 ..
  pos])` — a `size`-bit field starting at bit `pos` of `$rs`, zero-extended
  into `$rt`. Worked example: `ext $t0, $t1, 6, 10` with
  `$t1 = 0x12345678` extracts the 10-bit field at bits [15:6]
  (`(0x12345678 >> 6) & 0x3ff`), giving `$t0 = 0x159`.
- **UNPREDICTABLE encodings do not decode**: "The operation is
  UNPREDICTABLE if lsb+msbd > 31" (i.e. `pos + size > 32`; MD00086 Vol II
  Rev 2.50, EXT, p.131). `decode` rejects such a word (→ Reserved
  Instruction, a pin among the legal outcomes). For constructor values not
  produced by `decode`, `step` reads the diagram's 5-bit fields as `encode`
  writes them (`lsb = pos mod 32`, `msbd = (size − 1) mod 32`) and raises
  Reserved Instruction when `lsb + msbd > 31` (7R; `ext_spec_fields`).
- **Errors/halts**: none at execution time.
- **Source**: MD00086 Vol II Rev 2.50, EXT, p.131 (`msbd ← size-1`,
  `lsb ← pos`); the corresponding page of MD00086 Vol II-A Rev 6.06 (EXT,
  p.183) has no extracted text in the local manual text (image-only page).

### ins (R, SPECIAL3)

- **Encoding**: `opcode=011111` (0x1f, SPECIAL3), `funct=000100` (0x04).
  Same `rs`/`rt`/`lsb` field roles as `ext` (`lsb` = `pos`), but the
  `rd`-position field (bits 15-11, called `msb` for this instruction) holds
  a **different** quantity than `ext`'s `msbd`: `msb = pos + size - 1` (the
  real MIPS32 ISA pseudocode sets `lsb = pos; msb = pos + size - 1`). This
  is a genuinely different field computation from `ext`'s `size - 1`, not a
  typo — `Instruction.decode`/`encode` do the matching `±1` arithmetic for
  each instruction separately.
- **Semantics**: Insert Bit Field. Inserts the low `size` bits of `$rs` into
  `$rt` starting at bit `pos`; bits of `$rt` **outside** `[pos+size-1 ..
  pos]` are left completely unchanged (the same "partially update a
  register" shape as `movn`/`movz`, though the bit-level masking here is
  new). Worked example: `ins $t0, $t1, 6, 10` with `$t1 = 0x159` and
  `$t0 = 0x12345678` beforehand re-inserts exactly the field `ext` extracted
  above, reproducing `$t0 = 0x12345678` unchanged — `ext`/`ins` round-trip
  by construction. A second example starting from `$t0 = 0`: with
  `$t1 = 0xfffffc01` (`size = 10`, so only the low 10 bits `0x001` are
  used, the rest of `$t1` is ignored), `ins $t0, $t1, 6, 10` gives
  `$t0 = 0x00000040` (`0x001 << 6`) — the bits of `$t0` outside `[15:6]`
  stay `0`, demonstrating the "unchanged outside the field" guarantee.
- **UNPREDICTABLE encodings do not decode**: "The operation is
  UNPREDICTABLE if lsb > msb" (MD00086 Vol II-A Rev 6.06, INS, p.193);
  `decode` rejects a word with `msb < lsb`. For constructor values not
  produced by `decode`, `step` reads `lsb = pos mod 32`,
  `msb = (pos + size − 1) mod 32` and raises Reserved Instruction when
  `lsb > msb` (7R; `ins_spec_fields`).
- **Errors/halts**: none.
- **Source**: MD00086 Vol II-A Rev 6.06, INS, p.192-193.

### wsbh (R, SPECIAL3/BSHFL)

- **Encoding**: `opcode=011111` (0x1f, SPECIAL3), `funct=100000` (0x20) —
  the same BSHFL funct family as the already-implemented `seb`/`seh`,
  distinguished by the shamt-position sub-field: `seb` is `0x10`, `seh` is
  `0x18`, `wsbh` is `0x02` (`rs` unused/fixed 0, same as `seb`/`seh`). This
  is a **new case added alongside** the existing `seb`/`seh` dispatch on
  that sub-field, not a replacement.
- **Semantics**: Word Swap Bytes Within Halfwords. Swaps the byte order
  **within** each 16-bit half of `$rt` independently (byte 0 ↔ byte 1,
  byte 2 ↔ byte 3) — the two halfwords themselves stay in their original
  word positions. This is **not** a full 32-bit byte-reverse; that needs
  `wsbh` followed by `rotr $rd, $rd, 16` (swap bytes within each halfword,
  then swap the halfwords themselves), the standard MIPS32r2
  endianness-conversion idiom — `wsbh` alone does not do this. Worked
  example: `wsbh $t0, $t1` with `$t1 = 0x12345678` gives `$t0 =
  0x34127856` (halfword `0x5678` → `0x7856`; halfword `0x1234` → `0x3412`;
  halfword *positions* unchanged).
- **Errors/halts**: none.
- **Source**: MD00086 Vol II-A Rev 6.06, WSBH, p.445 (MIPS32 Release 2).

## Unaligned memory access (`lwl`/`lwr`/`swl`/`swr`)

This section documents the real MIPS32 classic (MIPS I
through MIPS32 Release 2) unaligned load/store pair `lwl`/`lwr` (Load/Store
Word Left) and `swl`/`swr` (Store Word Left/Right) (common in classic MIPS:
emitted by standard-library `memcpy`/`strcpy` and by unaligned-struct-field
access in compiled C). **Grounding note**: like the Coprocessor 0,
floating-point, GPR-multiply/variable-shift, and `ll`/`sc` additions above,
this section is grounded directly in the **real MIPS32 architecture** —
MD00086 Vol II-A Rev 6.06, LWL p.240-242, LWR p.247-251, SWL p.397-398,
SWR p.401-403 — not against MARS (which is this project's
differential-testing oracle, not the spec source). **Scope note**:
"Release 6 removes the load/store-left/right family of instructions" (LWL
p.241); this project targets MIPS32 Release 2 (per the project
target profile in CLAUDE.md and the README), so
these four classic instructions are in scope.

### Why this family exists

`lw`/`sw` require a word-aligned address (Global rule 5) and raise Address
Error otherwise. `lwl`/`lwr`/`swl`/`swr` are classic MIPS's
alignment-free alternative: **neither ever halts on a misaligned address —
that is their entire purpose.** Software loads/stores an arbitrary unaligned
32-bit word by issuing one `lwl` (or `swl`) and one `lwr` (or `swr`) to two
different offsets of the *same* base register; between the two instructions,
every byte of the 4-byte unaligned word is touched exactly once, so the pair
is equivalent to a hypothetical "unaligned `lw`/`sw`".

### Shared addressing and the byte-position convention

All four compute the same way: `addr = $rs + sext16(offset)`, exactly like
`lw`/`sw` (**no alignment check** — this is the one addressing-mode
difference from `lw`/`sw`). Let `off = addr mod 4` (i.e. how far `addr` is
past the start of the word that contains it) and let `wordBase = addr - off`
(the address of that word's first/most-significant byte). Per Global rule 4,
this project's memory is big-endian: for any word-aligned address `W`, byte
`W` holds bits `[31:24]` of the conceptual word at `W` ("slot 0"), `W+1`
holds bits `[23:16]` ("slot 1"), `W+2` holds `[15:8]` ("slot 2"), and `W+3`
holds `[7:0]` ("slot 3"). `lwl`/`swl` work from `addr` *up to* the next word
boundary (i.e. slots `off..3`); `lwr`/`swr` work from the word boundary *up
to and including* `addr` (i.e. slots `0..off`, except indexed from the
*other* end — see each entry below for the exact slot arithmetic).

### lwl (I)

- **Encoding**: `opcode=100010` (0x22). Same field layout as `lw`:
  `base=rs`, `rt` (destination — and also *read*, since the bytes `lwl`
  doesn't touch are preserved from `rt`'s prior value), `offset` (sign-
  extended exactly like `lw`'s offset).
- **Semantics**: `addr = $base + sext16(offset)` (no alignment check). Let
  `off = addr mod 4`. Reads the `4 - off` bytes starting at `addr` up to and
  including `wordBase + 3` (the next word boundary) and places them into the
  **most-significant** `4 - off` byte-slots of `$rt` (slots `0 .. 3-off`, in
  address order — the byte at `addr` is the most significant of the ones
  read); `$rt`'s remaining `off` least-significant byte-slots are left
  **unchanged**. When `off = 0`, this reads all 4 bytes and behaves exactly
  like `lw`.
- **Errors/halts**: no misalignment error — `readMemByte` (the per-byte primitive this
  is built from) has no alignment requirement, unlike `readMemWord`. A kernel address from User
  Mode raises Address Error (AdEL, `BadVAddr = addr`; Global rule 5a): every byte touched lies in
  the aligned word containing `addr`, so the access at `addr` decides (MD00086 Vol II-A Rev 6.06,
  LWL p.240-242: Exceptions include Address Error).
- **ISA note**: standard classic-MIPS instruction (MIPS I onward; removed in
  MIPS32r6). Always paired with `lwr` to load an arbitrary unaligned word;
  see the worked example below.

### lwr (I)

- **Encoding**: `opcode=100110` (0x26). Same field layout as `lwl`.
- **Semantics**: Same `addr`/`off` as `lwl`. Reads the `off + 1` bytes from
  `wordBase` up to and including `addr` and places them into the
  **least-significant** `off + 1` byte-slots of `$rt` (slots `3-off .. 3`,
  in address order); `$rt`'s remaining `3 - off` most-significant byte-slots
  are left **unchanged**. When `off = 3`, this reads all 4 bytes (`wordBase`
  through `wordBase + 3 = addr`) and behaves exactly like `lw`.
- **Errors/halts**: as `lwl`: no misalignment error; AdEL for a kernel address from User Mode.
- **ISA note**: standard classic-MIPS instruction (MIPS I onward; removed in
  MIPS32r6). Complementary to `lwl` — see the worked example below.

### swl (I)

- **Encoding**: `opcode=101010` (0x2a). Same field layout as `sw`:
  `base=rs`, `rt` (source register, read-only — unlike `lwl`, `swl` does not
  write `$rt`), `offset` (sign-extended exactly like `sw`'s offset).
- **Semantics**: Same `addr`/`off` as `lwl`. Stores `$rt`'s **most-
  significant** `4 - off` byte-slots (slots `0 .. 3-off`) into memory at
  `addr` through `wordBase + 3` (the next word boundary), in address order.
  When `off = 0`, this stores all 4 bytes and behaves exactly like `sw`.
  Like `sw`, clears `State.llBit` (see the "`LLbit` single-hart
  simplification" note above — `swl`/`swr` are store-class instructions for
  that purpose too).
- **Errors/halts**: no misalignment error (`writeMemByte`, the per-byte primitive this
  is built from, has no alignment requirement, unlike `writeMemWord`); a kernel address from User
  Mode raises Address Error (AdES, nothing stored; Global rule 5a).
- **ISA note**: standard classic-MIPS instruction (MIPS I onward; removed in
  MIPS32r6). Always paired with `swr`; see the worked example below.

### swr (I)

- **Encoding**: `opcode=101110` (0x2e). Same field layout as `swl`.
- **Semantics**: Same `addr`/`off` as `lwl`. Stores `$rt`'s **least-
  significant** `off + 1` byte-slots (slots `3-off .. 3`) into memory from
  `wordBase` through `addr`, in address order. When `off = 3`, this stores
  all 4 bytes and behaves exactly like `sw`. Clears `State.llBit`, same as
  `swl`.
- **Errors/halts**: as `swl`: no misalignment error; AdES for a kernel address from User Mode.
- **ISA note**: standard classic-MIPS instruction (MIPS I onward; removed in
  MIPS32r6). Complementary to `swl` — see the worked example below.

### Worked example: loading/storing an unaligned word with the complementary pair

Let `$s0 = A` where `A mod 4 = 0` (word-aligned), and suppose memory holds
the big-endian bytes `A:0x11, A+1:0x22, A+2:0x33, A+3:0x44, A+4:0x55,
A+5:0x66, A+6:0x77, A+7:0x88`. The *unaligned* word spanning `A+1 .. A+4` is
conceptually `0x22334455` (byte `A+1` most significant, `A+4` least
significant) — but no single `lw` can read it, since neither `A+1` nor any
address in that range is word-aligned.

```
lwl $t0, 1($s0)    # addr = A+1, off = 1
lwr $t0, 4($s0)    # addr = A+4, off = 0
```

- `lwl $t0, 1($s0)`: `addr = A+1`, `off = 1`, so it reads the `4-1=3` bytes
  `A+1=0x22, A+2=0x33, A+3=0x44` into `$t0`'s top 3 byte-slots (slots 0,1,2);
  slot 3 (the low byte) is left unchanged (whatever `$t0` held before). After
  this instruction, `$t0 = 0x2233_44??` (`??` = `$t0`'s prior low byte).
- `lwr $t0, 4($s0)`: `addr = A+4`, `off = (A+4) mod 4 = 0`, so it reads the
  `0+1=1` byte `A+4=0x55` into `$t0`'s bottom byte-slot (slot 3) only; slots
  0–2 are left unchanged (`lwr` never touches them). After this instruction,
  `$t0 = 0x22334455` — exactly the unaligned word, with each of the 4 bytes
  `A+1..A+4` supplied by exactly one of the two instructions (`lwl` supplied
  `A+1,A+2,A+3`; `lwr` supplied `A+4`; no byte is supplied twice or missed).

The store direction is the exact mirror image: to write `$t0 = 0x22334455`
back to the same unaligned range,

```
swl $t0, 1($s0)    # addr = A+1, off = 1: stores $t0's top 3 bytes (0x22,0x33,0x44) to A+1,A+2,A+3
swr $t0, 4($s0)    # addr = A+4, off = 0: stores $t0's bottom byte (0x55) to A+4
```

writes `A+1:0x22, A+2:0x33, A+3:0x44, A+4:0x55` — again, every byte in the
range touched exactly once between the two instructions.

### Encoding summary

| Mnemonic | Format | One-line semantics |
|---|---|---|
| `lwl $rt, offset($rs)` | I, opcode 0x22 | loads bytes `addr..wordBase+3` into `$rt`'s high byte-slots; low slots unchanged |
| `lwr $rt, offset($rs)` | I, opcode 0x26 | loads bytes `wordBase..addr` into `$rt`'s low byte-slots; high slots unchanged |
| `swl $rt, offset($rs)` | I, opcode 0x2a | stores `$rt`'s high byte-slots to memory `addr..wordBase+3` |
| `swr $rt, offset($rs)` | I, opcode 0x2e | stores `$rt`'s low byte-slots to memory `wordBase..addr` |

(`addr = $rs + sext16(offset)`, no alignment check; `wordBase = addr - (addr
mod 4)`.)

### Citation

Printed pages of MD00086 Vol II-A Rev 6.06 for the three sections above:

- Integer multiply-accumulate and HI/LO moves: MADD p.255, MADDU p.261,
  MSUB p.286, MSUBU p.289 (SPECIAL2, funct `0x00`/`0x01`/`0x04`/`0x05`);
  MTHI p.297, MTLO p.298 (SPECIAL, funct `0x11`/`0x13`).
- Rotate and bitfield: ROTR p.339, ROTRV p.340, EXT p.183-184 (text: Rev
  2.50 p.131), INS p.192-193, WSBH p.445.
- Unaligned access: LWL p.240-242 (opcode `0x22`), LWR p.247-251 (`0x26`),
  SWL p.397-398 (`0x2a`), SWR p.401-403 (`0x2e`).

## Memory-ordering / cache-hint instructions (`sync`/`synci`)

This section documents the real MIPS32 memory-ordering
barrier (`sync`) and instruction-cache-flush hint (`synci`), which complete the atomics story alongside `ll`/`sc` above.
**Grounding note**: like every other section added after the original set, this
section is grounded directly in the **real MIPS32 architecture** —
MD00086 Vol II-A Rev 6.06, SYNC p.407-411 and SYNCI p.412-414 (MIPS32
Release 2) — not against MARS, which implements neither instruction.

### Why both are no-ops in this model

Real MIPS32 hardware uses `sync` to order a core's own loads/stores against
what other cores/coherent I/O devices observe, and `synci` to flush a stale
instruction-cache line after self-modifying code or a JIT compiler writes
new instruction bytes. Both instructions exist to manage hazards that only
arise from things this simulator does not model at all: **`sync`** orders
against other cores and out-of-order/speculative execution, and this is a
single-hart simulator with no multiprocessor state and no instruction
reordering of any kind (every instruction's effect is fully committed,
in program order, before the next one is fetched — see `Step.lean`'s
`execInstr`/`mkNext`); **`synci`** orders against a hardware instruction
cache that might otherwise serve stale fetched bytes, and this simulator
has no instruction cache (or any cache) at all — fetch (`readMemWord s s.pc`)
always reads the current contents of `State.physMem`, so a store is visible to
the next fetch (`sw_next_instruction_is_fetched`). SYNCI's Operation is
`SynchronizeCacheLines(vaddr)` (MD00086 Vol II-A Rev 6.06, SYNCI, p.413);
with no cache line to synchronize this has no architectural effect, which is
correct for a cacheless implementation; the optional AdEL for kernel
addresses is "implementation dependent" (p.412) and not raised. With neither
hazard able to exist in this model, both instructions are **documented no-ops**: each
falls through to `PC_next` exactly like any other non-control-flow
instruction, via the same `mkNext` path every arithmetic/logic instruction
uses, touching no other part of `State` at all. This is the same
simplification rationale already used for `wait` above (real hardware
behavior this simulator has no state to usefully model), not a silent
pretense that ordering or cache-coherence is implemented.

### sync (R, SPECIAL)

- **Encoding**: `000000 00000 00000 00000 stype 001111` — SPECIAL, funct
  `0x0f`; bits 25..11 must be zero; **`stype` = bits 10..6** selects the
  kind of barrier. Constructor `sync (stype)`: the field is carried, so
  every `stype` decodes and round-trips; all of them execute identically.
- **Semantics**: a complete no-op — see "Why both are no-ops in this
  model" above. Falls through to `PC_next`; no register, memory, `hi`/`lo`,
  FPU, or CP0 state is touched.
- **Errors/halts**: none.
- **Source**: MD00086 Vol II-A Rev 6.06, SYNC, p.407-411.

### synci (I, REGIMM)

- **Encoding**: `opcode=000001` (0x01, REGIMM — the same major opcode as
  `bltz`/`bgez`/the trap-immediate family above), `rt`-field = `11111`
  (0x1f), selecting `synci` the same way `rt` multiplexes every other
  REGIMM sub-instruction in this reference. `rs` (base register) and the
  16-bit `offset` fields are laid out identically to `lw`/`sw`/`blez`.
- **Semantics**: `addr = $rs + sext16(offset)` — the exact same effective-
  address computation `lw`/`sw` perform, included for architectural
  fidelity (a real implementation would use `addr` to identify which
  cache line to flush) — but since this simulator has no instruction-cache
  model, `addr` is computed and then **used for nothing**: no memory read,
  no memory write, no state of any kind is touched. Falls through to
  `PC_next`, same as `sync` above.
- **Errors/halts**: none in the model — `addr` is never dereferenced, so
  no alignment or address check is made.
- **Source**: MD00086 Vol II-A Rev 6.06, SYNCI, p.412-414.

## "Branch likely" family (real MIPS32; deprecated in MIPS32, removed in Release 6)

This section documents the eight real MIPS32 "branch
likely" instructions `beql`, `bnel`, `blezl`, `bgtzl`, `bltzl`, `bgezl`,
`bltzall`, `bgezall`. **Grounding note**:
like the Coprocessor 0, floating-point, GPR-multiply/variable-shift,
`ll`/`sc`, and unaligned-memory-access additions above, this section is
grounded directly in the **real MIPS32 architecture** — MD00086 Vol II-A
Rev 6.06, pages listed under "Citation" below — not against MARS (which is
this project's differential-testing oracle, not the spec source). **Scope
note**: every page of this family is marked "removed in Release 6"; this
project targets MIPS32
Release 2, where the family is still architecturally present, and it does
still appear in real historical/legacy binaries and in code generated by
older toolchains with `-mbranch-likely` — hence "real historical/
compatibility part of the language" rather than purely academic. **All
eight are implemented** (no subset was cut): the four `beq`/`bne`/`blez`/
`bgtz`-shaped instructions (`beql`, `bnel`, `blezl`, `bgtzl`) and the four
REGIMM zero-comparison-shaped instructions (`bltzl`, `bgezl`, `bltzall`,
`bgezall`).

### This is a real architectural difference, not a simplification

**Every other branch/jump documented in this file always executes its
delay-slot instruction, taken or not** — that is exactly what `pendingBranch`
(Global rule 3 above) models: a taken `beq`/`bltz`/`j`/`jr`/etc. falls
through to the delay slot first, and only *then* redirects `pc`; a
not-taken `beq`/`bltz`/etc. just falls through normally, with the delay
slot executing either way. The eight instructions in this section are the
one documented exception to that global rule, by MIPS32's own architectural
definition, not by any modeling choice of this project: **if the branch is
*not* taken, the delay-slot instruction is architecturally nullified
("squashed")** — real hardware never fetches, decodes, or executes it at
all, and control falls straight through to `PC_next + 4` (i.e. `pc + 8`,
past *both* the branch and its squashed delay slot). If the branch *is*
taken, a branch-likely instruction behaves exactly like its non-likely
counterpart — the delay slot *does* execute normally in that case, with no
difference from `beq`/`bltz`/etc. at all.

This is why `beql` is not simply "`beq` with a different opcode": the
not-taken case has a genuinely different effect on what instructions
execute, not just on where `pc` ends up. Historically, this existed so
compilers could place a loop body (which, by construction, only needs to
run when the loop continues) directly in the delay slot of the
loop-continuation branch, without a wasted/no-op delay-slot instruction on
loop exit — a micro-optimization for the classic MIPS in-order pipeline,
which is also exactly why it was deprecated once pipelines/compilers moved
past needing it, per MIPS32 Release 6's removal.

### Nullification is its own instruction time

MD00086 Vol II-A Rev 6.06, BEQL, p.73: "I+1: if condition then PC ← PC +
target_offset else NullifyCurrentInstruction() endif". The `I+1` statements
take effect in the delay-slot instruction's instruction time (§1.3, Table 1.1,
p.6), and NullifyCurrentInstruction aborts that instruction, "inhibiting not
only the functional effect of the instruction, but also inhibiting all
exceptions detected during fetch, decode, or execution" (§2.2.2.5.4, p.26). In
the model a **not-taken** branch-likely's own `step` moves `pc` to the delay
slot (`pc + 4`), sets `pendingBranch := some (pc + 8)` and `nullified := true`;
the next `step` is the nullified slot's instruction time (`nullifiedStep`): the
delay-slot word is never fetched, decoded or executed, whatever it is (even
undecodable garbage or an unmapped address), `pc` becomes `pc + 8`, and `Count`
advances. An interrupt can be taken at the nullified slot (`EPC` = the branch,
`Cause.BD = 1`; SPEC-NOTES §9 item 1b). A **taken** branch-likely behaves
exactly like its non-likely counterpart. `bltzall`/`bgezall` link `$ra ← pc + 8`
unconditionally. StepSpec: `beql_spec_raw` … `bgezall_spec_raw`,
`beql_not_taken_squashes_delay_slot`, `step_nullified`.

(Before Wave 7 the branch's own step went straight to `pc + 8`, so the
nullified slot took no instruction time. Earlier still, a `State.squashNext`
flag was honored only by `run`.)

### beql / bnel (I-branch)

- **Encoding**: `beql`: `opcode=010100` (0x14). `bnel`: `opcode=010101`
  (0x15). Identical field layout to `beq`/`bne`: `rs=fffff`, `rt=sssss`,
  `offset=tttt...` (16-bit signed word displacement).
- **Semantics**: `beql`: if `$rs == $rt`, schedules `PC = PC_next +
  (offset << 2)` exactly like `beq` (the delay slot executes normally);
  otherwise (not taken) moves to the delay slot and marks it `nullified`; the
  next step consumes it without executing it (see above). `bnel` is the same with the
  condition inverted (`$rs != $rt`), exactly mirroring `bne`.
- **Errors/halts**: none directly; a branch/jump occupying a *taken*
  `beql`/`bnel`'s own delay slot raises Reserved Instruction,
  same as every other branch/jump (Global rule 3) — this check is unrelated
  to and unaffected by the not-taken squash mechanism.
- **ISA note**: real MIPS32 instruction (MIPS II onward), deprecated in
  MIPS32 and removed in Release 6 (see the scope note above). Not MARS-
  sourced; grounded directly in MD00086.
- **Source**: MD00086 Vol II-A Rev 6.06, BEQL p.73-74, BNEL p.104-106.

### blezl / bgtzl (I-branch)

- **Encoding**: `blezl`: `opcode=010110` (0x16), `rt` field fixed 0.
  `bgtzl`: `opcode=010111` (0x17), `rt` field fixed 0. Identical field
  layout to `blez`/`bgtz`.
- **Semantics**: `blezl`: if `$rs <= 0` (signed), schedules `PC = PC_next +
  (offset << 2)` exactly like `blez`; otherwise squashes the delay slot,
  same mechanism as `beql`. `bgtzl`: if `$rs > 0` (signed), schedules the
  same way as `bgtz`; otherwise squashes.
- **Errors/halts**: same delay-slot-halt and squash behavior as `beql`.
- **ISA note**: real MIPS32 instruction (MIPS II onward), deprecated in
  MIPS32 and removed in Release 6. Not MARS-sourced.
- **Source**: MD00086 Vol II-A Rev 6.06, BLEZL p.95-96, BGTZL p.89-91.

### bltzl / bgezl / bltzall / bgezall (I-branch, REGIMM)

- **Encoding**: all four share REGIMM `opcode=000001` (0x01), same major
  opcode as `bltz`/`bgez`/`bltzal`/`bgezal`/the trap-immediate family above
  — the `rt` field (not the opcode) selects which instruction it is:
  `bltzl` = `0x02`, `bgezl` = `0x03`, `bltzall` = `0x12`, `bgezall` = `0x13`.
  Identical `rs, offset` field layout to `bltz`/`bgez`/`bltzal`/`bgezal`.

  | Mnemonic | `rt` field | Semantics |
  |---|---|---|
  | `bltzl` | `0x02` | `if ($rs < 0) PC = PC_next + (offset << 2)`, signed; else squash |
  | `bgezl` | `0x03` | `if ($rs >= 0) PC = PC_next + (offset << 2)`, signed; else squash |
  | `bltzall` | `0x12` | `$ra = PC_next + 4` unconditionally; then same condition as `bltzl` |
  | `bgezall` | `0x13` | `$ra = PC_next + 4` unconditionally; then same condition as `bgezl` |

- **Semantics**: `bltzl`/`bgezl` are plain branch-likely versions of
  `bltz`/`bgez` — taken schedules `pendingBranch` exactly like `bltz`/
  `bgez`; not taken squashes, same mechanism as `beql`. `bltzall`/
  `bgezall` additionally link `$ra = PC_next + 4` (`pc + 8`, past the delay
  slot, same convention as `jal`/`bltzal`/`bgezal`) — real MIPS32 performs
  this link **unconditionally**, on every execution of the instruction,
  regardless of whether the branch itself is taken *or* squashed (same
  "link always happens" rule already documented for `bltzal`/`bgezal`
  above, now additionally confirmed to survive the squash case: the link
  is a plain register write that happens before the taken/not-taken test,
  completely independent of the delay-slot mechanism).
- **Errors/halts**: same delay-slot-halt and squash behavior as `beql`.
- **UNPREDICTABLE case**: `bltzall`/`bgezall` share the same `rs = $ra`
  (31) UNPREDICTABLE case as `bltzal`/`bgezal`, resolved the same way (the
  pre-link value of `$rs` is tested) — see `bltzal`'s entry above for the
  full discussion; nothing about that resolution changes when the branch
  is squashed rather than not-taken-and-falling-through, since the
  resolution is about which value of `$rs` is read, not about the delay
  slot at all.
- **ISA note**: real MIPS32 instruction (MIPS II onward), deprecated in
  MIPS32 and removed in Release 6. Not MARS-sourced.
- **Source**: MD00086 Vol II-A Rev 6.06, BLTZL p.101-102, BGEZL p.86-87,
  BLTZALL p.99-100, BGEZALL p.80-81.

### Encoding summary

| Mnemonic | Format | One-line semantics |
|---|---|---|
| `sync stype` | R, opcode 0, funct 0x0f, `stype` = bits 10..6 | no-op for every `stype` (falls through to `PC_next`); no concurrency/reordering model exists to order against |
| `synci offset($rs)` | I, REGIMM opcode 0x01, `rt`=0x1f | no-op (falls through to `PC_next`); `addr = $rs + sext16(offset)` computed but never used — no instruction-cache model exists to flush |

| `beql $rs, $rt, target` | I, opcode 0x14 | if `$rs == $rt`, branch (delay slot executes); else squash the delay slot |
| `bnel $rs, $rt, target` | I, opcode 0x15 | if `$rs != $rt`, branch; else squash |
| `blezl $rs, target` | I, opcode 0x16 | if `$rs <= 0` (signed), branch; else squash |
| `bgtzl $rs, target` | I, opcode 0x17 | if `$rs > 0` (signed), branch; else squash |
| `bltzl $rs, target` | I, REGIMM, `rt`=0x02 | if `$rs < 0` (signed), branch; else squash |
| `bgezl $rs, target` | I, REGIMM, `rt`=0x03 | if `$rs >= 0` (signed), branch; else squash |
| `bltzall $rs, target` | I, REGIMM, `rt`=0x12 | `$ra = PC_next+4` always; if `$rs < 0`, branch; else squash |
| `bgezall $rs, target` | I, REGIMM, `rt`=0x13 | `$ra = PC_next+4` always; if `$rs >= 0`, branch; else squash |

("branch" = schedule `PC = PC_next + (sext16(offset) << 2)` via
`pendingBranch`, delay slot executes normally, same as the non-likely
counterpart; "squash" = move to the delay slot with `pendingBranch := some (pc + 8)`
and `nullified := true`; the next step is the nullified slot's own instruction
time: the instruction at `pc + 4` is never fetched/decoded/executed and `pc`
becomes `pc + 8`.)

### Citation

MD00086 Vol II-A Rev 6.06:

- SYNC p.407-411 (SPECIAL, funct `0x0f`), SYNCI p.412-414 (REGIMM, `rt` =
  `0x1f`, MIPS32 Release 2).
- BEQL p.73-74, BNEL p.104-106, BLEZL p.95-96, BGTZL p.89-91, BLTZL
  p.101-102, BGEZL p.86-87, BLTZALL p.99-100, BGEZALL p.80-81 (all "MIPS32,
  removed in Release 6"); BC1FL p.58-59 and BC1TL p.62-63 are in the
  floating-point section.
