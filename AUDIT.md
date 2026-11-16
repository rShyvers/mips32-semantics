# Audit record: what was checked against the manuals

A compact record of the manual-grounded checks made during the work that produced this tree, and the decisions
taken. Sources are named in brackets: `SN` = `docs/spec/SPEC-NOTES.md` (section/item), `PN` = `docs/PROOF-NOTES.md`,
`oracle` = a `# oracle:` directive in `tests/oracle/*.asm` (or `ASM_DIRECTIVES` in `scripts/oracle.py`), a commit hash =
its message (`git log`). A claim that none of these sources supports is not here. This is a record of checks, not a
certificate: it states what was looked at, not that nothing else is wrong. Manual references: MD00086 Vol II-A Rev 6.06
(Vol II), MD00090 Vol III Rev 6.02 (Vol III), MD00082 Vol I-A Rev 6.01 (Vol I), printed pages.

## 1. Method

- Revisions: the latest revisions are normative and read for pre-Release-6 wording; Rev 2.50 citations that remain in
  comments are historical [PN "Module headers"; CLAUDE.md].
- Lookups were made with `manuals/mipsdoc.py` [CLAUDE.md]. Commit fa2275b records the exception model,
  decoding and CP0 behaviour as "audited against MD00086 Rev 6.06 / MD00090 Rev 6.02"; 94468fb records the FPU as
  "brought to the manual (MD00086 Rev 6.06, MD00082 Rev 6.01, legacy FP)".
- Differential evidence was added as a second line: MARS (`tests/corpus`) and QEMU 24Kf with an LLVM encoding oracle
  (`tests/oracle`) [fddea0e]. Where QEMU departs from the manual the manual won and the difference is declared (section 4).

## 2. Decisions taken from the manuals (behaviour)

| Topic | Decision | Manual |
|---|---|---|
| Exception entry | `EPC`/`Cause.BD` only if `EXL = 0`; `EPC = pc - 4` and `BD = 1` in a delay slot; `ExcCode`-only `Cause` update; `BEV` selects the vector, `EBase` the base; pending branch abandoned; `Status.EXL ← 1` [fa2275b; `Exception.lean`] | Vol III §6.2.3 General Exception Processing, p.86-88 |
| `LLbit` | cleared by every exception entry and by `eret` [fa2275b; SN §9.7] | Vol II SC, p.350 ("Exceptions between the LL and SC cause SC to fail"); Vol II ERET, p.177 |
| `eret` | honours `ERL` (`ErrorEPC`), clears `EXL`/`ERL` [fa2275b] | Vol II ERET, p.177 |
| Integer Overflow, Address Error, Reserved Instruction are exceptions, not halts [fa2275b; SN §3, §9.12]; since f620266 `syscall` is always the System Call exception and `step` never halts (the MARS-style services are the environment's, `Env.lean`) [f620266; SN §9.9, §9.12] | | Vol III §6.2; Vol II SYSCALL, p.415 |
| `div`/`divu` by zero | `HI`/`LO` unchanged, no trap; a pin [SN §9.2] | Vol II DIV, p.165 ("UNPREDICTABLE", "No arithmetic exception occurs under any circumstances") |
| Strict decoding | nonzero must-be-zero fields, `clz`/`clo` with `rt != rd`, bad `ext`/`ins` ranges give Reserved Instruction; a pin of UNPREDICTABLE [fa2275b; SN §9.11] | Vol II §2.1.1, p.12 (fields "UNPREDICTABLE" if nonzero); §1.2.1, p.3 (pdf 13) |
| Store/`LLbit` | every store-class instruction clears `LLbit`; `sc` fails on an address different from the preceding `ll` [94468fb; SN §9.7] | Vol II SC, p.347-349 |
| Coprocessor Unusable | any COP1/COP1X instruction with `Status.CU1 = 0`, `Cause.CE = 1`; COP2-space words raise it with `CE = 2` [94468fb; SN §9.10] | Vol III §6.2.22, p.100 |
| FPU state | `FCSR` with eight condition codes, rounding mode, flags, enables, cause; `FIR/FCCR/FEXR/FENR` views; bits 22..18 read zero [94468fb; SN §9.13] | Vol I §6.5.4, p.92 |
| FP arithmetic | exact rational result and one rounding in all four rounding modes; enabled FP exceptions trap (ExcCode 15) without writing the destination [94468fb] | Vol I §6.7, p.99-102 |
| Float to word | honours the rounding mode and returns `0x7FFFFFFF` on invalid [94468fb; SN §9.13] | Vol II ROUND.W.fmt, p.342; Vol I Table 6.3, p.82 |
| `ldc1`/`sdc1`/`ldxc1`/`sdxc1` | need doubleword alignment; `lwxc1`/`swxc1` word alignment [94468fb; oracle `exc_*xc1_misaligned`] | Vol II LDC1 p.215, LDXC1 p.218, SDXC1 p.364, LWXC1 p.254, SWXC1 p.406 |
| Legacy NaN, default QNaN | `0x7FBFFFFF` / `0x7FF7FFFF_FFFFFFFF`; `abs`/`neg` arithmetic [94468fb; SN §9.13] | Vol I Table 6.3, p.82; Vol II ABS.fmt p.32, NEG.fmt p.307 |
| `FIR` | `FIR = 0x0033_0000`, `L = 1` since 6b88488 (was `0x0013_0000`); the L-format instructions stay undecoded: the manuals are inconsistent about `FIR.L` with `FR = 0` (SN §9.13) | Vol I Table 6.4, p.85; Vol II CVT.L.fmt, p.154 |
| `NMADD`/`NMSUB` | follow "as if separate instructions" (a NaN sum signals Invalid) [SN §9.13] | Vol II NMADD.fmt, p.308 |
| `RECIP`/`RSQRT` | pinned to `1.0 / x` and `1.0 / sqrt(x)`; the oracle declares accuracy `unpredictable` [SN §9.13; oracle `fp_recip_rsqrt_inexact`] | Vol II RECIP.fmt, p.336; RSQRT.fmt, p.343 |
| NaN operand order | first quiet NaN operand in operand order [SN §9.13; `Format.nanResult`]; the oracle declares the choice `unpredictable` [oracle `fp_nan_propagation_quiet`] | Vol I §6.3.1.5, p.82 |

## 3. Pins added by the independent audit (all in SN §9)

| Pin | SN item | Manual |
|---|---|---|
| `mul` leaves `HI`/`LO` unchanged | 17 | Vol II MUL, p.299 |
| `abs.fmt`/`neg.fmt` of a quiet NaN return the operand unchanged and signal Invalid (ambiguous text: both "negated by changing the sign bit" and "any NaN operand signals invalid operation") | 21 | Vol II ABS.fmt p.32, NEG.fmt p.307; Vol I §6.3.1.5 p.82, §6.7.2.1 p.100 |
| NaN payload narrowing in format conversion | 22 | Vol I §6.3.1.5, p.82 |
| `wait` was a no-op until wave 6; since then it enters standby until an interrupt request (non-enabled unmasked requests restart it, `Count` keeps counting) | 23 | Vol II WAIT, p.442-443 |
| `printStringFuel` bounds syscall 4 | 20 | environment convention, not architectural |
| `Cause.CE` written as 0 for exceptions other than Coprocessor Unusable | 24 | Vol III Cause §9.36, p.209 |
| `jr`/`jalr` hint: only 0 (`jr`/`jalr`) and `10000` (`jr.hb`/`jalr.hb`) decode, others Reserved Instruction (7R; formerly tolerated) | 19 | Vol II JR p.207, JALR p.196 |
| `bltzal`/`bgezal` with `rs = 31` and `jalr` with `rs = rd` | 18 | Vol II BLTZAL p.98, BGEZAL p.76, BLTZALL p.99, BGEZALL p.80, JALR p.196 |
| `pause`/`nal` decode as `sll`/`bltzal $0`; assembler mnemonics since 6b88488 | 16 | Vol II PAUSE p.317, NAL p.306 |
| the `LLbit`-clearing store list includes `swxc1`/`sdxc1` | 7 | Vol II SC, p.348 |

## 4. Where an oracle disagreed with the manual (the manual won)

Declared in the tests and tabulated in SN §10; each citation was re-checked with `mipsdoc.py` while writing this record.
`exc_sc_misaligned` (SC p.349); `exc_lwxc1_misaligned`, `exc_ldxc1_misaligned`, `exc_swxc1_misaligned`,
`exc_sdxc1_misaligned` (p.254, p.218, p.406, p.364); `fp_flush_to_zero_fs` (Vol I §6.7.2.4 p.102); `fp_abs_neg_nan` and
`tests/asm/fp_legacy_nan` (ABS.fmt p.32, NEG.fmt p.307); `fp_trap_enabled_handler` (Vol I §6.7.2.6 p.102). Gate record of
fddea0e: 135 tests, 126 pass, 9 declared QEMU deviations, 0 known model bugs; encodings 581 identical, 13 declared, 0 mismatches.
MARS divergences (SN §9 items 1, 3, 4, 5; item 14) are the other source of declared differences.

## 5. Corrections made to citations and claims

- SN §9 item 11 cited "bltzal/bgezal(+likely) with rs = 31 (pp. 97-98)"; the pages are BLTZAL p.98, BGEZAL p.76,
  BLTZALL p.99, BGEZALL p.80 (`mipsdoc.py list`). Corrected, and the content of the pin written out (item 18).
- SN §9 item 7 and the `State.llBit` docstring listed the `LLbit`-clearing stores without `swxc1`/`sdxc1`; `Step.lean`
  clears it for both. SN corrected; the docstring in `Types.lean` is still stale (not changed: no `.lean` edits in the documentation pass).
- The docstring of `branch_in_delay_slot_halts` in `Semantics/Statements.lean` counts 24 instructions of `isBranchLike` and
  omits `bc1fl`/`bc1tl`; `isBranchLike` in `Step.lean` lists 26 (12 branches/jumps, 8 branch-likely, 4 FP branches, `eret`, `wait`).
  Comment only; the statement is unaffected (it quantifies over `isBranchLikeSpec`). Not changed here.
- The "p.3" and "p.12" citations of Vol II refer to the body pages (pdf 13 and 22); the table of contents also has a "p.3".
- Rev 2.50 page numbers that appear in older INSTRUCTION-REF sections are historical; the citation convention is stated at the top
  of that file. A mechanical check of `NAME p.N` citations in INSTRUCTION-REF.md and SPEC-NOTES.md against `mipsdoc.py list`
  (271 citations matched) found no mismatch other than Rev 2.50 EXT p.131, which is correct for that revision.
- README, DESIGN and MIPS-COVERAGE-GAPS had described a 76-instruction, single-precision, partially proved model; they were rewritten
  against `scripts/trace.py` output and the sources.

## 6. The model as of wave 6 (commits f620266 to 0f72c83 and the wave-6 tree)

What the model is now, with the manual sections each part was checked against; details in SN §9 items 6, 9-10, 23, 25-29 and
`docs/spec/COMPLIANCE.md` (every Vol III chapter 9 register and every Vol II instruction-list entry, with a verdict; after wave 6:
411 rows, 202 conform, 59 permitted pins, 0 departures, 0 missing-required, 101 declared optional-absent, 49 outside the profile).

| Part | Model | Manual |
|---|---|---|
| `step` | `step : State → State`, total; one instruction time = `timerTick (stepCore s)`: an enabled interrupt, else a standby step, else fetch (from `physMem` through the MMU), decode, execute; no halting state [f620266; SN §9.6, §9.12, §9.29] | Vol III §6.1-6.2 |
| Environment | loader, boot convention, MARS-style services, stopping conventions and the hardware interrupt lines' drive are in `Env.lean`, outside the architecture [f620266, 66da8b5; SN §9.25, §9.29] | (none: environment) |
| Reset | `resetException`/`resetState`: PC `0xBFC0_0000`, `BEV = ERL = 1`, `Cause.DC ← 0`, `HWREna ← 0`, `EBase` base 0, `Config.K0 ← 2`, `ErrorEPC ←` restart PC, standby cleared; `IntCtl.VS`, `SRSCtl` hold their reset values (constants) [66da8b5; SN §9.10] | Vol III §6.2.5, p.89-90 |
| Modes | Kernel/User Mode (`UM`, `EXL`, `ERL`), `CU0` access rule, Coprocessor Unusable (`CE = 0`) for CP0 instructions outside Kernel Mode [66da8b5; SN §9.10] | Vol III §3.2-3.5, p.21-23; §6.2.22, p.100 |
| MMU | Fixed Mapping MMU (`Config.MT = 3`), physical memory, kuseg `+1 GB` with `ERL = 0`, identity with `ERL = 1`, User-Mode Address Errors [166a67a; SN §9.26-9.27] | Vol III Appendix A.1, p.313-317; Table 4.2, p.30 |
| Timer, `RDHWR` | `Count` + 1 per step unless `Cause.DC = 1`, `Compare`, `Cause.TI` merged into `IP7` (`IntCtl.IPTI = 7`), `HWREna`, `RDHWR` 0-3 [0f72c83; SN §9.28] | Vol III §9.27, §9.30, §9.23; Vol II RDHWR, p.332-334 |
| Interrupts | compatibility mode; request = `Cause.IP & Status.IM`, taken when `IE = 1`, `EXL = ERL = 0`, before the fetch; `ExcCode` 0, EPC/BD as for any exception, vector `0x180`/`0x200` by `Cause.IV`; sources: `IP1..0`, the timer, six hardware lines (`State.hwInt`, inputs held at 0 by the environment); hazards cleared at once [wave 6; SN §9.29] | Vol III §6.1, p.71-73; Table 6.6-6.7, p.83-84; §6.2.26, p.102; Table 6.10, p.86 |
| `wait` | standby until an interrupt request [wave 6; SN §9.23] | Vol II WAIT, p.442-443 |
| `IntCtl`, `SRSCtl`, shadow sets | constants `0xE000_0000` and 0 (`HSS = 0`); `SRSMap` RI (UNPREDICTABLE access); `rdpgpr`/`wrpgpr` on shadow set 0 [wave 6; SN §9.29] | Vol III §9.33-9.35, p.199-207; §7, p.103; Vol II RDPGPR p.335, WRPGPR p.444 |
| Trusted surface | `Semantics/Statements.lean`, 139 statements after wave 6 (116 before; 216 now, see `docs/PROOF-NOTES.md`); 68 of the older statements gained the hypothesis `executesInstr s = true` in wave 6, a weakening forced by interrupts (SN §9.29) [PN "The comparator arrangement"] | - |

## 7. Known gaps in this record

- The semantics is not machine-checked against the manuals; the checks above are lookups and reviews by the authors.
- UNPREDICTABLE pins are choices, not facts about the architecture.
- (Wave 10: the FP rounding core, the integer square root and `ADD`/`SUB`/`MUL`/`DIV`/`SQRT` are now proved correct against `Semantics/FpOpsSpec.lean`; README (d).) Earlier: no general proof of the FP rounding core or the integer square root; no proof that the FP compare field order equals the order
  of rational values [PN "Compare predicates"; b236c1f].
- Not compared with an emulator: EBase relocation, the reset vector boot (SN §9.10), interrupts in a branch delay slot, the
  hardware interrupt lines (the environment never asserts them; Malta's own HW0 is masked in the tests), `SRSMap` access, a `wait`
  restarted by a non-enabled request (SN §9.23, §9.29). Interrupts by software request and by the timer, `Cause.IV`, `wait` woken
  by the timer, `IntCtl`/`SRSCtl` reads and `rdpgpr`/`wrpgpr` are compared since wave 6 (`tests/oracle/irq_*`, `rdpgpr_wrpgpr`).
- What the model lacks is in `docs/spec/MIPS-COVERAGE-GAPS.md`.
