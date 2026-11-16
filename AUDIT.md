# Audit record: what was checked against the manuals

A compact record of the manual-grounded checks made on this tree and the decisions taken. Part A is the record of the current model,
MIPS32 **Release 6** (re-audit of wave R6-7). Part B is the audit record of the pre-Release-6 model (Release 2, tag
`mips32r2-final`), kept as history: its sections describe that model and are not statements about the current one.
Sources are named in brackets: `SN` = `docs/spec/SPEC-NOTES.md` (section/item), `PN` = `docs/PROOF-NOTES.md`, `oracle` = a `# oracle:`
directive in `tests/oracle/*.asm` (or `ASM_DIRECTIVES` in `scripts/oracle.py`), a commit hash = its message (`git log`). A claim that
none of these sources supports is not here. This is a record of checks, not a certificate: it states what was looked at, not that nothing
else is wrong. Manual references: MD00086 Vol II-A Rev 6.06 (Vol II), MD00090 Vol III Rev 6.02 (Vol III), MD00082 Vol I-A Rev 6.01
(Vol I), printed pages.

# Part A. Release 6 (wave R6-7 re-audit)

Wave R6-7 (commit 0e7ef66, merged 63e01a2) closed Release 6 coverage with two audits and a re-audit of every pin and every oracle
directive. Work was done in worktrees with `manuals/mipsdoc.py`; image-only pages (EXT p.183, ALIGN p.39, CFC1 p.130's relational glyph,
Status Table 9.47 p.190) were read by rendering the PDF page. The detailed tables are the wave's working notes (pins:
`PINS-R6.md`, coverage: `COVERAGE-R6.md`); the coverage result is `docs/spec/R6-COVERAGE.md`, and the pins are in `docs/spec/SPEC-NOTES.md`.

## A.1 Pins re-audited (PINS-R6.md)

Four groups, 89 rows in all: (A) the `Impl` constants of `Manual/Choices.lean` (`modelImpl`: Count rate, PRId, Config 0..5, SRSCtl,
IntCtl, FIR, `CCASupported`); (B) the `Oracle` choice points (`modelOracle`); (C) misprint and erratum readings and the profile
decisions D1-D13; (D) the directives of `tests/oracle/*.asm` (105 `expect-deviation`, 92 `unpredictable`, 0 `known-model-bug`).
Verdicts: **63 OK**, 4 OK with a note or an extended comment, 5 notes (legitimate, worth recording), **16 citations corrected**, **1 wrong
directive (fixed)**, **no wrong choice**. Examples of corrected citations:

* `Config3 = 0x8C00_3000`: the BP/BI quotation was a merged paraphrase; now two verbatim quotes, "Release 6: BadInstrP is always
  implemented." and "Release 6: BadInstr is always implemented." (Vol III §9.48 p.246), ULRI and RXI p.248.
* `SRSCtl = 0`: Vol III Chapter 7 p.103 says "shadow set zero", not "set 0".
* `FIR = 0x00F3_0000`: §6.5.1 starts Vol I p.87; Table 6.5 is p.88-90 (`Has2008` p.88; `F64` "In Release 6, StatusFR is read-only 1" p.89;
  Table 6.4 note 3 p.85).
* `storeClearsLL`/`loadClearsLL`: the pre-Release-6 wording "there is no `Config5`" is wrong for Release 6; SC p.347-348 with
  `Config5.LLB = 1` ("In Release 6, Config5LLB is read-only 1", Vol III Table 9.69 p.264).
* `unpredictableEncoding`: the pages do not call a JALR hint UNPREDICTABLE (JALR p.196 defines two values, JALR.HB p.198), the
  docstring now says so.
* Directive citations: `exc_sc_misaligned` (SC p.349, quote added), `fp_cfc1_ri_fs1` (CFC1 `fs = 1` "Release 6 traps" is on p.129, not p.130),
  `fp_flush_to_zero_fs` (Vol I §6.7.2.4 p.102), `fp_nan_propagation_quiet` ("(or the default QNaN)" contradicted "When possible, this
  QNaN result is one of the operand QNaN values", p.82), `cp0_config_k0_rw` (bit 7 is in `MT`, not `Impl`), `sc_without_ll` (on Release 6 it is
  not UNPREDICTABLE: success or failure is mandated with `Config5.LLB = 1`, SC p.348).

## A.2 Wrong directive fixed

`tests/oracle/cti_in_delay_slot_reserved.asm` carried six `unpredictable` lines (gpr, cause, epc, status, pc, term) for a control transfer
instruction in a delay slot, citing "BEQ p.72: CTI in a delay slot is UNPREDICTABLE". That is the pre-Release-6 text. BEQ p.72 and JALR p.196
read: "Pre-Release 6: ... UNPREDICTABLE"; "Release 6: ... Release 6 implementations are required to signal a Reserved Instruction
exception" (Vol I §5.3.2.1 p.62 says the same). The directive declared a mandated behaviour as not comparable, so a regression would
have passed. The six lines were removed and the header rewritten with the Release 6 citations; every field is now compared and QEMU agrees
(`python3 scripts/oracle.py --only cti_in_delay_slot_reserved`). The model's side is `forbidden_slot_cti_reserved` and
`branch_in_delay_slot_reserved_instruction` on the trusted surface.

## A.3 Probes run, and the model fixes they caused

* `div/mod/divu/modu rd, rs, $zero`: model and QEMU `mips32r6-generic` agree, so the `Oracle.divByZero` docstring's QEMU claim holds.
* `cfc1 $s0, $5` (FRE): the model read 0 without an exception; QEMU signals Reserved Instruction. The pages support QEMU
  (CFC1 p.129 Restrictions; p.130 `ConfigAR <= 2` read as `< 2`). Model changed in R6-7: CFC1 `fs = 5` raises Reserved Instruction, which removes the
  `cfc1Unpredictable` choice point; `cfc1_spec_raw` keeps its text, its meaning changed.
* Gap found by the coverage audit (A.4): DVP and EVP raised Reserved Instruction; reproducer `tests/oracle/r6gap_dvp_evp.asm` (model RI four times,
  QEMU no-op) before the fix.

## A.4 Coverage audit (COVERAGE-R6.md)

Every instruction page of MD00086 Vol II-A Rev 6.06 (`python3 manuals/mipsdoc.py list`: **263 pages**, the duplicate titles DIV and
MUL counted per page) was classified against the profile of CLAUDE.md:

| class | pages |
|---|---:|
| (a) implemented | 137 |
| (b) removed in Release 6 | 77 |
| (c) optional module or feature absent | 36 |
| (d) TLB instruction, Reserved Instruction under the Fixed Mapping MMU | 6 |
| (e) assembler idiom | 7 |
| (f) gap (open) | 0 |

Evidence per row: for (a), the constructor, decode/encode (`decode_encode`), step arm, `_spec_raw` and `_refines` (`trace.py --check`, 203/203);
for (b), (c), (d), a `decode` probe of the removed or absent encoding (words from `llvm-mc-21 -show-encoding` or built from the page diagram) and the
exception it raises by encoding space (COP0: Coprocessor Unusable outside Kernel Mode, else Reserved Instruction; COP1: Coprocessor
Unusable with `CE = 1` if `CU1 = 0`, else Reserved Instruction; COP2: Coprocessor Unusable with `CE = 2`; else Reserved Instruction);
for (e), `AsmTests` guards, `encodings.list` and the QEMU oracle. **One gap class was found: DVP and EVP** (DVP p.172-173, EVP p.181-182:
no-ops with `Config5.VP = 0`), closed by two new constructors (201 → 203). Idiom changes: the bgtc/blec/bgtuc/bleuc operand-swap forms
(B<cond>C p.83) were added to the assembler (llvm-mc-21 rejects them; the QEMU oracle program `r6gap_reversed_compact` checks taken and not taken; the
p.83 text for BLEUC reads "GPR rt ... GPR rt", a misprint for rs), and SSNOP is rejected (SSNOP p.387: "Assemblers targeting specifically Release 6
should reject the SSNOP instruction with an error"; the word 0x00000040 still decodes as `sll`).
New gate check from this audit: every constructor must be executed by some QEMU oracle program (203/203, gate step 7).

## A.5 Where the spec is looser or stricter than the manual (recorded, not model bugs)

* **Looser: LL/SC same-block rule.** With `Config5.LLB = 1` a store to the LL block must fail the SC and a load must not (SC p.347-348; Vol III
  Table 9.69 p.264). The oracle fields `storeClearsLL`/`loadClearsLL` take no address, so `Manual.Step` also admits oracles that Release 6 forbids for
  same-block accesses. The model's constants (`true`, `false`) are the only correct ones for every address. Tightening needs the
  implementation-dependent block size in `Impl`.
* **Stricter: `BadInstrP` in a forbidden slot.** Vol III §9.26 p.181 makes `BadInstrP` UNPREDICTABLE outside a branch delay slot, and speaks only of
  a delay slot; Vol I §5.3.2.2 p.62 treats delay and forbidden slots alike for EPC and BD. `Manual.GeneralExceptionProcessing` fixes `BadInstrP` to the
  compact branch word instead of asking `Oracle.badInstrP`. A permitted value; the spec is stricter than the manual there.
* **Note: `Config4.IE`.** Table 9.68 p.254 states two readings (TLBINV/TLBINVF must be supported; required for TLB implementations) that conflict with TLBINV p.423 and
  TLBINVF p.426 ("on processors that include a BAT or Fixed Mapping MMU (ConfigMT = 2 or 3)" the operation raises Reserved Instruction). Pin: `IE = 0` and RI.
* **Note: `LLAddr.PAddr`** not implemented (reads 0, writes ignored): Vol III Table 9.72 p.270 permits "as many of the bits ... as it finds convenient"; `LLB` is implemented.
* **Note: WAIT.** The prose (p.442) says it resumes on an interrupt "even if interrupts are not enabled"; the Release 6 pseudocode (p.442-443) tests
  `interrupt_pending_and_not_masked_out` (IP & IM). The pseudocode is transcribed (D9).
* **Note: `PAUSE`** with `LLbit = 1` enters standby with `EPC ← PC + 4`; `DescheduleInstructionStream()` is undefined in the manual and is read as WAIT-like (PAUSE p.317).
* **Note: COP2.** COP2-space words signal Coprocessor Unusable with `CE = 2` (no CP2; Vol III §6.2.22 p.100); QEMU raises Reserved Instruction (declared deviation,
  `tests/oracle/r6gap_absent_modules.asm`).
* **Note: `Status` bit 28** is `RW`, not `CU0` (Vol III Table 9.47 p.190, image-only page, read in the PDF), although §3.5.3 p.23 still lists CU0.

Misprint readings recorded in the pins (each with its page): ALIGN `tmp_rt_lo` read as `tmp_rs_lo` (p.39); the CFC1 relational glyph (p.130); the
`-2^63-1` of the `.L` and CVT.W pages read as the Table 6.3 values (p.82); MADDF/MSUBF `vfr` and MADDF twice (p.260); B<cond>C `PC+4+sign_extend(offset)`
read as `target_offset` (p.84, D11); BOVC/BNVC and BC1EQZ/BC1NEZ offsets (p.107-108, p.54-55); MIN/MAX function codes from the diagrams (p.262) rather than Table A.15 (p.456); "StatusBD" read as
`CauseBD` (Vol I p.62).

# Part B. The Release 2 model (history, tag `mips32r2-final`)

The record below was written for the pre-Release-6 model (Release 2, big-endian, 32-bit FPU, legacy NaNs, branch-likely, HI/LO) and is kept
as written. Decisions in it that Release 6 reversed (HI/LO, legacy NaN, `FIR = 0x0033_0000`, `LLbit` cleared by every exception entry, the
`mul` pin, the QEMU 24Kf oracle) do not describe the current model; see Part A, `docs/PROOF-NOTES.md` (R6-1 to R6-7) and `docs/spec/SPEC-NOTES.md`.

## B.1 Method

- Revisions: the latest revisions are normative and read for pre-Release-6 wording; Rev 2.50 citations that remain in
  comments are historical [PN "Module headers"; CLAUDE.md].
- Lookups were made with `manuals/mipsdoc.py` [CLAUDE.md]. Commit fa2275b records the exception model,
  decoding and CP0 behaviour as "audited against MD00086 Rev 6.06 / MD00090 Rev 6.02"; 94468fb records the FPU as
  "brought to the manual (MD00086 Rev 6.06, MD00082 Rev 6.01, legacy FP)".
- Differential evidence was added as a second line: MARS (`tests/corpus`) and QEMU 24Kf with an LLVM encoding oracle
  (`tests/oracle`) [fddea0e]. Where QEMU departs from the manual the manual won and the difference is declared (section 4).

## B.2 Decisions taken from the manuals (behaviour)

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

## B.3 Pins added by the independent audit (all in SN §9)

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

## B.4 Where an oracle disagreed with the manual (the manual won)

Declared in the tests and tabulated in SN §10; each citation was re-checked with `mipsdoc.py` while writing this record.
`exc_sc_misaligned` (SC p.349); `exc_lwxc1_misaligned`, `exc_ldxc1_misaligned`, `exc_swxc1_misaligned`,
`exc_sdxc1_misaligned` (p.254, p.218, p.406, p.364); `fp_flush_to_zero_fs` (Vol I §6.7.2.4 p.102); `fp_abs_neg_nan` and
`tests/asm/fp_legacy_nan` (ABS.fmt p.32, NEG.fmt p.307); `fp_trap_enabled_handler` (Vol I §6.7.2.6 p.102). Gate record of
fddea0e: 135 tests, 126 pass, 9 declared QEMU deviations, 0 known model bugs; encodings 581 identical, 13 declared, 0 mismatches.
MARS divergences (SN §9 items 1, 3, 4, 5; item 14) are the other source of declared differences.

## B.5 Corrections made to citations and claims

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

## B.6 The model as of wave 6 (commits f620266 to 0f72c83 and the wave-6 tree)

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

## B.7 Known gaps in this record

- The semantics is not machine-checked against the manuals; the checks above are lookups and reviews by the authors.
- UNPREDICTABLE pins are choices, not facts about the architecture.
- (Wave 10: the FP rounding core, the integer square root and `ADD`/`SUB`/`MUL`/`DIV`/`SQRT` are now proved correct against `Semantics/FpOpsSpec.lean`; README (d).) Earlier: no general proof of the FP rounding core or the integer square root; no proof that the FP compare field order equals the order
  of rational values [PN "Compare predicates"; b236c1f].
- Not compared with an emulator: EBase relocation, the reset vector boot (SN §9.10), interrupts in a branch delay slot, the
  hardware interrupt lines (the environment never asserts them; Malta's own HW0 is masked in the tests), `SRSMap` access, a `wait`
  restarted by a non-enabled request (SN §9.23, §9.29). Interrupts by software request and by the timer, `Cause.IV`, `wait` woken
  by the timer, `IntCtl`/`SRSCtl` reads and `rdpgpr`/`wrpgpr` are compared since wave 6 (`tests/oracle/irq_*`, `rdpgpr_wrpgpr`).
- What the model lacks is in `docs/spec/MIPS-COVERAGE-GAPS.md`.
