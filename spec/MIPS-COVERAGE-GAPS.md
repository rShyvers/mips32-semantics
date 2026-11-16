# What the model does not cover

This is the gap analysis of the modeled processor against the architecture it targets: a pre-Release-6
MIPS32 processor with the Release 2 feature set, big-endian, 32-bit FPU (`Status.FR = 0`), legacy FP
(`FIR.Has2008 = 0`). The normative documents are MD00086 Vol II-A Rev 6.06, MD00090 Vol III Rev 6.02
and MD00082 Vol I-A Rev 6.01, read for their pre-Release-6 wording. Citations give document, revision,
instruction or section, and the printed page; each was looked up with
`manuals/mipsdoc.py`. The "priority" column is the authors' judgment, not the manual's.

What *is* modeled is in the root `README.md` (coverage table, generated from `scripts/trace.py`) and
`docs/TRACE.md`. The items below were checked against `python3 scripts/trace.py --json` (the 179
constructors of `Instruction`): none of them has a constructor. Pinned UNPREDICTABLE choices and
deliberate divergences are in `SPEC-NOTES.md`, not here.

## 1. What the manual requires, and the model lacks

MD00086 §3.1.1 (Vol II-A Rev 6.06, p.29): "All non-privileged ... CPU (non-FPU) instructions must be
implemented — no subsetting of these are allowed — per the MIPS Instruction Set Architecture release
supported." Privileged features and the optional units are subsettable (p.30-31); each row says which
case applies.

### 1.1 Non-privileged instructions and the FPU

| Missing | Manual | Status in the manual | Priority |
|---|---|---|---|
| L-format (`cvt.l.fmt`, `round.l`, `trunc.l`, `ceil.l`, `floor.l`, `cvt.s.l`, `cvt.d.l`) | MD00086 Vol II-A Rev 6.06, CVT.L.fmt p.154; ROUND.L p.341; TRUNC.L p.440; CEIL.L p.127; FLOOR.L p.185 | UNPREDICTABLE in the FR = 0 model (p.154: "The result of this instruction is UNPREDICTABLE if the processor is executing in the FR=0 32-bit FPU register model"). Yet p.30 lists the pre-Release-6 FPU with `FIR.L = 1` and "Status.FR=0 support is required", and Vol I-A Table 6.4 (p.85) requires `FIR.D = FIR.L = 1` on a Release 2 32-bit FPU. **The manual is inconsistent here** (see also SPEC-NOTES §9 item 13); the model reports `FIR.L = 1` (as p.30 and Table 6.4 require) and does not decode these words (Reserved Instruction: a pin of the UNPREDICTABLE result) | Low: nothing predictable can be specified for FR = 0 |
| `LUXC1`, `SUXC1` | MD00086 Vol II-A Rev 6.06, LUXC1 p.234, SUXC1 p.391 (MIPS32 Release 2, removed in Release 6) | The FR = 0 restriction applies to these too: the model does not decode them | Low |
| Paired-single (`add.ps` ... `c.cond.ps`, `movf.ps`, `cvt.ps.s`, `cvt.s.pl`/`pu`, `pll`/`plu`/`pul`/`puu.ps`, `alnv.ps`) | MD00086 Vol II-A Rev 6.06, CVT.S.PL p.157, CVT.S.PU p.158, PLL.PS p.319, PLU.PS p.320, PUL.PS p.330, PUU.PS p.331, ALNV.PS p.41-42; NEG.PS p.307 | Optional (`FIR.PS`, p.30) and "UNPREDICTABLE if the processor is executing in the FR=0 32-bit FPU register model" (NEG.PS, p.307) | Low |

### 1.2 Privileged resources (Coprocessor 0)

| Missing | Manual | Status in the manual | Priority |
|---|---|---|---|
| Vectored Interrupt (VI) and External Interrupt Controller (EIC) modes; `SRSMap` (12, 3); GPR shadow sets beyond the normal GPRs. (Interrupt compatibility mode, the Interrupt exception, `IntCtl`, `SRSCtl` and `RDPGPR`/`WRPGPR` on shadow set 0 are modeled since wave 6: SPEC-NOTES §9 item 29) | MD00090 Vol III Rev 6.02, §6.1.1 p.72 (VI, EIC: "optional"), §9.35 SRSMap p.207, §7 p.103; §9.34 SRSCtl p.203 (`HSS = 0`: "only the normal GPRs are implemented") | Optional: VI/EIC are announced by `Config3.VInt`/`VEIC` (absent: Config3 reads 0); SRSMap is required only "if Additional Shadow Sets and Vectored Interrupt Mode are Implemented" (p.207) | Low |
| TLB and the TLB instructions `TLBP`, `TLBR`, `TLBWI`, `TLBWR` (and optional `TLBINV`, `TLBINVF`); TLB exceptions; `Index`, `Random`, `EntryLo0/1`, `Context`, `PageMask`, `Wired`, `EntryHi` | MD00086 Vol II-A Rev 6.06, TLBP p.427, TLBR p.428-429, TLBWI p.430-431, TLBWR p.432-433, TLBINV p.422-424 (optional, `Config4.IE`); MD00090 Vol III Rev 6.02, §6.2.10 p.93, §9.4 Index p.119, §9.6 Random p.123, §9.7 EntryLo p.125, §9.9 Context p.137, §9.13 PageMask p.147, §9.21 Wired p.169, §9.29 EntryHi p.185 Optional: the model has the Fixed Mapping MMU instead (`Config.MT = 3`; MD00090 Vol III Rev 6.02 Appendix A.1, p.313-317), under which "The TLBWR, TLBWI, TLBP, and TLBR instructions are no longer required and must cause a Reserved Instruction Exception" (§A.1.3, p.317) and the TLB registers "may be removed" (p.317). Segments, the `ERL = 1` kuseg mapping, kseg0/kseg1 aliasing and the User-Mode Address Errors are modeled (SPEC-NOTES §9 item 27) | Medium: a TLB is needed to run a paging OS; not needed for bare programs |
| `CACHE` (and the cache-related CP0 state) | MD00086 Vol II-A Rev 6.06, CACHE p.114-121 | Caches are optional (p.30); `Config1` reports none | Low |
| Watch registers `WatchLo`/`WatchHi`, Watch exception | MD00090 Vol III Rev 6.02, §9.55 p.279 ("Compliance Level: Optional"), §9.56 p.281, §6.2.25 p.101 | Optional (`Config1.WR = 0`) | Low |
| EJTAG: `SDBBP`, `DERET`, `Debug`, `DEPC`, `DESAVE` | MD00086 Vol II-A Rev 6.06, SDBBP p.361, DERET p.163; MD00090 Vol III Rev 6.02, §9.58 Debug p.285, §9.60 DEPC p.289, §9.69 DESAVE p.309 | Optional; "If EJTAG is not implemented, the EJTAG instructions (SDBBP and DERET) can be subsetted out" (MD00086 p.31) | Low |
| Coprocessor 2: `COP2`, `MFC2`, `MTC2`, `CFC2`, `CTC2`, `LWC2`, `SWC2`, `LDC2`, `SDC2`, `BC2F/T/FL/TL` | MD00086 Vol II-A Rev 6.06, COP2 p.141-142, CFC2 p.131, LDC2 p.216-217, BC2F p.66; p.30 ("Coprocessor 2 is optional and may be omitted") | Optional. The model has `Config1.C2 = 0`, so every COP2-space word raises Coprocessor Unusable with `Cause.CE = 2` (SPEC-NOTES §9 item 10) rather than Reserved Instruction | None unless a COP2 is wanted |
| Other CP0 registers (`Config4`, `Config5`, `UserLocal`, `PerfCtl`/`PerfCnt`, `LLAddr`, `NestedEPC`, `CMGCRBase`, ...), and `mfc0`/`mtc0` of any unmodeled register or `sel` | MD00090 Vol III Rev 6.02, §9.49-9.50 Config4-5 p.253-266, §9.11 UserLocal p.143, §9.61 Performance Counter p.291, §9.52 LLAddr p.269 | The model implements `HWREna`, `BadVAddr`, `Count`, `Compare`, `Status`, `IntCtl`, `SRSCtl`, `Cause`, `EPC`, `PRId`, `EBase`, `Config`, `Config1`, `Config2`, `Config3`, `ErrorEPC`; an access to any other register raises Reserved Instruction (SPEC-NOTES §9 items 10, 11). UserLocal (and so `rdhwr 29`) is optional pre-Release 6 and absent (`Config3.ULRI = 0`; SPEC-NOTES §9 item 28) | Low |

## 2. Later-release and optional features that are out of the Release 2 profile

These are not required by Release 2 and are not planned; they are listed so that "not implemented" is not
read as "forgotten".

| Item | Manual | Why not in the profile |
|---|---|---|
| `ERETNC`, `MFHC0`/`MTHC0` | MD00086 Vol II-A Rev 6.06, ERETNC p.179-180 ("MIPS32 Release 5"), MFHC0 p.270, MTHC0 p.294 ("MIPS32 Release 5") | Release 5 |
| EVA instructions (`LBE`, `LBUE`, `LHE`, `LHUE`, `LWE`, `LLE`, `LWLE`, `LWRE`, `SBE`, `SHE`, `SWE`, `SCE`, `SWLE`, `SWRE`, `CACHEE`, `PREFE`) | e.g. LBE p.212: "Implementation of this instruction is specified by the Config5 EVA field being set to one" | Config5.EVA; Release 3 and later privileged feature |
| `JALX` | MD00086 Vol II-A Rev 6.06, JALX p.201-202; p.31: required "if and only if ISA mode-switching is possible" | Only with microMIPS or MIPS16e |
| MIPS64 instructions (`DDIV`, `DDIVU`, ...) | MD00086 Vol II-A Rev 6.06, DDIV p.161, DDIVU p.162 | 32-bit processor |
| Release 6 instructions and encodings (`BALC`, `BC`, `AUI`, `ALUIPC`, `LSA`, `ALIGN`, `BITSWAP`, `MUL/MUH`, `DIV/MOD`, `CMP.cond.fmt`, `MADDF/MSUBF`, `SEL.fmt`, `SELEQZ`, `CRC32*`, `LLWP`, `SIGRIE`, `GINVI`, `DVP`/`EVP`, ...) | MD00086 Vol II-A Rev 6.06, e.g. BALC p.52, LSA p.232, ALIGN p.39-41, LLWP p.228-229, SIGRIE p.375 | Release 6 removes delay slots, HI/LO and the branch-likely and unaligned instructions that this model implements; it is a different architecture |
| DSP, MSA, MT, VZ, SmartMIPS, MDMX, microMIPS, MIPS16e ASEs and modules | MD00086 Vol II-A Rev 6.06 p.30 ("Supported Modules/ASEs are optional and may be subsetted out") | Optional |

Permanently out of scope: MIPS64, DSP, MSA, microMIPS, MIPS16e, Release 6.

## 3. Closed since the previous version of this document

The previous version of this file (written when 76 instruction variants were modeled and only about 16
had proofs) listed as missing, and the model now has (each with a constructor, decode/encode round trip,
step arm and a `_spec_raw` theorem; see `docs/TRACE.md`):

- Register-indirect jumps `jr`, `jalr` (and `jr.hb`/`jalr.hb` as their own constructors: hint `10000`; hint 0 is `jr`/`jalr`, any other hint is Reserved Instruction); `b`/`bal`
  assembler idioms.
- Zero-comparison branches `bltz`, `bgez`, `bltzal`, `bgezal` and the eight branch-likely instructions.
- Variable shifts, `rotr`/`rotrv`, `ext`/`ins`, `seb`/`seh`/`wsbh`, `clo`/`clz`, `movn`/`movz`.
- `mul`, `madd`/`maddu`/`msub`/`msubu`, `mthi`/`mtlo`.
- `lwl`/`lwr`/`swl`/`swr`, `ll`/`sc` (including the address match), `sb`, `sync`/`synci`, `pref`.
- The immediate trap family `teqi` ... `tltiu`.
- Double precision (`.d` arithmetic, `ldc1`/`sdc1`, conversions), all sixteen compare predicates with
  eight condition codes, `round/trunc/ceil/floor.w.fmt`, `cfc1`/`ctc1`/FCSR with rounding modes, flags,
  enables and the Floating Point exception, `mfhc1`/`mthc1`, `movf`/`movt` and the FP conditional moves,
  `bc1fl`/`bc1tl`, indexed loads/stores `lwxc1`/`ldxc1`/`swxc1`/`sdxc1`, `prefx`, `madd.fmt` family,
  `recip`/`rsqrt`. The previous version's remark "Single-Precision Only" is obsolete.
- Coprocessor 0 access and exception model: `mfc0`/`mtc0` with `sel`, `di`/`ei`, `eret`, `wait`, `rdpgpr`/`wrpgpr`, the
  exception-entry sequence (EPC, `Cause.BD`, `EXL`, vectors, `BadVAddr`, `ErrorEPC`), Reserved Instruction,
  Address Error, Overflow, Trap, Breakpoint, System Call and Coprocessor Unusable as architectural
  exceptions rather than halts.
- Operating modes (wave 3): Kernel Mode and User Mode (`Status.UM`, `EXL`, `ERL`; MD00090 Vol III
  Rev 6.02 ch.3, p.21-23), `Status.CU0`, and Coprocessor Unusable (`Cause.CE = 0`) for every CP0
  instruction and every undecodable COP0/CACHE word executed outside Kernel Mode with `CU0 = 0`
  (§6.2.22, p.100). Exception entry enters Kernel Mode; `eret` returns to User Mode.
- The Reset exception and the reset state (wave 3): `resetException`, `resetState` (`pc =
  0xBFC0_0000`, `Status.BEV = ERL = 1`, `Cause.DC = 0`, `EBase`, `Config.K0 = 2`, `ErrorEPC`;
  §6.2.5, p.89-90); the hosted start state is reset followed by a named boot convention, and
  `MipsRun --reset` starts at the reset vector.
- Timer and hardware registers (wave 5): `Count`, `Compare`, `Cause.TI`/`DC`/`IP7` (`Count` + 1 per
  step unless `DC = 1`; `Count = Compare` sets `TI`; a `Compare` write clears it; MD00090 Vol III Rev 6.02
  §9.27 p.183, §9.30 p.187, Table 9.52 p.209-211), `HWREna` (§9.23, p.175) and `rdhwr` (MD00086 Vol II-A
  Rev 6.06, p.332-334: registers 0-3; Reserved Instruction otherwise).
- Interrupts and shadow-set registers (wave 6): interrupt compatibility mode (request = `Cause.IP & Status.IM`,
  taken when `IE = 1`, `EXL = ERL = 0`, before the next instruction; `ExcCode` 0; vector offset `0x180`/`0x200`
  by `Cause.IV`; MD00090 Vol III Rev 6.02 §6.1 p.71-73, §6.2.26 p.102), software, timer and hardware-line
  requests (the lines are inputs the environment holds deasserted), `wait` as standby until an interrupt
  request (MD00086 Vol II-A Rev 6.06, WAIT, p.442-443), `IntCtl` (`IPTI = 7`, `VS = 0`), `SRSCtl` (`HSS = 0`),
  `rdpgpr`/`wrpgpr` on shadow set 0 (p.335, p.444). SPEC-NOTES §9 items 23, 29.
- Proofs: every constructor has a spec theorem, `decode (encode i) = some i` is proved for all constructors,
  and `step`/`run` preserve the zero register and register-file sizes (README, "What is proved, what is
  tested, what is trusted").
