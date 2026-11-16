# Manual-compliance matrix (Release 6)

The model targets MIPS32 Release 6 (`CLAUDE.md`, "Target profile"; code commit in `SYNC`). Every claim here was looked up with
`manuals/mipsdoc.py` and cites document + revision + section/instruction + PRINTED page. `tools/compliance.py check` verifies that
section A lists every Vol III chapter 9 register section (9.4-9.70) once, and that `R6-COVERAGE.md` lists every Vol II-A list entry
(263) once with its class counts. The model's CP0 register file is the table `cp0Layout` in `Semantics/Exec/Cp0.lean`; a register
not in the table reads 0 and ignores writes ("Release 6: Reading a reserved register or a register that is not implemented for the
current core configuration returns 0", MD00086 Vol II-A Rev 6.06, MFC0, p.266; MTC0, p.290).

## A. CP0 registers (Vol III chapter 9)

"Compliance Level" is the text of the register's own section. Pins and choices for the implemented registers: `SPEC-NOTES.md`.

| ID | Register | Compliance Level (manual) | Model |
|---|---|---|---|
| A9.4 | 9.4 Index Register | "Required for TLB-based MMUs; Optional otherwise." (Vol III Rev 6.02 §9.4, p.119) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.5 | 9.5 VPControl | "Required. if Release 6 Virtual Processor based Multi-threading supported ( i.e., Config5VP=1)." (Vol III Rev 6.02 §9.5, p.121) | absent: VP/MT module (Config5.VP=0) |
| A9.6 | 9.6 Random Register | "Required for TLB-based MMUs; Optional otherwise. Pre-Release 6 only; deprecated in Release 6." (Vol III Rev 6.02 §9.6, p.123) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.7 | 9.7 EntryLo0, EntryLo1 | "EntryLo0 is Required for a TLB-based MMU; Optional otherwise." (Vol III Rev 6.02 §9.7, p.125) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.8 | 9.8 Global Number Register | "Optional Release 6" (Vol III Rev 6.02 §9.8, p.135) | absent: Release 6 Global Number (MT/VP modules) |
| A9.9 | 9.9 Context Register | "Required for TLB-based MMUs; Optional otherwise." (Vol III Rev 6.02 §9.9, p.137) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.10 | 9.10 ContextConfig Register | "Optional." (Vol III Rev 6.02 §9.10, p.141) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.11 | 9.11 UserLocal Register | "Pre-Release 6: Recommended. Release 6: Required" (Vol III Rev 6.02 §9.11, p.143) | implemented: UserLocal (4,2); RDHWR 29 |
| A9.12 | 9.12 Debug ContextID | "Reserved Pre-Release 6; Optional Release 6." (Vol III Rev 6.02 §9.12, p.145) | absent: Debug ContextID: EJTAG/EVA, absent |
| A9.13 | 9.13 PageMask Register | "Required for TLB-based MMUs; Optional otherwise." (Vol III Rev 6.02 §9.13, p.147) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.14 | 9.14 PageGrain Register | "Required for implementations of Release 2 (and subsequent releases) of the Architecture that include TLB-based MMUs and support 1 kB pages, the XI/RI TLB protection bits, multiple types of Machine Check exceptions; Required for SmartMIPS™ ASE; Required for XPA (Config3LPA=1); Optional otherwise." (Vol III Rev 6.02 §9.14, p.151) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.15 | 9.15 SegCtl0 | "(not in the extracted text; page image)" (Vol III Rev 6.02 §9.15, p.157) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.16 | 9.16 SegCtl1 | "(not in the extracted text; page image)" (Vol III Rev 6.02 §9.16, p.157) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.17 | 9.17 SegCtl2 | "Required for programmable memory segmentation; Optional otherwise." (Vol III Rev 6.02 §9.17, p.157) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.18 | 9.18 PWBase Register | "Required for the hardware page walker feature." (Vol III Rev 6.02 §9.18, p.161) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.19 | 9.19 PWField Register | "Required for the hardware page walker feature." (Vol III Rev 6.02 §9.19, p.161) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.20 | 9.20 PWSize Register | "Required for the hardware page walk feature." (Vol III Rev 6.02 §9.20, p.164) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.21 | 9.21 Wired Register | "(not in the extracted text; page image)" (Vol III Rev 6.02 §9.21, p.169) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.22 | 9.22 PWCtl Register | "Required for the hardware page walker feature." (Vol III Rev 6.02 §9.22, p.171) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.23 | 9.23 HWREna Register | "Required (Release 2)." (Vol III Rev 6.02 §9.23, p.175) | implemented: HWREna (7,0) |
| A9.24 | 9.24 BadVAddr Register | "Required." (Vol III Rev 6.02 §9.24, p.177) | implemented: BadVAddr (8,0) |
| A9.25 | 9.25 BadInstr Register | "Pre-Release 6 - Optional Release 6 - Required" (Vol III Rev 6.02 §9.25, p.179) | implemented: BadInstr (8,1); 0 when no instruction word was fetched (pin) |
| A9.26 | 9.26 BadInstrP Register | "Pre-Release 6 - Optional Release 6 - Required" (Vol III Rev 6.02 §9.26, p.181) | implemented: BadInstrP (8,2); 0 outside a delay/forbidden slot (pin) |
| A9.27 | 9.27 Count Register | "Required." (Vol III Rev 6.02 §9.27, p.183) | implemented: Count (9,0); increment 1 per instruction time (pin) |
| A9.28 | 9.28 Reserved for Implementations | "Implementation-dependent." (Vol III Rev 6.02 §9.28, p.183) | absent: reserved for implementations: none used |
| A9.29 | 9.29 EntryHi Register | "Required for TLB-based MMU; Optional otherwise." (Vol III Rev 6.02 §9.29, p.185) | absent (Fixed Mapping MMU, `Config.MT = 3`): reads 0, writes ignored; Vol III A.1.3 p.317 |
| A9.30 | 9.30 Compare Register | "Required." (Vol III Rev 6.02 §9.30, p.187) | implemented: Compare (11,0) |
| A9.31 | 9.31 Reserved for Implementations | "Implementation-dependent." (Vol III Rev 6.02 §9.31, p.187) | absent: reserved for implementations: none used |
| A9.32 | 9.32 Status Register | "Required." (Vol III Rev 6.02 §9.32, p.189) | implemented: Status (12,0): CU3..CU1, RW (bit 28), FR reads 1, no RE |
| A9.33 | 9.33 IntCtl Register | "Required (Release 2)." (Vol III Rev 6.02 §9.33, p.199) | implemented: IntCtl (12,1) = 0xE0000000 (IPTI=7, VS=0) |
| A9.34 | 9.34 SRSCtl Register | "Required (Release 2)." (Vol III Rev 6.02 §9.34, p.203) | implemented: SRSCtl (12,2) = 0 (HSS=PSS=0) |
| A9.35 | 9.35 SRSMap Register | "Required in Release 2 (and subsequent releases) of the Architecture if Additional Shadow Sets and Vectored Interrupt Mode are Implemented" (Vol III Rev 6.02 §9.35, p.207) | absent: SRSMap: only with Additional Shadow Sets and Vectored Interrupt Mode (HSS=0, VInt=0) |
| A9.36 | 9.36 Cause Register | "Required." (Vol III Rev 6.02 §9.36, p.209) | implemented: Cause (13,0) |
| A9.37 | 9.37 NestedExc | "Optional." (Vol III Rev 6.02 §9.37, p.215) | absent: NestedExc: Nested Fault feature absent |
| A9.38 | 9.38 Exception Program Counter | "Required." (Vol III Rev 6.02 §9.38, p.217) | implemented: EPC (14,0) |
| A9.39 | 9.39 Nested Exception Program Counter | "Optional." (Vol III Rev 6.02 §9.39, p.219) | absent: NestedEPC: Nested Fault feature absent |
| A9.40 | 9.40 Processor Identification | "Required." (Vol III Rev 6.02 §9.40, p.221) | implemented: PRId (15,0) constant |
| A9.41 | 9.41 EBase Register | "Required (Release 2)." (Vol III Rev 6.02 §9.41, p.223) | implemented: EBase (15,1) |
| A9.42 | 9.42 CDMMBase Register | "Optional." (Vol III Rev 6.02 §9.42, p.227) | absent: CDMM absent |
| A9.43 | 9.43 CMGCRBase Register | "Optional." (Vol III Rev 6.02 §9.43, p.229) | absent: CM/GCR absent |
| A9.44 | 9.44 BEVVA Register | "Required. if Release 5 Enhanced Virtual Addressing is supported ( i.e., Config5EVA=1)." (Vol III Rev 6.02 §9.44, p.231) | absent: BEVVA: only with EVA (absent) |
| A9.45 | 9.45 Configuration Register | "Required." (Vol III Rev 6.02 §9.45, p.233) | implemented: Config (16,0): BE=0, AR=2, MT=3 |
| A9.46 | 9.46 Configuration Register 1 | "Required." (Vol III Rev 6.02 §9.46, p.237) | implemented: Config1 (16,1): FP=1, no TLB/caches |
| A9.47 | 9.47 Configuration Register 2 | "Required if a level 2 or level 3 cache is implemented, or if the Config3 register is required; Optional otherwise. In Release 6, presence of Config2 is dependent on Config5L2C." (Vol III Rev 6.02 §9.47, p.241) | implemented: Config2 (16,2) = 0x80000000 |
| A9.48 | 9.48 Configuration Register 3 | "Required if any optional feature described by this register is implemented: Release 2 of the Architecture, the SmartMIPS™ ASE, or trace logic; Optional otherwise." (Vol III Rev 6.02 §9.48, p.245) | implemented: Config3 (16,3): BP, BI, ULRI, RXI |
| A9.49 | 9.49 Configuration Register 4 | "Required if any optional feature described by this register is implemented: Release 2 of the Architecture; Optional otherwise." (Vol III Rev 6.02 §9.49, p.253) | implemented: Config4 (16,4): KScrExist=0xFC, IE=0 |
| A9.50 | 9.50 Configuration Register 5 | "Required if any optional feature described by this register is implemented: Release 3 of the Architecture; Optional otherwise." (Vol III Rev 6.02 §9.50, p.259) | implemented: Config5 (16,5): XNP=1, LLB=1, DEC=0, SBRI R/W |
| A9.51 | 9.51 Reserved for Implementations | "Implementation Dependent." (Vol III Rev 6.02 §9.51, p.267) | absent: reserved for implementations: none used |
| A9.52 | 9.52 Load Linked Address | "Optional prior to Release 5. Required in Release 5 if Config5LLB=1. Required in Release 6." (Vol III Rev 6.02 §9.52, p.269) | implemented: LLAddr (17,0): LLB only, PAddr reads 0 (pin) |
| A9.53 | 9.53 Memory Accessibility Attribute Register | "Optional (Release 5)" (Vol III Rev 6.02 §9.53, p.271) | absent: MAAR: optional, absent |
| A9.54 | 9.54 Memory Accessibility Attribute Register Index | "Optional (Release 5)" (Vol III Rev 6.02 §9.54, p.277) | absent: MAARI: optional, absent |
| A9.55 | 9.55 WatchLo Register | "Optional." (Vol III Rev 6.02 §9.55, p.279) | absent: Watch: Config1.WR=0 |
| A9.56 | 9.56 WatchHi Register | "Optional." (Vol III Rev 6.02 §9.56, p.281) | absent: Watch: Config1.WR=0 |
| A9.57 | 9.57 Reserved for Implementations | "Implementation Dependent." (Vol III Rev 6.02 §9.57, p.283) | absent: reserved for implementations: none used |
| A9.58 | 9.58 Debug Register | "Optional." (Vol III Rev 6.02 §9.58, p.285) | absent: EJTAG absent |
| A9.59 | 9.59 Debug2 Register | "Optional." (Vol III Rev 6.02 §9.59, p.287) | absent: EJTAG absent |
| A9.60 | 9.60 DEPC Register | "Optional." (Vol III Rev 6.02 §9.60, p.289) | absent: EJTAG absent |
| A9.61 | 9.61 Performance Counter Register | "Recommended." (Vol III Rev 6.02 §9.61, p.291) | absent: Performance counters: Config1.PC=0; RDHWR 4 is a Reserved Instruction |
| A9.62 | 9.62 ErrCtl Register | "Optional." (Vol III Rev 6.02 §9.62, p.295) | absent: ErrCtl: no caches/parity |
| A9.63 | 9.63 CacheErr Register | "Optional." (Vol III Rev 6.02 §9.63, p.297) | absent: CacheErr: no caches/parity |
| A9.64 | 9.64 TagLo Register | "Required if a cache is implemented; Optional otherwise." (Vol III Rev 6.02 §9.64, p.299) | absent: TagLo: no caches |
| A9.65 | 9.65 DataLo Register | "Optional." (Vol III Rev 6.02 §9.65, p.301) | absent: DataLo: no caches |
| A9.66 | 9.66 TagHi Register | "Required if a cache is implemented; Optional otherwise." (Vol III Rev 6.02 §9.66, p.303) | absent: TagHi: no caches |
| A9.67 | 9.67 DataHi Register | "Optional." (Vol III Rev 6.02 §9.67, p.305) | absent: DataHi: no caches |
| A9.68 | 9.68 ErrorEPC | "Required." (Vol III Rev 6.02 §9.68, p.307) | implemented: ErrorEPC (30,0) |
| A9.69 | 9.69 DESAVE Register | "Optional." (Vol III Rev 6.02 §9.69, p.309) | absent: DESAVE: EJTAG absent |
| A9.70 | 9.70 KScratchn Registers | "Pre-Release 6 - Optional, KScratch1 and KScratch2 at selects 2, 3 are recommended. Release 6 - Required." (Vol III Rev 6.02 §9.70, p.311) | implemented: KScratch1..6 (31,2..7) |

Counts: 67 register sections: 23 implemented, 16 absent because of the Fixed Mapping MMU (TLB, page walker, segmentation), 28 absent
because the module or optional feature is outside the profile.

## B. Instructions (Vol II-A)

All 263 list entries are classified in [`R6-COVERAGE.md`](R6-COVERAGE.md): (a) implemented 137, (b) removed in Release 6 77,
(c) optional module or feature absent 36, (d) TLB instruction, Reserved Instruction under the Fixed Mapping MMU 6, (e) assembler
idiom 7, (f) open gap 0. [`MIPS-COVERAGE-GAPS.md`](MIPS-COVERAGE-GAPS.md) states the open gaps (none).

## C. Operating modes, exceptions, interrupts, FPU control registers

Kernel/User Mode and the Fixed Mapping MMU, exception entry, interrupts, the timer and the FPU control registers (FIR, FCSR with
FCCR/FEXR/FENR removed, `Status.FR = 1`, NAN2008, ABS2008) are specified in `Semantics/Manual/` and proved to be refined by `step`
(`docs/OVERVIEW.md`, `docs/MANUAL-SPEC.md`); their pins are in `SPEC-NOTES.md`.
