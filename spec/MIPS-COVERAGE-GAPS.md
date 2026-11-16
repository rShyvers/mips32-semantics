# What the model does not cover (Release 6)

**Open gaps: 0.** All 263 instruction pages of MD00086 Vol II-A Rev 6.06 are classified in [`R6-COVERAGE.md`](R6-COVERAGE.md)
(checked by `tools/compliance.py check`):

| class | pages |
|---|---:|
| (a) implemented (203 `Instruction` constructors) | 137 |
| (b) removed in Release 6 (the word does not decode: Reserved Instruction) | 77 |
| (c) optional module or feature absent | 36 |
| (d) TLB instruction, Reserved Instruction under the Fixed Mapping MMU | 6 |
| (e) assembler idiom of an implemented instruction | 7 |
| (f) open gap | 0 |

What follows is what the profile leaves out on purpose. Each item is a choice the manual permits, not a gap; the pins are in
[`SPEC-NOTES.md`](SPEC-NOTES.md). The profile is in `CLAUDE.md` ("Target profile"). The wave R6-7 audit closed the only two gaps it
found: DVP (p.172-173) and EVP (p.181-182) were Reserved Instruction and are now no-ops with `Config5.VP = 0`
(MD00086 Vol II-A Rev 6.06; MD00090 Vol III Rev 6.02 Table 9.69, p.263).

## 1. Left out by the profile

- **Other releases.** Only Release 6 is modeled. Release 5, 3, 2 and 1 will be added backwards as profiles
  (`Release`/`Profile`, per-release decoder tables and CP0 layout table: `docs/DESIGN.md`). The Release 2 model is at tag `mips32r2-final`.
- **Big-endian.** `Config5.DEC = 0`, `Config.BE = 0`: little-endian only, which Release 6 requires every implementation to support
  (MD00090 Vol III Rev 6.02, Config5, p.261). The byte order sits behind one constant.
- **Optional modules:** MSA, microMIPS, VZ, MT, DSP, EVA, XPA, MCU, CRC, GINV, VP, EJTAG (their `Config` bits read 0). Their
  instruction pages are class (c) below.
- **MMU.** Fixed Mapping MMU (`Config.MT = 3`, MD00082 Vol I-A Rev 6.01 §2.4.2, p.32): TLB registers read 0 and ignore writes, and
  TLBP, TLBR, TLBWI, TLBWR, TLBINV, TLBINVF raise Reserved Instruction (MD00090 Vol III Rev 6.02 A.1.3, p.317; MD00086 Vol II-A
  Rev 6.06 TLBINV p.423). No Supervisor Mode.
- **Caches.** None; CACHE and the prefetches are no-ops (CACHE p.119; D8 in `SPEC-NOTES.md`).
- **Misaligned loads and stores** raise Address Error (MD00082 Vol I-A Rev 6.01 App. B.2, p.128); LL/SC always do.
- **FPU.** 64-bit FPU only (`Status.FR = 1`, read-only); paired-single, 3D and the FCCR/FEXR/FENR registers are removed in Release 6.
- **CP0 registers** not in the table `cp0Layout` (`Semantics/Exec/Cp0.lean`): 44 of the 67 sections of Vol III chapter 9 (see
  [`COMPLIANCE.md`](COMPLIANCE.md) section A). Coprocessor 2 does not exist: its encodings raise Coprocessor Unusable with `CE = 2`.
- **Hardware interrupt lines and the platform** are the environment (`hwInt`), not the architecture.

## 2. Class (c): optional module or feature absent

| Mnemonic | Title | Behaviour in the model | Citation |
|---|---|---|---|
| BC2EQZ BC2NEZ | Branch if Coprocessor 2 Condition (Register) Equal/Not Equal to Zero | model: CpU, CE=2 (isCop2Word; Manual.Undecodable InCop2Space) - correct per 6.2.22; QEMU raises RI (declared deviation, r6gap_absent_modules) | MD00086 Vol II-A Rev 6.06 BC2EQZ BC2NEZ p.64-65; no coprocessor 2: Config1.C2 = 0 (MD00090 Vol III Rev 6.02 Table 9.65 p.239); MD00090 Vol III Rev 6.02 6.2.22 p.100: COP2/LWC2/SWC2/LDC2/SDC2 "and the CU2 bit ... was a zero" -> Coprocessor Unusable, CE = unit 2; CU2 reads 0 (MD00090 Vol III Rev 2.50 Table 8-19 p.79, R6 Table 9.47 p.190 image-only) |
| CACHEE | Perform Cache Operation EVA | model: RI (word does not decode) | MD00086 Vol II-A Rev 6.06 CACHEE p.121-126; Config5.EVA = 0 (MD00090 Vol III Rev 6.02 Table 9.69 p.259-264; DECISIONS D5) |
| CFC2 | Move Control Word From Coprocessor 2 | model: CpU, CE=2 (isCop2Word; Manual.Undecodable InCop2Space) - correct per 6.2.22; QEMU raises RI (declared deviation, r6gap_absent_modules) | MD00086 Vol II-A Rev 6.06 CFC2 p.131; no coprocessor 2: Config1.C2 = 0 (MD00090 Vol III Rev 6.02 Table 9.65 p.239); MD00090 Vol III Rev 6.02 6.2.22 p.100: COP2/LWC2/SWC2/LDC2/SDC2 "and the CU2 bit ... was a zero" -> Coprocessor Unusable, CE = unit 2; CU2 reads 0 (MD00090 Vol III Rev 2.50 Table 8-19 p.79, R6 Table 9.47 p.190 image-only) |
| COP2 | Coprocessor Operation to Coprocessor 2 | model: CpU, CE=2 (isCop2Word; Manual.Undecodable InCop2Space) - correct per 6.2.22; QEMU raises RI (declared deviation, r6gap_absent_modules) | MD00086 Vol II-A Rev 6.06 COP2 p.141-142; no coprocessor 2: Config1.C2 = 0 (MD00090 Vol III Rev 6.02 Table 9.65 p.239); MD00090 Vol III Rev 6.02 6.2.22 p.100: COP2/LWC2/SWC2/LDC2/SDC2 "and the CU2 bit ... was a zero" -> Coprocessor Unusable, CE = unit 2; CU2 reads 0 (MD00090 Vol III Rev 2.50 Table 8-19 p.79, R6 Table 9.47 p.190 image-only) |
| CRC32B, CRC32H, CRC32W | Generate CRC with reversed polynomial 0xEDB88320 | model: RI | MD00086 Vol II-A Rev 6.06 CRC32B, CRC32H, CRC32W p.143-145; CRC module absent (Config5.CRCP = 0, D10) |
| CRC32CB, CRC32CH, CRC32CW | Generate CRC with reversed polynomial 0x82F63B78 | model: RI | MD00086 Vol II-A Rev 6.06 CRC32CB, CRC32CH, CRC32CW p.146-148; CRC module absent (Config5.CRCP = 0, D10) |
| CTC2 | Move Control Word to Coprocessor 2 | model: CpU, CE=2 (isCop2Word; Manual.Undecodable InCop2Space) - correct per 6.2.22; QEMU raises RI (declared deviation, r6gap_absent_modules) | MD00086 Vol II-A Rev 6.06 CTC2 p.152; no coprocessor 2: Config1.C2 = 0 (MD00090 Vol III Rev 6.02 Table 9.65 p.239); MD00090 Vol III Rev 6.02 6.2.22 p.100: COP2/LWC2/SWC2/LDC2/SDC2 "and the CU2 bit ... was a zero" -> Coprocessor Unusable, CE = unit 2; CU2 reads 0 (MD00090 Vol III Rev 2.50 Table 8-19 p.79, R6 Table 9.47 p.190 image-only) |
| DERET | Debug Exception Return | model: RI (SDBBP: SPECIAL funct 0x0e; DERET: COP0 space, CpU CE=0 outside Kernel Mode) | MD00086 Vol II-A Rev 6.06 DERET p.163; "If EJTAG is not implemented, the EJTAG instructions (SDBBP and DERET) can be subsetted out" (MD00082 Vol I-A Rev 6.01 2.4.1 p.31; D5, D7) |
| GINVI | Global Invalidate Instruction Cache | model: RI | MD00086 Vol II-A Rev 6.06 GINVI p.187-188; GINV module absent (Config5.GI = 0, D10; SYNC p.407 "Release 6 (with Config5GI =10/11)") |
| GINVT | Global Invalidate TLB | model: RI | MD00086 Vol II-A Rev 6.06 GINVT p.189-192; GINV module absent (Config5.GI = 0, D10; SYNC p.407 "Release 6 (with Config5GI =10/11)") |
| LBE | Load Byte EVA | model: RI (word does not decode) | MD00086 Vol II-A Rev 6.06 LBE p.212; Config5.EVA = 0 (MD00090 Vol III Rev 6.02 Table 9.69 p.259-264; DECISIONS D5) |
| LBUE | Load Byte Unsigned EVA | model: RI (word does not decode) | MD00086 Vol II-A Rev 6.06 LBUE p.214; Config5.EVA = 0 (MD00090 Vol III Rev 6.02 Table 9.69 p.259-264; DECISIONS D5) |
| LDC2 | Load Doubleword to Coprocessor 2 | model: CpU, CE=2 (isCop2Word; Manual.Undecodable InCop2Space) - correct per 6.2.22; QEMU raises RI (declared deviation, r6gap_absent_modules) | MD00086 Vol II-A Rev 6.06 LDC2 p.216-217; no coprocessor 2: Config1.C2 = 0 (MD00090 Vol III Rev 6.02 Table 9.65 p.239); MD00090 Vol III Rev 6.02 6.2.22 p.100: COP2/LWC2/SWC2/LDC2/SDC2 "and the CU2 bit ... was a zero" -> Coprocessor Unusable, CE = unit 2; CU2 reads 0 (MD00090 Vol III Rev 2.50 Table 8-19 p.79, R6 Table 9.47 p.190 image-only) |
| LHE | Load Halfword EVA | model: RI (word does not decode) | MD00086 Vol II-A Rev 6.06 LHE p.220; Config5.EVA = 0 (MD00090 Vol III Rev 6.02 Table 9.69 p.259-264; DECISIONS D5) |
| LHUE | Load Halfword Unsigned EVA | model: RI (word does not decode) | MD00086 Vol II-A Rev 6.06 LHUE p.222; Config5.EVA = 0 (MD00090 Vol III Rev 6.02 Table 9.69 p.259-264; DECISIONS D5) |
| LLE | Load Linked Word EVA | model: RI (word does not decode) | MD00086 Vol II-A Rev 6.06 LLE p.225-227; Config5.EVA = 0 (MD00090 Vol III Rev 6.02 Table 9.69 p.259-264; DECISIONS D5) |
| LLWP | Load Linked Word Paired | model: RI (does not decode; Manual: LL/SC bit 6 UnpredictableEncoding -> oracle RI) | MD00086 Vol II-A Rev 6.06 LLWP p.228-229; "only present if Config5XNP=0" (LLWP p.228, SCWP p.355); Config5.XNP = 1 "LLX/SCX family of instructions is not present" (MD00090 Vol III Rev 6.02 Table 9.40 p.176, Table 9.69 p.261; D13) |
| LLWPE | Load Linked Word Paired EVA | model: RI | MD00086 Vol II-A Rev 6.06 LLWPE p.230-231; "only present if Config5XNP=0 and Config5EVA=1" (LLWPE p.230, SCWPE p.359) |
| LWC2 | Load Word to Coprocessor 2 | model: CpU, CE=2 (isCop2Word; Manual.Undecodable InCop2Space) - correct per 6.2.22; QEMU raises RI (declared deviation, r6gap_absent_modules) | MD00086 Vol II-A Rev 6.06 LWC2 p.237-238; no coprocessor 2: Config1.C2 = 0 (MD00090 Vol III Rev 6.02 Table 9.65 p.239); MD00090 Vol III Rev 6.02 6.2.22 p.100: COP2/LWC2/SWC2/LDC2/SDC2 "and the CU2 bit ... was a zero" -> Coprocessor Unusable, CE = unit 2; CU2 reads 0 (MD00090 Vol III Rev 2.50 Table 8-19 p.79, R6 Table 9.47 p.190 image-only) |
| LWE | Load Word EVA | model: RI (word does not decode) | MD00086 Vol II-A Rev 6.06 LWE p.239-240; Config5.EVA = 0 (MD00090 Vol III Rev 6.02 Table 9.69 p.259-264; DECISIONS D5) |
| MFC2 | Move Word From Coprocessor 2 | model: CpU, CE=2 (isCop2Word; Manual.Undecodable InCop2Space) - correct per 6.2.22; QEMU raises RI (declared deviation, r6gap_absent_modules) | MD00086 Vol II-A Rev 6.06 MFC2 p.268-269; no coprocessor 2: Config1.C2 = 0 (MD00090 Vol III Rev 6.02 Table 9.65 p.239); MD00090 Vol III Rev 6.02 6.2.22 p.100: COP2/LWC2/SWC2/LDC2/SDC2 "and the CU2 bit ... was a zero" -> Coprocessor Unusable, CE = unit 2; CU2 reads 0 (MD00090 Vol III Rev 2.50 Table 8-19 p.79, R6 Table 9.47 p.190 image-only) |
| MFHC0 | Move from High Coprocessor 0 | model: RI in Kernel Mode, CpU CE=0 outside (COP0 space, Table A.1 p.451 priority) | MD00086 Vol II-A Rev 6.06 MFHC0 p.270; "if Config5MVH = 0 then SignalException(ReservedInstruction)" (MFHC0 p.270, MTHC0 p.294); Config5.MVH = 0 (MD00090 Vol III Rev 6.02 Table 9.69 p.263) |
| MFHC2 | Move Word From High Half of Coprocessor 2 Register | model: CpU, CE=2 (isCop2Word; Manual.Undecodable InCop2Space) - correct per 6.2.22; QEMU raises RI (declared deviation, r6gap_absent_modules) | MD00086 Vol II-A Rev 6.06 MFHC2 p.272; no coprocessor 2: Config1.C2 = 0 (MD00090 Vol III Rev 6.02 Table 9.65 p.239); MD00090 Vol III Rev 6.02 6.2.22 p.100: COP2/LWC2/SWC2/LDC2/SDC2 "and the CU2 bit ... was a zero" -> Coprocessor Unusable, CE = unit 2; CU2 reads 0 (MD00090 Vol III Rev 2.50 Table 8-19 p.79, R6 Table 9.47 p.190 image-only) |
| MTC2 | Move Word to Coprocessor 2 | model: CpU, CE=2 (isCop2Word; Manual.Undecodable InCop2Space) - correct per 6.2.22; QEMU raises RI (declared deviation, r6gap_absent_modules) | MD00086 Vol II-A Rev 6.06 MTC2 p.293; no coprocessor 2: Config1.C2 = 0 (MD00090 Vol III Rev 6.02 Table 9.65 p.239); MD00090 Vol III Rev 6.02 6.2.22 p.100: COP2/LWC2/SWC2/LDC2/SDC2 "and the CU2 bit ... was a zero" -> Coprocessor Unusable, CE = unit 2; CU2 reads 0 (MD00090 Vol III Rev 2.50 Table 8-19 p.79, R6 Table 9.47 p.190 image-only) |
| MTHC0 | Move to High Coprocessor 0 | model: RI in Kernel Mode, CpU CE=0 outside (COP0 space, Table A.1 p.451 priority) | MD00086 Vol II-A Rev 6.06 MTHC0 p.294; "if Config5MVH = 0 then SignalException(ReservedInstruction)" (MFHC0 p.270, MTHC0 p.294); Config5.MVH = 0 (MD00090 Vol III Rev 6.02 Table 9.69 p.263) |
| MTHC2 | Move Word to High Half of Coprocessor 2 Register | model: CpU, CE=2 (isCop2Word; Manual.Undecodable InCop2Space) - correct per 6.2.22; QEMU raises RI (declared deviation, r6gap_absent_modules) | MD00086 Vol II-A Rev 6.06 MTHC2 p.296; no coprocessor 2: Config1.C2 = 0 (MD00090 Vol III Rev 6.02 Table 9.65 p.239); MD00090 Vol III Rev 6.02 6.2.22 p.100: COP2/LWC2/SWC2/LDC2/SDC2 "and the CU2 bit ... was a zero" -> Coprocessor Unusable, CE = unit 2; CU2 reads 0 (MD00090 Vol III Rev 2.50 Table 8-19 p.79, R6 Table 9.47 p.190 image-only) |
| PREFE | Prefetch EVA | model: RI (word does not decode) | MD00086 Vol II-A Rev 6.06 PREFE p.325-328; Config5.EVA = 0 (MD00090 Vol III Rev 6.02 Table 9.69 p.259-264; DECISIONS D5) |
| SBE | Store Byte EVA | model: RI (word does not decode) | MD00086 Vol II-A Rev 6.06 SBE p.346; Config5.EVA = 0 (MD00090 Vol III Rev 6.02 Table 9.69 p.259-264; DECISIONS D5) |
| SCE | Store Conditional Word EVA | model: RI (word does not decode) | MD00086 Vol II-A Rev 6.06 SCE p.351-353; Config5.EVA = 0 (MD00090 Vol III Rev 6.02 Table 9.69 p.259-264; DECISIONS D5) |
| SCWP | Store Conditional Word Paired | model: RI (does not decode; Manual: LL/SC bit 6 UnpredictableEncoding -> oracle RI) | MD00086 Vol II-A Rev 6.06 SCWP p.354-357; "only present if Config5XNP=0" (LLWP p.228, SCWP p.355); Config5.XNP = 1 "LLX/SCX family of instructions is not present" (MD00090 Vol III Rev 6.02 Table 9.40 p.176, Table 9.69 p.261; D13) |
| SCWPE | Store Conditional Word Paired EVA | model: RI | MD00086 Vol II-A Rev 6.06 SCWPE p.358-360; "only present if Config5XNP=0 and Config5EVA=1" (LLWPE p.230, SCWPE p.359) |
| SDBBP | Software Debug Breakpoint | model: RI (SDBBP: SPECIAL funct 0x0e; DERET: COP0 space, CpU CE=0 outside Kernel Mode) | MD00086 Vol II-A Rev 6.06 SDBBP p.361; "If EJTAG is not implemented, the EJTAG instructions (SDBBP and DERET) can be subsetted out" (MD00082 Vol I-A Rev 6.01 2.4.1 p.31; D5, D7) |
| SDC2 | Store Doubleword from Coprocessor 2 | model: CpU, CE=2 (isCop2Word; Manual.Undecodable InCop2Space) - correct per 6.2.22; QEMU raises RI (declared deviation, r6gap_absent_modules) | MD00086 Vol II-A Rev 6.06 SDC2 p.363; no coprocessor 2: Config1.C2 = 0 (MD00090 Vol III Rev 6.02 Table 9.65 p.239); MD00090 Vol III Rev 6.02 6.2.22 p.100: COP2/LWC2/SWC2/LDC2/SDC2 "and the CU2 bit ... was a zero" -> Coprocessor Unusable, CE = unit 2; CU2 reads 0 (MD00090 Vol III Rev 2.50 Table 8-19 p.79, R6 Table 9.47 p.190 image-only) |
| SHE | Store Halfword EVA | model: RI (word does not decode) | MD00086 Vol II-A Rev 6.06 SHE p.374; Config5.EVA = 0 (MD00090 Vol III Rev 6.02 Table 9.69 p.259-264; DECISIONS D5) |
| SWC2 | Store Word from Coprocessor 2 | model: CpU, CE=2 (isCop2Word; Manual.Undecodable InCop2Space) - correct per 6.2.22; QEMU raises RI (declared deviation, r6gap_absent_modules) | MD00086 Vol II-A Rev 6.06 SWC2 p.394-395; no coprocessor 2: Config1.C2 = 0 (MD00090 Vol III Rev 6.02 Table 9.65 p.239); MD00090 Vol III Rev 6.02 6.2.22 p.100: COP2/LWC2/SWC2/LDC2/SDC2 "and the CU2 bit ... was a zero" -> Coprocessor Unusable, CE = unit 2; CU2 reads 0 (MD00090 Vol III Rev 2.50 Table 8-19 p.79, R6 Table 9.47 p.190 image-only) |
| SWE | Store Word EVA | model: RI (word does not decode) | MD00086 Vol II-A Rev 6.06 SWE p.396; Config5.EVA = 0 (MD00090 Vol III Rev 6.02 Table 9.69 p.259-264; DECISIONS D5) |

## 3. Class (d): TLB instructions

| Mnemonic | Title | Behaviour in the model | Citation |
|---|---|---|---|
| TLBINV | TLB Invalidate | RI (COP0 space: CpU CE=0 outside Kernel Mode); word does not decode | MD00086 Vol II-A Rev 6.06 TLBINV p.422-424, p.423: "On processors that include a ... Fixed Mapping (FM) MMU (ConfigMT = 2 or 3), the operation of this instruction causes a Reserved Instruction exception (RI)"; MD00090 Vol III Rev 6.02 A.1.3 p.317 (TLBWR/TLBWI/TLBP/TLBR "must cause a Reserved Instruction Exception"); TLBINV/TLBINVF optional, "indicated by the IE field in Config4" (Config4.IE = 0, D4) |
| TLBINVF | TLB Invalidate Flush | RI (COP0 space: CpU CE=0 outside Kernel Mode); word does not decode | MD00086 Vol II-A Rev 6.06 TLBINVF p.425-426, p.426: "On processors that include a ... Fixed Mapping (FM) MMU (ConfigMT = 2 or 3), the operation of this instruction causes a Reserved Instruction exception (RI)"; MD00090 Vol III Rev 6.02 A.1.3 p.317 (TLBWR/TLBWI/TLBP/TLBR "must cause a Reserved Instruction Exception"); TLBINV/TLBINVF optional, "indicated by the IE field in Config4" (Config4.IE = 0, D4) |
| TLBP | Probe TLB for Matching Entry | RI (COP0 space: CpU CE=0 outside Kernel Mode); word does not decode | MD00086 Vol II-A Rev 6.06 TLBP p.427, p.427: "On processors that include a ... Fixed Mapping (FM) MMU (ConfigMT = 2 or 3), the operation of this instruction causes a Reserved Instruction exception (RI)"; MD00090 Vol III Rev 6.02 A.1.3 p.317 (TLBWR/TLBWI/TLBP/TLBR "must cause a Reserved Instruction Exception") |
| TLBR | Read Indexed TLB Entry | RI (COP0 space: CpU CE=0 outside Kernel Mode); word does not decode | MD00086 Vol II-A Rev 6.06 TLBR p.428-429, p.428: "On processors that include a ... Fixed Mapping (FM) MMU (ConfigMT = 2 or 3), the operation of this instruction causes a Reserved Instruction exception (RI)"; MD00090 Vol III Rev 6.02 A.1.3 p.317 (TLBWR/TLBWI/TLBP/TLBR "must cause a Reserved Instruction Exception") |
| TLBWI | Write Indexed TLB Entry | RI (COP0 space: CpU CE=0 outside Kernel Mode); word does not decode | MD00086 Vol II-A Rev 6.06 TLBWI p.430-431, p.430: "On processors that include a ... Fixed Mapping (FM) MMU (ConfigMT = 2 or 3), the operation of this instruction causes a Reserved Instruction exception (RI)"; MD00090 Vol III Rev 6.02 A.1.3 p.317 (TLBWR/TLBWI/TLBP/TLBR "must cause a Reserved Instruction Exception") |
| TLBWR | Write Random TLB Entry | RI (COP0 space: CpU CE=0 outside Kernel Mode); word does not decode | MD00086 Vol II-A Rev 6.06 TLBWR p.432-433, p.432: "On processors that include a ... Fixed Mapping (FM) MMU (ConfigMT = 2 or 3), the operation of this instruction causes a Reserved Instruction exception (RI)"; MD00090 Vol III Rev 6.02 A.1.3 p.317 (TLBWR/TLBWI/TLBP/TLBR "must cause a Reserved Instruction Exception") |
