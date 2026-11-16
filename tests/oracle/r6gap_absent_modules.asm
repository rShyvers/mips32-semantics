# Encodings of instruction pages outside the profile raise Reserved Instruction in Kernel Mode (ExcCode 10, Cause & mask = 0x28),
# the COP0-space ones Coprocessor Unusable with CE = 0 in User Mode (0x2c), and every COP2 word Coprocessor Unusable with CE = 2
# (0x2000002c). The handler stores Cause & 0x3000007c per exception (res, in order), counts them (s4) and skips the instruction.
# Kernel Mode, Reserved Instruction: DERET (EJTAG absent: MD00082 Vol I-A Rev 6.01 sec 2.4.1 p.31 "If EJTAG is not implemented, the
# EJTAG instructions (SDBBP and DERET) can be subsetted out"; sec 2.4.1 p.30 "an attempt to execute that instruction must cause the
# appropriate exception (typically Reserved Instruction or Coprocessor Unusable)"); MFHC0/MTHC0 (MD00086 Vol II-A Rev 6.06 MFHC0 p.270,
# MTHC0 p.294: "if Config5MVH = 0 then SignalException(ReservedInstruction)"; MD00090 Vol III Rev 6.02 Table 9.69 p.263, MVH = 0);
# the EVA pages LWE p.239, SWE p.396, CACHEE p.121, PREFE p.325 (Config5.EVA = 0); CRC32W p.143; GINVI p.187, GINVT p.189; DDIV p.161
# (MIPS64, "removed in Release 6"); JALX p.201 ("removed in Release 6").
# COP2 (no coprocessor 2, Config1.C2 = 0, Vol III Table 9.65 p.239): COP2 p.141, MFC2 p.268, BC2EQZ p.64, LWC2 p.237 (Release 6 COP2
# encoding); Vol III sec 6.2.22 p.100: "A COP2, LWC2, SWC2, LDC2, or SDC2 instruction was executed, and the CU2 bit in the Status register
# was a zero. COP2 instructions include MFC2, ..."; CE = "unit number of the coprocessor being referenced". Status.CU2 reads 0 without a
# coprocessor 2 ("If there is no provision for connecting a coprocessor, the corresponding CU bit must be ignored on write and read as
# zero", MD00090 Vol III Rev 2.50 Table 8-19 p.79; the Release 6 table, Rev 6.02 Table 9.47 p.190, is image-only in the PDF).
# User Mode: DERET, MFHC0 (COP0 space): Coprocessor Unusable, CE = 0 (sec 6.2.22 p.100; Table A.1 p.451: "the unusable exception takes
# priority"); CRC32W: Reserved Instruction.
# Not run here (QEMU's mips32r6-generic is another legal configuration): the TLB instructions (QEMU has a TLB MMU; this profile the
# Fixed Mapping MMU, Vol III sec A.1.3 p.317), LLWP/SCWP (QEMU has them; Config5.XNP = 1 here, LLWP p.228), TLBINV/TLBINVF/SDBBP (QEMU
# enters an endless loop). Their words do not decode in the model (Tests/InstructionTests.lean).
# oracle: expect gpr:s4=20 mem:0x10010000=0x28 mem:0x1001002c=0x2000002c mem:0x10010044=0x2c mem:0x10010048=0x28 mem:0x1001004c=0x2000002c
# oracle: expect-deviation mem:0x1001002c MD00090 Vol III Rev 6.02 sec 6.2.22 p.100 (COP2 with Status.CU2 = 0 raises Coprocessor Unusable, CE = 2; CU2 reads 0 without a coprocessor 2, Rev 2.50 Table 8-19 p.79): QEMU raises Reserved Instruction for COP2
# oracle: expect-deviation mem:0x10010030 same as mem:0x1001002c (MFC2)
# oracle: expect-deviation mem:0x10010034 same as mem:0x1001002c (BC2EQZ)
# oracle: expect-deviation mem:0x10010038 same as mem:0x1001002c (LWC2, Release 6 COP2 encoding)
# oracle: expect-deviation mem:0x1001004c same as mem:0x1001002c (COP2 in User Mode)
.data
res: .space 96
.ktext
mfc0 $k0, $13
li $k1, 0x3000007c
and $k0, $k0, $k1
sw $k0, 0($s7)
addiu $s7, $s7, 4
addiu $s4, $s4, 1
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
li $k1, 0
eret
.text
la $s7, res
li $s4, 0
la $t0, res
# Kernel Mode
.word 0x4200001f        # deret
.word 0x40486000        # mfhc0 $t0, $12
.word 0x40c86000        # mthc0 $t0, $12
.word 0x7d09002f        # lwe $t1, 0($t0)
.word 0x7d09001f        # swe $t1, 0($t0)
.word 0x7d01001b        # cachee 1, 0($t0)
.word 0x7d000023        # prefe 0, 0($t0)
.word 0x7d2a008f        # crc32w $t2, $t1, $t2
.word 0x7d00003d        # ginvi $t0
.word 0x7d0000bd        # ginvt $t0, 0
.word 0x0109001e        # ddiv $t0, $t1 (MIPS64)
.word 0x4a000001        # cop2 1
.word 0x48081000        # mfc2 $t0, $2
.word 0x49220002        # bc2eqz $2, 8
.word 0x49484800        # lwc2 $t0, 0($t1)
.word 0x74100000        # jalx
# User Mode (Status = CU1|UM|EXL, eret)
la $t2, user
mtc0 $t2, $14
lui $t3, 0x2000
ori $t3, $t3, 0x12
mtc0 $t3, $12
eret
user:
.word 0x4200001f        # deret
.word 0x40486000        # mfhc0 $t0, $12
.word 0x7d2a008f        # crc32w $t2, $t1, $t2
.word 0x4a000001        # cop2 1
li $s0, 7
li $t2, 0
li $t3, 0
