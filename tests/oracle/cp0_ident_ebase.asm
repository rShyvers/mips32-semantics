# mfc0 PRId/Config/Config1/EBase and cfc1 FIR: implementation-specific constants are NOT compared; only fields the manual fixes are:
# Config.BE (bit 15) = 1, Config.AT = 0 (MIPS32), Config.AR = 1 (Release 2), Config1.FP (bit 0) = 1, FIR.S/D/L (bits 16,17,21) = 1 (L is required with D: MD00086 Vol II-A Rev 6.06 §3.1 p.30, MD00082 Vol I-A Rev 6.01 Table 6.4 p.85) and FIR.PS (bit 18) = 0 (F64, bit 22, is not compared: QEMU's 24Kf has a 64-bit FPU),
# EBase bits 31..30 = 10, CPUNum (9..0) = 0 and EBase read/write round trip (restored before exit).
# MD00090 Vol III Rev 6.02: PRId p.221, EBase Table 9.58 p.224, Config Table 9.64 p.233-234, Config1 p.237; MD00082 Vol I-A Rev 6.01 FIR Table 6.5 p.88.
# oracle: unpredictable gpr:s0 MD00090 Vol III Rev 6.02 PRId: Company/Processor ID/Revision are implementation-defined constants
# oracle: unpredictable gpr:s1 MD00090 Vol III Rev 6.02 Config: only BE/AT/AR are fixed by the architecture (checked in s2); the rest is implementation-defined
# oracle: unpredictable gpr:s3 MD00090 Vol III Rev 6.02 Config1: cache/TLB geometry fields are implementation-defined (FP bit checked in s4)
# oracle: unpredictable gpr:s5 MD00082 Vol I-A Rev 6.01 FIR: ProcessorID/Revision are implementation-defined (fixed bits checked in s6)
.data
res: .space 64
.text
mfc0 $s0, $15
mfc0 $s1, $16
srl $s2, $s1, 10
andi $s2, $s2, 0x3f
mfc0 $s3, $16, 1
andi $s4, $s3, 1
cfc1 $s5, $0
li $t0, 0x00270000
and $s6, $s5, $t0
mfc0 $t1, $15, 1
srl $s7, $t1, 30
andi $t2, $t1, 0x3ff
li $t3, 0x3ffff000
mtc0 $t3, $15, 1
mfc0 $t4, $15, 1
li $t5, 0x80000000
mtc0 $t5, $15, 1
mfc0 $t6, $15, 1
li $v0, 10
syscall
