# The Release 6 FPU mode bits, read raw: FCSR.NAN2008 (bit 18) and FCSR.ABS2008 (bit 19) are read-only 1 in Release 6, FIR.Has2008
# (bit 23) and FIR.F64 (bit 22) are 1, and Status.FR (bit 26) is read-only 1. QEMU mips32r6-generic implements them; the model is
# still the FR = 0, legacy-NaN FPU until W5 (profile DECISIONS D2), so every value differs: known model bugs.
# Every other FP test masks these bits out of its FCSR/Status reads and compares the rest exactly.
# MD00082 Vol I-A Rev 6.01: FCSR Table 6.8 p.93 (ABS2008 "1 (Release 6)", "Required as of Release 5") and p.94 (NAN2008 "1 (Release 6)");
# FIR Table 6.5 p.88 (Has2008 "1 Required (Release 6)") and p.89 (F64: "In Release 6, StatusFR is read-only 1"); MD00090 Vol III Rev 6.02
# 9.32 Status Table 9.47 p.191 (FR: "Release 6 disallows bi-modal support ...; i.e., FR is read-only").
# oracle: known-model-bug gpr:s0 MD00082 Vol I-A Rev 6.01 FCSR Table 6.8 p.93-94: ABS2008 and NAN2008 read 1 in Release 6 (FCSR = 0x000c0000 here); W5: the model reads 0
# oracle: known-model-bug gpr:s1 MD00082 Vol I-A Rev 6.01 FIR Table 6.5 p.88-89: Has2008 = 1 (Release 6) and F64 = 1 (64-bit FPU, StatusFR read-only 1); W5: the model has a 32-bit legacy FPU
# oracle: known-model-bug gpr:s2 MD00090 Vol III Rev 6.02 9.32 Status Table 9.47 p.191 and MD00082 Vol I-A Rev 6.01 FIR p.89 ("In Release 6, StatusFR is read-only 1"), profile D2; W5: the model reads FR = 0
ctc1 $zero, $31
cfc1 $s0, $31              # raw FCSR: only the read-only bits remain
cfc1 $t0, $0
lui $t1, 0x00c0            # FIR.Has2008 | FIR.F64
and $s1, $t0, $t1
mfc0 $t2, $12
lui $t3, 0x0400            # Status.FR
and $s2, $t2, $t3
move $t0, $zero            # raw FIR / Status: implementation-defined fields are not compared
move $t2, $zero
li $v0, 10
syscall
