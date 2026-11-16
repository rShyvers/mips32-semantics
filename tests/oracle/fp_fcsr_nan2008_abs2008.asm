# The Release 6 FPU mode bits, read raw: FCSR.NAN2008 (bit 18) and FCSR.ABS2008 (bit 19) are read-only 1 in Release 6, FIR.Has2008
# (bit 23) and FIR.F64 (bit 22) are 1, and Status.FR (bit 26) is read-only 1.
# QEMU mips32r6-generic and the model (Release 6 FPU) agree: after ctc1 $zero the raw FCSR is 0x000c0000, FIR has both bits, Status.FR is set.
# The other FP tests read FCSR and Status unmasked and see these bits too.
# oracle: expect gpr:s0=0x000c0000 gpr:s1=0x00c00000 gpr:s2=0x04000000
# MD00082 Vol I-A Rev 6.01: FCSR Table 6.8 p.93 (ABS2008 "1 (Release 6)", "Required as of Release 5") and p.94 (NAN2008 "1 (Release 6)");
# FIR Table 6.5 p.88 (Has2008 "1 Required (Release 6)") and p.89 (F64: "In Release 6, StatusFR is read-only 1"); MD00090 Vol III Rev 6.02
# 9.32 Status Table 9.47 p.191 (FR: "Release 6 disallows bi-modal support ...; i.e., FR is read-only").
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
