# RDPGPR/WRPGPR (MIPS32 Release 2) with SRSCtl.HSS = 0: only the normal GPRs exist ("shadow set zero"), SRSCtl.PSS = 0, so
# `rdpgpr rd, rt` is GPR[rd] <- GPR[rt] and `wrpgpr rd, rt` is GPR[rd] <- GPR[rt]; a write to $zero is ignored. SRSCtl reads 0
# before and after a write of 0 (ESS = PSS = 0).
# MD00086 Vol II-A Rev 6.06 RDPGPR p.335 ("GPR[rd] <- SGPR[SRSCtlPSS, rt]"), WRPGPR p.444 ("SGPR[SRSCtlPSS, rd] <- GPR[rt]");
# MD00090 Vol III Rev 6.02 sec 7 p.103 ("The normal GPRs are logically considered shadow set zero"), Table 9.49 p.203-204.
# oracle: expect gpr:s0=0x12345678 gpr:s1=0x9abcdef0 gpr:s2=0 gpr:s3=0 gpr:s4=0x12345678
.text
li $t0, 0x12345678
li $t1, 0x9abcdef0
rdpgpr $s0, $t0
wrpgpr $s1, $t1
wrpgpr $zero, $t1
mfc0 $s2, $12, 2
mtc0 $zero, $12, 2
mfc0 $s3, $12, 2
rdpgpr $s4, $s0
li $v0, 10
syscall
