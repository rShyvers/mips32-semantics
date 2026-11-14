# JR.HB / JALR.HB (MIPS32 Release 2; MD00086 Vol II-A Rev 6.06, JR.HB p.208, JALR.HB p.198): JR/JALR with hint
# bit 10 set. They jump (and link) like JR/JALR; the hazard barrier has no state in the model.
# oracle: expect gpr:s0=0 gpr:s1=2 gpr:s2=3
la $t0, t1lab
jr.hb $t0
nop
li $s0, 1
t1lab:
li $s1, 2
la $t1, sub
jalr.hb $ra, $t1
nop
li $v0, 10
syscall
sub:
li $s2, 3
li $v0, 10
syscall
