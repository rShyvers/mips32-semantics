# di/ei: the old Status is returned in rt, Status.IE is cleared/set; di/ei with rt = $zero; Status read back.
# Status.FR (bit 26) is masked out of every value read ($t7 = ~0x04000000): a Release 6 FPU reads FR = 1 (profile D2), the model 0 until W5
# (checked in fp_fcsr_nan2008_abs2008).
# MD00086 Vol II-A Rev 6.06: DI p.164, EI p.176 (MIPS32 Release 2); Status.IE MD00090 Vol III Rev 6.02.
# oracle: expect gpr:s0=0x20000000 gpr:s1=0x20000001 gpr:s2=0x20000001 gpr:s3=0x20000000 gpr:s4=0 gpr:s5=1
.data
res: .space 64
.text
lui $t7, 0xfbff
ori $t7, $t7, 0xffff
ei $s0
and $s0, $s0, $t7
di $s1
and $s1, $s1, $t7
ei $zero
mfc0 $s2, $12
and $s2, $s2, $t7
di
mfc0 $s3, $12
and $s3, $s3, $t7
ei $s6
and $s6, $s6, $t7
di $zero
mfc0 $s4, $12
andi $s4, $s4, 1
ei
mfc0 $s5, $12
andi $s5, $s5, 1
li $v0, 10
syscall
