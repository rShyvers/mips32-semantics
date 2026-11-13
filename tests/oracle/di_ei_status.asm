# di/ei: the old Status is returned in rt, Status.IE is cleared/set; di/ei with rt = $zero; Status read back.
# MD00086 Vol II-A Rev 6.06: DI p.164, EI p.176 (MIPS32 Release 2); Status.IE MD00090 Vol III Rev 6.02.
# oracle: expect gpr:s0=0x20000000 gpr:s1=0x20000001 gpr:s2=0x20000001 gpr:s3=0x20000000 gpr:s4=0 gpr:s5=1
.data
res: .space 64
.text
ei $s0
di $s1
ei $zero
mfc0 $s2, $12
di
mfc0 $s3, $12
ei $s6
di $zero
mfc0 $s4, $12
andi $s4, $s4, 1
ei
mfc0 $s5, $12
andi $s5, $s5, 1
li $v0, 10
syscall
