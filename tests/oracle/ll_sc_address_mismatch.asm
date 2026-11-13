# sc to an address different from the preceding ll fails (rt = 0, memory unchanged); a matching sc succeeds (rt = 1).
# MD00086 Vol II-A Rev 6.06 SC p.347: 'An SC will fail if the aligned address of the SC does not match that of the preceding LL.'
# oracle: expect gpr:t1=0 gpr:t3=1 gpr:s0=0x20 gpr:s2=0x77
.data
a: .word 0x10
b: .word 0x20
res: .space 64
.text
la $t4, a
la $t5, b
ll $t0, 0($t4)
li $t1, 0x99
sc $t1, 0($t5)
ll $t0, 0($t4)
li $t3, 0x77
sc $t3, 0($t4)
lw $s0, 0($t5)
li $s1, 0x20
lw $s2, 0($t4)
li $v0, 10
syscall
