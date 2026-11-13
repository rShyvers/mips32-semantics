# lwxc1/ldxc1/swxc1/sdxc1: address = base + index register; word and doubleword (8-byte aligned).
# MD00086 Vol II-A Rev 6.06: LWXC1 p.254, LDXC1 p.218, SWXC1 p.406, SDXC1 p.364 (MIPS32 Release 2).
# oracle: expect fpr:f2=0x11223344 fpr:f4=0x55667788
.data
.align 3
src: .word 0x11223344, 0x55667788, 0x99aabbcc, 0xddeeff00
dst: .space 32
res: .space 64
.text
la $s7, res
la $t0, src
li $t1, 0
li $t2, 4
li $t3, 8
lwxc1 $f2, $t1($t0)
lwxc1 $f3, $t2($t0)
ldxc1 $f4, $t1($t0)
ldxc1 $f6, $t3($t0)
la $t4, dst
li $t5, 4
li $t6, 8
swxc1 $f2, $zero($t4)
swxc1 $f3, $t5($t4)
sdxc1 $f6, $t6($t4)
li $t7, 16
sdxc1 $f4, $t7($t4)
lw $s0, 0($t4)
lw $s1, 4($t4)
lw $s2, 8($t4)
lw $s3, 12($t4)
lw $s4, 16($t4)
lw $s5, 20($t4)
li $v0, 10
syscall
