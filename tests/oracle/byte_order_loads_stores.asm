# sb/lb/lbu/sh/lh/lhu byte order and sign/zero extension, big-endian.
# MD00086 Vol II-A Rev 6.06: SB p.344-345, SH p.373, LB p.211, LBU p.213, LH p.219, LHU p.221.
# Word 0x8182F384: byte0=81 byte1=82 byte2=F3 byte3=84; half0=8182 half1=F384.
# oracle: expect gpr:s0=0xffffff81 gpr:s1=0x00000081 gpr:s2=0xfffff384 gpr:s3=0x0000f384 gpr:s4=0xffff8182
.data
w: .word 0x8182F384
out: .space 16
.text
la $t0, w
lb $s0, 0($t0)
lbu $s1, 0($t0)
lh $s2, 2($t0)
lhu $s3, 2($t0)
lh $s4, 0($t0)
lb $s5, 3($t0)
lbu $s6, 2($t0)
la $t1, out
li $t2, 0x12345678
sb $t2, 0($t1)
sb $t2, 1($t1)
sh $t2, 2($t1)
sh $t2, 4($t1)
sb $t2, 7($t1)
lw $s7, 0($t1)
lw $t3, 4($t1)
li $v0, 10
syscall
