# sb/lb/lbu/sh/lh/lhu byte order and sign/zero extension, little-endian (DECISIONS D1; MD00090 Vol III Rev 6.02 Config.BE = 0).
# MD00086 Vol II-A Rev 6.06: SB p.344-345, SH p.373, LB p.211, LBU p.213, LH p.219, LHU p.221.
# Word 0x8182F384: byte0=84 byte1=F3 byte2=82 byte3=81; half0=F384 half1=8182 (byte k at address a+k holds bits 8k+7..8k).
# oracle: expect gpr:s0=0xffffff84 gpr:s1=0x00000084 gpr:s2=0xffff8182 gpr:s3=0x00008182 gpr:s4=0xfffff384 gpr:s5=0xffffff81 gpr:s6=0x82
# oracle: expect gpr:s7=0x56787878 gpr:t3=0x78005678
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
