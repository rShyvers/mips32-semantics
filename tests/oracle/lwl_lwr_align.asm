# lwl/lwr at all four byte offsets (big-endian), merging into a pre-loaded destination.
# MD00086 Vol II-A Rev 6.06: LWL p.240-242 (Figure 4.2), LWR p.247-251 (Figure 4.3).
# Memory word = 11 22 33 44 (bytes 0..3); destination initial = AA BB CC DD.
# LWL BE: off0 11223344, off1 223344DD, off2 3344CCDD, off3 44BBCCDD.
# LWR BE: off0 AABBCC11, off1 AABB1122, off2 AA112233, off3 11223344.
# oracle: expect gpr:s0=0x11223344 gpr:s1=0x223344dd gpr:s2=0x3344ccdd gpr:s3=0x44bbccdd
# oracle: expect gpr:s4=0xaabbcc11 gpr:s5=0xaabb1122 gpr:s6=0xaa112233 gpr:s7=0x11223344
.data
w: .word 0x11223344
.text
la $t0, w
li $s0, 0xAABBCCDD
lwl $s0, 0($t0)
li $s1, 0xAABBCCDD
lwl $s1, 1($t0)
li $s2, 0xAABBCCDD
lwl $s2, 2($t0)
li $s3, 0xAABBCCDD
lwl $s3, 3($t0)
li $s4, 0xAABBCCDD
lwr $s4, 0($t0)
li $s5, 0xAABBCCDD
lwr $s5, 1($t0)
li $s6, 0xAABBCCDD
lwr $s6, 2($t0)
li $s7, 0xAABBCCDD
lwr $s7, 3($t0)
li $v0, 10
syscall
