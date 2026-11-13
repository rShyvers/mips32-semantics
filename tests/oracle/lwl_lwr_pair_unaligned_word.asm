# The canonical unaligned-word load: lwl 0(a)/lwr 3(a) reads 4 bytes at any alignment.
# MD00086 Vol II-A Rev 6.06: LWL p.240-242, LWR p.247-251 (programming note: LWL+LWR pair).
# Bytes at w: 01 02 03 04 05 06 07 08. Loads at offsets 1,2,3 give 02030405, 03040506, 04050607.
# oracle: expect gpr:s1=0x02030405 gpr:s2=0x03040506 gpr:s3=0x04050607
.data
w: .byte 1,2,3,4,5,6,7,8
.text
la $t0, w
lwl $s1, 1($t0)
lwr $s1, 4($t0)
lwl $s2, 2($t0)
lwr $s2, 5($t0)
lwl $s3, 3($t0)
lwr $s3, 6($t0)
li $v0, 10
syscall
