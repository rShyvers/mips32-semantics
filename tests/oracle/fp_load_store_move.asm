# lwc1/swc1/mtc1/mfc1 round trips, including the sign bit and NaN payloads (moves are bit-exact).
# MD00086 Vol II-A Rev 6.06: LWC1 p.236, SWC1 p.393, MTC1 p.292, MFC1 p.267.
# oracle: expect gpr:s0=0xff800001 gpr:s1=0x7fc00000 fpr:f3=0xff800001
.data
w: .word 0xff800001, 0x7fc00000
out: .space 8
.text
la $t0, w
lwc1 $f1, 0($t0)
lwc1 $f2, 4($t0)
mfc1 $s0, $f1
mfc1 $s1, $f2
mov.s $f3, $f1
la $t1, out
swc1 $f3, 0($t1)
swc1 $f2, 4($t1)
mtc1 $s0, $f31
li $v0, 10
syscall
