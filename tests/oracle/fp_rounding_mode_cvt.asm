# FCSR.RM controls cvt.w.s: RM=0 nearest-even, 1 toward zero, 2 toward +inf, 3 toward -inf.
# MD00086 Vol II-A Rev 6.06: CVT.W.fmt p.160, CTC1 p.149-151, Vol I FCSR RM field (section "FCSR").
# 2.5 -> RN 2, RZ 2, RP 3, RM 2 ; -2.5 -> RN -2, RZ -2, RP -2, RM -3.
# oracle: expect gpr:s0=2 gpr:s1=2 gpr:s2=3 gpr:s3=2 gpr:s4=0xfffffffe gpr:s5=0xfffffffe gpr:s6=0xfffffffe gpr:s7=0xfffffffd
li $t9, 0x40200000
mtc1 $t9, $f0
li $t9, 0xc0200000
mtc1 $t9, $f1
ctc1 $zero, $31
cvt.w.s $f2, $f0
mfc1 $s0, $f2
li $t0, 1
ctc1 $t0, $31
cvt.w.s $f2, $f0
mfc1 $s1, $f2
li $t0, 2
ctc1 $t0, $31
cvt.w.s $f2, $f0
mfc1 $s2, $f2
li $t0, 3
ctc1 $t0, $31
cvt.w.s $f2, $f0
mfc1 $s3, $f2
ctc1 $zero, $31
cvt.w.s $f2, $f1
mfc1 $s4, $f2
li $t0, 1
ctc1 $t0, $31
cvt.w.s $f2, $f1
mfc1 $s5, $f2
li $t0, 2
ctc1 $t0, $31
cvt.w.s $f2, $f1
mfc1 $s6, $f2
li $t0, 3
ctc1 $t0, $31
cvt.w.s $f2, $f1
mfc1 $s7, $f2
ctc1 $zero, $31
li $v0, 10
syscall
