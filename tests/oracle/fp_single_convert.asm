# Conversions: cvt.s.w, cvt.w.s (current rounding mode = RN), round/trunc/ceil/floor.w.s on +-2.5, +-3.5.
# MD00086 Vol II-A Rev 6.06: CVT.S.fmt p.159, CVT.W.fmt p.160, ROUND.W.fmt p.342, TRUNC.W.fmt p.441, CEIL.W.fmt p.128,
# FLOOR.W.fmt p.186. 2.5: round->2 (ties to even) trunc->2 ceil->3 floor->2 ; -2.5: -2 -2 -2 -3 ; 3.5: round->4 .
# cvt.s.w(-7) = -7.0 (c0e00000); cvt.w.s(2.5) with RN = 2; cvt.w.s(3.5) = 4.
# oracle: expect fpr:f10=0xc0e00000 fpr:f11=2 fpr:f12=4 fpr:f13=2 fpr:f14=2 fpr:f15=3 fpr:f16=2 fpr:f17=0xfffffffe fpr:f18=0xfffffffe fpr:f19=0xfffffffe fpr:f20=0xfffffffd fpr:f21=4
li $t0, -7
mtc1 $t0, $f0
li $t9, 0x40200000
mtc1 $t9, $f1
li $t9, 0x40600000
mtc1 $t9, $f2
li $t9, 0xc0200000
mtc1 $t9, $f3
cvt.s.w $f10, $f0
cvt.w.s $f11, $f1
cvt.w.s $f12, $f2
round.w.s $f13, $f1
trunc.w.s $f14, $f1
ceil.w.s $f15, $f1
floor.w.s $f16, $f1
round.w.s $f17, $f3
trunc.w.s $f18, $f3
ceil.w.s $f19, $f3
floor.w.s $f20, $f3
round.w.s $f21, $f2
li $v0, 10
syscall
