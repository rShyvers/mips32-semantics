# Invalid operations deliver the default quiet NaN: MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 "Value Supplied When a New Quiet NaN Is
# Created": single 0x7fc00000 with FCSR.NAN2008 = 1 (Release 6: NAN2008 is required 1, FCSR Table 6.8 p.94; it would be 0x7fbfffff with NAN2008 = 0).
# MD00086 Vol II-A Rev 6.06 DIV.fmt p.170, SQRT.fmt p.382, SUB.fmt p.389. 0/0, inf-inf, sqrt(-1). FCSR not compared here (cfc1 not used).
# Release 6 model and QEMU agree: f10 = f11 = f12 = 0x7fc00000.
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x7f800000
mtc1 $t9, $f1
li $t9, 0xbf800000
mtc1 $t9, $f2
div.s $f10, $f0, $f0
sub.s $f11, $f1, $f1
sqrt.s $f12, $f2
li $v0, 10
syscall
