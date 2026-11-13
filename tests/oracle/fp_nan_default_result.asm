# Invalid operations deliver the default quiet NaN. With Has2008 = 0 (legacy) the default QNaN is 0x7fbfffff.
# MD00082 Vol I-A Rev 6.01 p.82 Table 6.3 "Value Supplied When a New Quiet NaN Is Created": single, FCSR.NAN2008 = 0 =>
# 0x7fbfffff (0x7fc00000 only when NAN2008 = 1). MD00086 Vol II-A Rev 6.06 DIV.fmt p.170, SQRT.fmt p.382, SUB.fmt p.389.  0/0, inf-inf, sqrt(-1) => 0x7fbfffff.
# FCSR flag/cause bits are not compared here (cfc1 not used).
# oracle: expect fpr:f10=0x7fbfffff fpr:f11=0x7fbfffff fpr:f12=0x7fbfffff
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
