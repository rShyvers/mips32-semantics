# Single-precision arithmetic on ordinary values: add.s sub.s mul.s div.s sqrt.s abs.s neg.s mov.s.
# MD00086 Vol II-A Rev 6.06: ADD.fmt p.34, SUB.fmt p.389, MUL.fmt p.302, DIV.fmt p.170, SQRT.fmt p.382, ABS.fmt p.32,
# NEG.fmt p.307, MOV.fmt p.275. a=1.5 (3fc00000) b=2.25 (40100000) c=9.0 (41100000) n=-3.5 (c0600000).
# a+b=3.75 (40700000) b-a=0.75 (3f400000) a*b=3.375 (40580000) c/b=4.0 (40800000) sqrt(c)=3.0 (40400000) abs(n)=3.5 neg(a)=-1.5
# oracle: expect fpr:f10=0x40700000 fpr:f11=0x3f400000 fpr:f12=0x40580000 fpr:f13=0x40800000 fpr:f14=0x40400000 fpr:f15=0x40600000 fpr:f16=0xbfc00000 fpr:f17=0x3fc00000
li $t9, 0x3fc00000
mtc1 $t9, $f0
li $t9, 0x40100000
mtc1 $t9, $f1
li $t9, 0x41100000
mtc1 $t9, $f2
li $t9, 0xc0600000
mtc1 $t9, $f3
add.s $f10, $f0, $f1
sub.s $f11, $f1, $f0
mul.s $f12, $f0, $f1
div.s $f13, $f2, $f1
sqrt.s $f14, $f2
abs.s $f15, $f3
neg.s $f16, $f0
mov.s $f17, $f0
li $v0, 10
syscall
