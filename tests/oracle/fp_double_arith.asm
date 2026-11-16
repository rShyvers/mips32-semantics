# Double-precision arithmetic and conversions through memory (ldc1/sdc1, little-endian: first word = low word). The high words of
# the even FPRs are cleared before exit (the final FPR dump of an FR = 1 FPU holds only low words; results are in memory).
# MD00086 Vol II-A Rev 6.06: LDC1 p.215, SDC1 p.362, ADD.fmt p.34, SUB.fmt p.389, MUL.fmt p.302, DIV.fmt p.170,
# SQRT.fmt p.382, ABS.fmt p.32, NEG.fmt p.307, CVT.D.fmt p.153, CVT.S.fmt p.159, CVT.W.fmt p.160.
# x=1.5 (3ff8000000000000) y=0.25 (3fd0000000000000) s=4.0: x+y=1.75 x-y=1.25 x*y=0.375 x/y=6.0 sqrt(s)=2.0
.data
.align 3
x: .double 1.5
y: .double 0.25
s: .double 4.0
out: .space 64
.text
la $t0, x
ldc1 $f0, 0($t0)
ldc1 $f2, 8($t0)
ldc1 $f4, 16($t0)
add.d $f6, $f0, $f2
sub.d $f8, $f0, $f2
mul.d $f10, $f0, $f2
div.d $f12, $f0, $f2
sqrt.d $f14, $f4
abs.d $f16, $f0
neg.d $f18, $f0
mov.d $f20, $f2
la $t1, out
sdc1 $f6, 0($t1)
sdc1 $f8, 8($t1)
sdc1 $f10, 16($t1)
sdc1 $f12, 24($t1)
cvt.s.d $f22, $f0
cvt.d.s $f24, $f22
li $t2, 5
mtc1 $t2, $f26
cvt.d.w $f28, $f26
cvt.w.d $f30, $f12
mthc1 $zero, $f0
mthc1 $zero, $f2
mthc1 $zero, $f4
mthc1 $zero, $f6
mthc1 $zero, $f8
mthc1 $zero, $f10
mthc1 $zero, $f12
mthc1 $zero, $f14
mthc1 $zero, $f16
mthc1 $zero, $f18
mthc1 $zero, $f20
mthc1 $zero, $f22
mthc1 $zero, $f24
mthc1 $zero, $f26
mthc1 $zero, $f28
mthc1 $zero, $f30
li $v0, 10
syscall
