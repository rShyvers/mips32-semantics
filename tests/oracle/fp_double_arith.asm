# Double-precision arithmetic and conversions through memory (ldc1/sdc1, big-endian: first word = high word).
# MD00086 Vol II-A Rev 6.06: LDC1 p.215, SDC1 p.362, ADD.fmt p.34, SUB.fmt p.389, MUL.fmt p.302, DIV.fmt p.170,
# SQRT.fmt p.382, ABS.fmt p.32, NEG.fmt p.307, CVT.D.fmt p.153, CVT.S.fmt p.159, CVT.W.fmt p.160.
# x=1.5 (3ff8000000000000) y=0.25 (3fd0000000000000): x+y=1.75 x-y=1.25 x*y=0.375 x/y=6.0 sqrt(2.25)=1.5
.data
.align 3
x: .word 0x3ff80000, 0x00000000
y: .word 0x3fd00000, 0x00000000
s: .word 0x40100000, 0x00000000
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
li $v0, 10
syscall
