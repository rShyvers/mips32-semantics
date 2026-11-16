# FCSR.FS = 1: tiny non-zero results are flushed to zero of the same sign with Underflow+Inexact; subnormal inputs are replaced by zero (Release 5+, implementation-dependent before).
# MD00082 Vol I-A Rev 6.01 sec 6.7.2.4 p.101-102 ('Every tiny non-zero result is replaced with zero of the same sign ... Flushing of tiny non-zero results causes Inexact and Underflow').
# oracle: expect-deviation gpr:t1 MD00082 Vol I-A Rev 6.01 sec 6.7.2.4 p.102 ("Flushing of tiny non-zero results causes Inexact and Underflow exceptions to be signaled"; FCSR.FS Table 6.8 p.93): QEMU mips32r6-generic leaves the flags clear
# oracle: expect-deviation fcsr same
# oracle: expect-deviation mem:0x10010004 same
# oracle: expect-deviation mem:0x1001000c same
# oracle: expect-deviation mem:0x10010014 same
# oracle: expect-deviation mem:0x1001001c same
# oracle: expect-deviation mem:0x10010024 same
# oracle: expect-deviation mem:0x1001002c same
# oracle: expect-deviation mem:0x10010034 same
# oracle: expect-deviation mem:0x1001003c same
.data
res: .space 128
.text
la $s7, res
li $t9, 0x0da24260
mtc1 $t9, $f2
li $t9, 0x0da24260
mtc1 $t9, $f4
li $t9, 0x00800000
mtc1 $t9, $f8
li $t9, 0x3f000000
mtc1 $t9, $f10
li $t8, 0x01000000
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 0($s7)
sw $t1, 4($s7)
li $t8, 0x01000000
ctc1 $t8, $31
mul.s $f6, $f8, $f10
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 8($s7)
sw $t1, 12($s7)
li $t8, 0x01000001
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 16($s7)
sw $t1, 20($s7)
li $t8, 0x01000001
ctc1 $t8, $31
mul.s $f6, $f8, $f10
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 24($s7)
sw $t1, 28($s7)
li $t8, 0x01000002
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 32($s7)
sw $t1, 36($s7)
li $t8, 0x01000002
ctc1 $t8, $31
mul.s $f6, $f8, $f10
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 40($s7)
sw $t1, 44($s7)
li $t8, 0x01000003
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 48($s7)
sw $t1, 52($s7)
li $t8, 0x01000003
ctc1 $t8, $31
mul.s $f6, $f8, $f10
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 56($s7)
sw $t1, 60($s7)
move $t0, $zero
move $t2, $zero
mtc1 $zero, $f0
mtc1 $zero, $f2
mtc1 $zero, $f4
mtc1 $zero, $f6
mtc1 $zero, $f8
mtc1 $zero, $f10
mtc1 $zero, $f12
mtc1 $zero, $f14
mtc1 $zero, $f16
mtc1 $zero, $f18
mtc1 $zero, $f20
mtc1 $zero, $f22
mtc1 $zero, $f24
mtc1 $zero, $f26
mtc1 $zero, $f28
mtc1 $zero, $f30
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
