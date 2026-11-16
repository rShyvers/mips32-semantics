# FCSR.FS = 1 with subnormal INPUT operands: every input subnormal is replaced with zero of the same sign (MD00082 Vol I-A
# Rev 6.01 Table 6.8, FS, p.93) and "Flushing of subnormal input operands in all instructions except comparisons causes Inexact
# exception to be signaled" (sec 6.7.2.4, p.102; MADDF.fmt, MD00086 Vol II-A Rev 6.06 p.260: "the conditions [are] ORed").
# Cases (result, then FCSR as cfc1 reads it): MUL.D 2^-1074 * 2^100; CVT.D.S 2^-149; CVT.W.S 2^-149 in RP; MADDF.S 0 + 2^-149 * 2^100;
# MADDF.S 2^-149 + 1*1; ADD.S 1+1 (no subnormal: no flag); ADD.S 1 + 2^-149. QEMU mips32r6-generic does not flush inputs.
# oracle: expect-deviation mem:0x10010004 MD00082 Vol I-A Rev 6.01 sec 6.7.2.4 p.102 and Table 6.8 FS p.93: with FS=1 a subnormal input is replaced with zero and the flush signals Inexact; QEMU mips32r6-generic does not flush inputs (MUL.D gives 2^-974 exactly)
# oracle: expect-deviation mem:0x10010008 same (MUL.D: FCSR Cause/Flags Inexact from the input flush)
# oracle: expect-deviation mem:0x10010010 same (CVT.D.S: +0 instead of 2^-149)
# oracle: expect-deviation mem:0x10010014 same (CVT.D.S: Inexact from the input flush)
# oracle: expect-deviation mem:0x10010018 same (CVT.W.S RP: ceil(+0) = 0 instead of 1; FCSR agrees: Inexact either way)
# oracle: expect-deviation mem:0x10010020 same (MADDF.S: 0 + 0*2^100 = +0 instead of 2^-49)
# oracle: expect-deviation mem:0x10010024 same (MADDF.S: Inexact from the input flush, MADDF.fmt MD00086 Vol II-A Rev 6.06 p.260)
# oracle: expect mem:0x10010000=0x00000000 mem:0x10010004=0x00000000 mem:0x10010008=0x010c1004
# oracle: expect mem:0x1001000c=0x00000000 mem:0x10010010=0x00000000 mem:0x10010014=0x010c1004
# oracle: expect mem:0x10010018=0x00000000 mem:0x1001001c=0x010c1006
# oracle: expect mem:0x10010020=0x00000000 mem:0x10010024=0x010c1004
# oracle: expect mem:0x10010028=0x3f800000 mem:0x1001002c=0x010c1004
# oracle: expect mem:0x10010030=0x40000000 mem:0x10010034=0x010c0000
# oracle: expect mem:0x10010038=0x3f800000 mem:0x1001003c=0x010c1004
.data
res: .space 64
.text
la $s7, res
# MUL.D: 0x0000000000000001 * 0x4630000000000000 (2^100)
li $t9, 1
mtc1 $t9, $f2
mthc1 $zero, $f2
mtc1 $zero, $f4
li $t9, 0x46300000
mthc1 $t9, $f4
li $t8, 0x01000000
ctc1 $t8, $31
mul.d $f6, $f2, $f4
mfc1 $t0, $f6
mfhc1 $t2, $f6
cfc1 $t1, $31
sw $t0, 0($s7)
sw $t2, 4($s7)
sw $t1, 8($s7)
# CVT.D.S: 0x00000001
li $t9, 1
mtc1 $t9, $f8
li $t8, 0x01000000
ctc1 $t8, $31
cvt.d.s $f6, $f8
mfc1 $t0, $f6
mfhc1 $t2, $f6
cfc1 $t1, $31
sw $t0, 12($s7)
sw $t2, 16($s7)
sw $t1, 20($s7)
# CVT.W.S in RP (FCSR.RM = 2): 0x00000001
li $t8, 0x01000002
ctc1 $t8, $31
cvt.w.s $f6, $f8
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 24($s7)
sw $t1, 28($s7)
# MADDF.S: fd = +0, fs = 0x00000001, ft = 0x71800000 (2^100)
mtc1 $zero, $f6
li $t9, 0x71800000
mtc1 $t9, $f10
li $t8, 0x01000000
ctc1 $t8, $31
maddf.s $f6, $f8, $f10
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 32($s7)
sw $t1, 36($s7)
# MADDF.S: fd = 0x00000001, fs = ft = 1.0
li $t9, 1
mtc1 $t9, $f6
li $t9, 0x3f800000
mtc1 $t9, $f12
li $t8, 0x01000000
ctc1 $t8, $31
maddf.s $f6, $f12, $f12
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 40($s7)
sw $t1, 44($s7)
# ADD.S 1.0 + 1.0: no subnormal operand, no flag
li $t8, 0x01000000
ctc1 $t8, $31
add.s $f6, $f12, $f12
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 48($s7)
sw $t1, 52($s7)
# ADD.S 1.0 + 0x00000001
li $t8, 0x01000000
ctc1 $t8, $31
add.s $f6, $f12, $f8
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
