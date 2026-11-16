# recip/rsqrt of 3.0 / 2.0 / 10.0 (.s and .d): the result is an approximation with implementation-dependent accuracy (<= 1 ULP), so the
# result bits and the Inexact flag are not compared; the program checks only that both executors terminate the same way.
# MD00086 Vol II-A Rev 6.06: RECIP.fmt p.336 / RSQRT.fmt p.343: 'The numeric accuracy of this operation is implementation dependent ... differs from the exact result by no more than one ULP'.
# oracle: unpredictable fpr MD00086 Rev 6.06 RECIP.fmt p.336 / RSQRT.fmt: numeric accuracy implementation dependent (within 1 ULP)
# oracle: unpredictable gpr MD00086 Rev 6.06 RECIP.fmt p.336: accuracy and rounding-mode dependence implementation dependent (results stored in GPRs)
# oracle: unpredictable fcsr MD00086 Rev 6.06 RECIP.fmt p.336: Inexact/Underflow flags of an approximation are implementation dependent
# oracle: unpredictable mem MD00086 Rev 6.06 RECIP.fmt p.336: stored approximation results
.data
res: .space 160
.text
la $s7, res
li $t9, 0x40400000
mtc1 $t9, $f2
ctc1 $zero, $31
recip.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 0($s7)
sw $t1, 4($s7)
ctc1 $zero, $31
rsqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 8($s7)
sw $t1, 12($s7)
li $t9, 0x40000000
mtc1 $t9, $f2
ctc1 $zero, $31
recip.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 16($s7)
sw $t1, 20($s7)
ctc1 $zero, $31
rsqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 24($s7)
sw $t1, 28($s7)
li $t9, 0x41200000
mtc1 $t9, $f2
ctc1 $zero, $31
recip.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 32($s7)
sw $t1, 36($s7)
ctc1 $zero, $31
rsqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 40($s7)
sw $t1, 44($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40080000
mthc1 $t9, $f2
ctc1 $zero, $31
recip.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 48($s7)
sw $t1, 52($s7)
ctc1 $zero, $31
rsqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 56($s7)
sw $t1, 60($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40000000
mthc1 $t9, $f2
ctc1 $zero, $31
recip.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 64($s7)
sw $t1, 68($s7)
ctc1 $zero, $31
rsqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 72($s7)
sw $t1, 76($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40240000
mthc1 $t9, $f2
ctc1 $zero, $31
recip.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 80($s7)
sw $t1, 84($s7)
ctc1 $zero, $31
rsqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 88($s7)
sw $t1, 92($s7)
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
