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
sw $t0, 0($s7)
sw $t1, 4($s7)
ctc1 $zero, $31
rsqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 8($s7)
sw $t1, 12($s7)
li $t9, 0x40000000
mtc1 $t9, $f2
ctc1 $zero, $31
recip.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 16($s7)
sw $t1, 20($s7)
ctc1 $zero, $31
rsqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 24($s7)
sw $t1, 28($s7)
li $t9, 0x41200000
mtc1 $t9, $f2
ctc1 $zero, $31
recip.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 32($s7)
sw $t1, 36($s7)
ctc1 $zero, $31
rsqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 40($s7)
sw $t1, 44($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40080000
mtc1 $t9, $f3
ctc1 $zero, $31
recip.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 48($s7)
sw $t1, 52($s7)
ctc1 $zero, $31
rsqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 56($s7)
sw $t1, 60($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f3
ctc1 $zero, $31
recip.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 64($s7)
sw $t1, 68($s7)
ctc1 $zero, $31
rsqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 72($s7)
sw $t1, 76($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40240000
mtc1 $t9, $f3
ctc1 $zero, $31
recip.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 80($s7)
sw $t1, 84($s7)
ctc1 $zero, $31
rsqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 88($s7)
sw $t1, 92($s7)
li $v0, 10
syscall
