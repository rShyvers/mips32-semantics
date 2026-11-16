# FP exceptions with a .ktext handler: Inexact, Invalid (sqrt -1), Divide-by-zero, Overflow, Underflow (enabled one at a time), a no-trap case
# (exact add, Overflow enabled) and cvt.w.s of NaN with all enables. The handler records ExcCode history ($s6), FCSR at the trap ($s5), count ($s4),
# clears FCSR.Cause and skips the instruction. Destination registers are stored after each case; the program ends by running off the text.
# Overflow with the Overflow trap enabled: Cause = O only (no Inexact), because 'Inexact is signaled if the rounded result overflows WITHOUT an overflow trap'.
# MD00082 Vol I-A Rev 6.01 sec 6.7.1 p.98-99 (an enabled exception -> Floating Point exception, ExcCode 15, destination not written, Flags not updated, Cause set);
# MD00090 Vol III Rev 6.02 Cause ExcCode 15 = FPE.
# oracle: expect gpr:s4=6
# oracle: expect-deviation mem:0x1001002c MD00082 Vol I-A Rev 6.01 sec 6.7.2.6 p.102: Inexact is signaled on overflow only 'without an overflow trap'; with Enables.O set the model reports Cause=O (0x4200 with the enable), QEMU also sets Cause.I (0x5200)
.data
res: .space 148
.ktext
mfc0 $k0, $13
srl $k0, $k0, 2
andi $k0, $k0, 31
sll $s6, $s6, 8
or $s6, $s6, $k0
addiu $s4, $s4, 1
cfc1 $s5, $31
li $k1, 0xfffc0fff
and $k1, $s5, $k1
ctc1 $k1, $31
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
eret
.text
la $s7, res
li $s4, 0
li $s6, 0
li $t9, 0x12345678
mtc1 $t9, $f6
li $t8, 0x00000080
ctc1 $t8, $31
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x40400000
mtc1 $t9, $f4
li $t8, 0x00000080
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
ctc1 $zero, $31
sw $t0, 0($s7)
sw $t1, 4($s7)
sw $s5, 8($s7)
li $t9, 0x12345678
mtc1 $t9, $f6
li $t8, 0x00000800
ctc1 $t8, $31
li $t9, 0xbf800000
mtc1 $t9, $f2
li $t8, 0x00000800
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
ctc1 $zero, $31
sw $t0, 12($s7)
sw $t1, 16($s7)
sw $s5, 20($s7)
li $t9, 0x12345678
mtc1 $t9, $f6
li $t8, 0x00000400
ctc1 $t8, $31
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t8, 0x00000400
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
ctc1 $zero, $31
sw $t0, 24($s7)
sw $t1, 28($s7)
sw $s5, 32($s7)
li $t9, 0x12345678
mtc1 $t9, $f6
li $t8, 0x00000200
ctc1 $t8, $31
li $t9, 0x7f7fffff
mtc1 $t9, $f2
li $t9, 0x7f7fffff
mtc1 $t9, $f4
li $t8, 0x00000200
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
ctc1 $zero, $31
sw $t0, 36($s7)
sw $t1, 40($s7)
sw $s5, 44($s7)
li $t9, 0x12345678
mtc1 $t9, $f6
li $t8, 0x00000100
ctc1 $t8, $31
li $t9, 0x0da24260
mtc1 $t9, $f2
li $t9, 0x0da24260
mtc1 $t9, $f4
li $t8, 0x00000100
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
ctc1 $zero, $31
sw $t0, 48($s7)
sw $t1, 52($s7)
sw $s5, 56($s7)
li $t9, 0x12345678
mtc1 $t9, $f6
li $t8, 0x00000200
ctc1 $t8, $31
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
li $t8, 0x00000200
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
ctc1 $zero, $31
sw $t0, 60($s7)
sw $t1, 64($s7)
sw $s5, 68($s7)
li $t9, 0x12345678
mtc1 $t9, $f6
li $t8, 0x00000f80
ctc1 $t8, $31
li $t9, 0x7fa00000
mtc1 $t9, $f2
li $t8, 0x00000f80
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
ctc1 $zero, $31
sw $t0, 72($s7)
sw $t1, 76($s7)
sw $s5, 80($s7)
