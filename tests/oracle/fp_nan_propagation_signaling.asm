# add/sub/mul/div.s with signaling-NaN operands (0x7fa00001, 0x7fa00002, 0xffa00005): Invalid is raised and the result is the operand SNaN with its
# most-significant fraction bit set (quieted, payload kept), e.g. 0x7fa00001 -> 0x7fe00001; with two SNaNs the first operand is the one passed on (a pin, not required by the manual).
# MD00082 Vol I-A Rev 6.01 sec 6.3.1.4 p.81 ('SNaN operands cause the Invalid Operation exception for arithmetic operations. ... An SNaN is never produced as a result value'), sec 6.3.1.5 p.82 ('a QNaN operand causes an arithmetic operation to supply a QNaN result. When possible, this QNaN result is one of the operand QNaN values'; Table 6.3: new QNaN 0x7fc00000 when none can be copied) and p.83 (FCSRNAN2008=1: 'If the chosen input is a SNAN, the only change is to set the leftmost/most-significant mantissa bit'), sec 6.7.2.1 p.100.
# NOTE Release 6 encoding (FCSR.NAN2008 = 1, Table 6.8 p.94): fraction MSB (bit 22) = 1 is QUIET, 0 is SIGNALING, so 0x7fa00001 is an sNaN and 0x7fc00003 a QNaN.
.data
res: .space 192
.text
la $s7, res
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7fa00001
mtc1 $t9, $f4
ctc1 $zero, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 0($s7)
sw $t1, 4($s7)
li $t9, 0x7fa00001
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
ctc1 $zero, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 8($s7)
sw $t1, 12($s7)
li $t9, 0x7fa00001
mtc1 $t9, $f2
li $t9, 0x7fa00002
mtc1 $t9, $f4
ctc1 $zero, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 16($s7)
sw $t1, 20($s7)
li $t9, 0xffa00005
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
ctc1 $zero, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 24($s7)
sw $t1, 28($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7fa00001
mtc1 $t9, $f4
ctc1 $zero, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 32($s7)
sw $t1, 36($s7)
li $t9, 0x7fa00001
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
ctc1 $zero, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 40($s7)
sw $t1, 44($s7)
li $t9, 0x7fa00001
mtc1 $t9, $f2
li $t9, 0x7fa00002
mtc1 $t9, $f4
ctc1 $zero, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 48($s7)
sw $t1, 52($s7)
li $t9, 0xffa00005
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
ctc1 $zero, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 56($s7)
sw $t1, 60($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7fa00001
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 64($s7)
sw $t1, 68($s7)
li $t9, 0x7fa00001
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 72($s7)
sw $t1, 76($s7)
li $t9, 0x7fa00001
mtc1 $t9, $f2
li $t9, 0x7fa00002
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 80($s7)
sw $t1, 84($s7)
li $t9, 0xffa00005
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 88($s7)
sw $t1, 92($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7fa00001
mtc1 $t9, $f4
ctc1 $zero, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 96($s7)
sw $t1, 100($s7)
li $t9, 0x7fa00001
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
ctc1 $zero, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 104($s7)
sw $t1, 108($s7)
li $t9, 0x7fa00001
mtc1 $t9, $f2
li $t9, 0x7fa00002
mtc1 $t9, $f4
ctc1 $zero, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 112($s7)
sw $t1, 116($s7)
li $t9, 0xffa00005
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
ctc1 $zero, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 120($s7)
sw $t1, 124($s7)
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
