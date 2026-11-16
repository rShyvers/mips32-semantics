# add/sub/mul/div.s with QUIET NaN operands (0x7fc00003 = QNaN, 0x7fc00004 = QNaN, 0x7fa00001 = sNaN): no Invalid for a QNaN with a number; the result is a NaN and never
# a signaling one (compared: isNaN, bit 22, FCSR). With exactly one QNaN operand (and a number) the operand QNaN is the result (6.3.1.5 'when possible ... one of the operand QNaN values';
# the model and QEMU return it unchanged). With two NaN operands which one is returned is not specified, so those raw word slots stay 'unpredictable'.
# A QNaN with an sNaN operand raises Invalid (the sNaN is quieted and passed on).
# MD00082 Vol I-A Rev 6.01 sec 6.3.1.4 p.81 ('SNaN operands cause the Invalid Operation exception for arithmetic operations. ... An SNaN is never produced as a result value'), sec 6.3.1.5 p.82 ('a QNaN operand causes an arithmetic operation to supply a QNaN result. When possible, this QNaN result is one of the operand QNaN values'; Table 6.3: new QNaN 0x7fc00000 when none can be copied) and p.83 (FCSRNAN2008=1: 'If the chosen input is a SNAN, the only change is to set the leftmost/most-significant mantissa bit'), sec 6.7.2.1 p.100.
# NOTE Release 6 encoding (FCSR.NAN2008 = 1, Table 6.8 p.94): fraction MSB (bit 22) = 1 is QUIET, 0 is SIGNALING, so 0x7fa00001 is an sNaN and 0x7fc00003 a QNaN.
# oracle: unpredictable mem:0x10010018 MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x10010024 MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x10010030 MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x1001003c MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x10010060 MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x1001006c MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x10010078 MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x10010084 MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x100100a8 MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x100100b4 MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x100100c0 MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x100100cc MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x100100f0 MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x100100fc MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x10010108 MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable mem:0x10010114 MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: with two NaN operands, which one is returned is not specified ("When possible, this QNaN result is one of the operand QNaN values")
# oracle: unpredictable gpr:t0 MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: raw NaN payload of the last result (see mem slots)
# oracle: unpredictable fpr:f6 MD00082 Vol I-A Rev 6.01 sec 6.3.1.5 p.82: raw NaN payload of the last result
.data
res: .space 352
.text
la $s7, res
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7fc00003
mtc1 $t9, $f4
ctc1 $zero, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 0($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 4($s7)
sw $t1, 8($s7)
li $t9, 0x7fc00003
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
ctc1 $zero, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 12($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 16($s7)
sw $t1, 20($s7)
li $t9, 0x7fc00003
mtc1 $t9, $f2
li $t9, 0x7fc00004
mtc1 $t9, $f4
ctc1 $zero, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 24($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 28($s7)
sw $t1, 32($s7)
li $t9, 0x7fc00004
mtc1 $t9, $f2
li $t9, 0x7fc00003
mtc1 $t9, $f4
ctc1 $zero, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 36($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 40($s7)
sw $t1, 44($s7)
li $t9, 0x7fc00003
mtc1 $t9, $f2
li $t9, 0x7fa00001
mtc1 $t9, $f4
ctc1 $zero, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 48($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 52($s7)
sw $t1, 56($s7)
li $t9, 0x7fa00001
mtc1 $t9, $f2
li $t9, 0x7fc00003
mtc1 $t9, $f4
ctc1 $zero, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 60($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 64($s7)
sw $t1, 68($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7fc00003
mtc1 $t9, $f4
ctc1 $zero, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 72($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 76($s7)
sw $t1, 80($s7)
li $t9, 0x7fc00003
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
ctc1 $zero, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 84($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 88($s7)
sw $t1, 92($s7)
li $t9, 0x7fc00003
mtc1 $t9, $f2
li $t9, 0x7fc00004
mtc1 $t9, $f4
ctc1 $zero, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 96($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 100($s7)
sw $t1, 104($s7)
li $t9, 0x7fc00004
mtc1 $t9, $f2
li $t9, 0x7fc00003
mtc1 $t9, $f4
ctc1 $zero, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 108($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 112($s7)
sw $t1, 116($s7)
li $t9, 0x7fc00003
mtc1 $t9, $f2
li $t9, 0x7fa00001
mtc1 $t9, $f4
ctc1 $zero, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 120($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 124($s7)
sw $t1, 128($s7)
li $t9, 0x7fa00001
mtc1 $t9, $f2
li $t9, 0x7fc00003
mtc1 $t9, $f4
ctc1 $zero, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 132($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 136($s7)
sw $t1, 140($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7fc00003
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 144($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 148($s7)
sw $t1, 152($s7)
li $t9, 0x7fc00003
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 156($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 160($s7)
sw $t1, 164($s7)
li $t9, 0x7fc00003
mtc1 $t9, $f2
li $t9, 0x7fc00004
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 168($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 172($s7)
sw $t1, 176($s7)
li $t9, 0x7fc00004
mtc1 $t9, $f2
li $t9, 0x7fc00003
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 180($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 184($s7)
sw $t1, 188($s7)
li $t9, 0x7fc00003
mtc1 $t9, $f2
li $t9, 0x7fa00001
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 192($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 196($s7)
sw $t1, 200($s7)
li $t9, 0x7fa00001
mtc1 $t9, $f2
li $t9, 0x7fc00003
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 204($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 208($s7)
sw $t1, 212($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7fc00003
mtc1 $t9, $f4
ctc1 $zero, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 216($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 220($s7)
sw $t1, 224($s7)
li $t9, 0x7fc00003
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
ctc1 $zero, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 228($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 232($s7)
sw $t1, 236($s7)
li $t9, 0x7fc00003
mtc1 $t9, $f2
li $t9, 0x7fc00004
mtc1 $t9, $f4
ctc1 $zero, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 240($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 244($s7)
sw $t1, 248($s7)
li $t9, 0x7fc00004
mtc1 $t9, $f2
li $t9, 0x7fc00003
mtc1 $t9, $f4
ctc1 $zero, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 252($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 256($s7)
sw $t1, 260($s7)
li $t9, 0x7fc00003
mtc1 $t9, $f2
li $t9, 0x7fa00001
mtc1 $t9, $f4
ctc1 $zero, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 264($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 268($s7)
sw $t1, 272($s7)
li $t9, 0x7fa00001
mtc1 $t9, $f2
li $t9, 0x7fc00003
mtc1 $t9, $f4
ctc1 $zero, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 276($s7)
sll $t2, $t0, 1
lui $t3, 0xff00
sltu $t2, $t3, $t2
srl $t4, $t0, 22
andi $t4, $t4, 1
sll $t2, $t2, 1
or $t2, $t2, $t4
sw $t2, 280($s7)
sw $t1, 284($s7)
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
