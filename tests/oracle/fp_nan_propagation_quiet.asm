# add/sub/mul/div.s with QUIET NaN operands (0x7fa00003 = QNaN, 0x7fa00004 = QNaN, 0x7fc00001 = sNaN): no Invalid for a QNaN with a number; the result is a NaN and never
# a signaling one (compared: isNaN, bit 22, FCSR). The exact payload is a documented pin: the model returns the first quiet-NaN operand unchanged ('when possible ... one of the operand QNaN values'),
# QEMU returns the default QNaN 0x7fbfffff; which NaN is returned is not specified, so the raw word slots are 'unpredictable' and the model value is pinned with 'expect' where a single QNaN is the only candidate.
# MD00082 Vol I-A Rev 6.01 sec 6.3.1.4 p.81 ('An SNaN is never produced as a result value'), sec 6.3.1.5 p.82 ('a QNaN operand causes an arithmetic operation to supply a QNaN result. When possible, this QNaN result is one of the operand QNaN values'; Table 6.3: new QNaN 0x7fbfffff when none can be copied), sec 6.7.2.1 p.100.
# NOTE legacy encoding (Has2008 = 0): fraction MSB (bit 22) = 1 is SIGNALING, 0 is QUIET, so 0x7fc00001 is an sNaN and 0x7fa00003 a QNaN.
# oracle: unpredictable mem:0x10010000 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: expect mem:0x10010000=0x7fa00003
# oracle: unpredictable mem:0x1001000c MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: expect mem:0x1001000c=0x7fa00003
# oracle: unpredictable mem:0x10010018 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x10010024 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x10010030 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x1001003c MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x10010048 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: expect mem:0x10010048=0x7fa00003
# oracle: unpredictable mem:0x10010054 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: expect mem:0x10010054=0x7fa00003
# oracle: unpredictable mem:0x10010060 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x1001006c MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x10010078 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x10010084 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x10010090 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: expect mem:0x10010090=0x7fa00003
# oracle: unpredictable mem:0x1001009c MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: expect mem:0x1001009c=0x7fa00003
# oracle: unpredictable mem:0x100100a8 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x100100b4 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x100100c0 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x100100cc MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x100100d8 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: expect mem:0x100100d8=0x7fa00003
# oracle: unpredictable mem:0x100100e4 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: expect mem:0x100100e4=0x7fa00003
# oracle: unpredictable mem:0x100100f0 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x100100fc MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x10010108 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable mem:0x10010114 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: which operand NaN is returned (or the default QNaN) is not specified
# oracle: unpredictable gpr:t0 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: raw NaN payload of the last result (see mem slots)
# oracle: unpredictable fpr:f6 MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82: raw NaN payload of the last result
.data
res: .space 352
.text
la $s7, res
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
mtc1 $t9, $f2
li $t9, 0x7fa00004
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
li $t9, 0x7fa00004
mtc1 $t9, $f2
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
mtc1 $t9, $f2
li $t9, 0x7fc00001
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
li $t9, 0x7fc00001
mtc1 $t9, $f2
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
mtc1 $t9, $f2
li $t9, 0x7fa00004
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
li $t9, 0x7fa00004
mtc1 $t9, $f2
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
mtc1 $t9, $f2
li $t9, 0x7fc00001
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
li $t9, 0x7fc00001
mtc1 $t9, $f2
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
mtc1 $t9, $f2
li $t9, 0x7fa00004
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
li $t9, 0x7fa00004
mtc1 $t9, $f2
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
mtc1 $t9, $f2
li $t9, 0x7fc00001
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
li $t9, 0x7fc00001
mtc1 $t9, $f2
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
mtc1 $t9, $f2
li $t9, 0x7fa00004
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
li $t9, 0x7fa00004
mtc1 $t9, $f2
li $t9, 0x7fa00003
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
li $t9, 0x7fa00003
mtc1 $t9, $f2
li $t9, 0x7fc00001
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
li $t9, 0x7fc00001
mtc1 $t9, $f2
li $t9, 0x7fa00003
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
li $v0, 10
syscall
