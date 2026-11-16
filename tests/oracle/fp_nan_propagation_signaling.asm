# add/sub/mul/div.s with legacy-signaling NaN operands (0x7fc00001, 0xffc00005): Invalid is raised and the result is the default QNaN 0x7fbfffff.
# Release 6 (FCSR.NAN2008 = 1) reverses the encodings: these operands are QUIET NaNs there (no Invalid, the operand is propagated). The test exercises
# the model's legacy FPU; every result slot and the FCSR differ until W5 (known model bug).
# MD00082 Vol I-A Rev 6.01 sec 6.3.1.4 p.81 ('An SNaN is never produced as a result value'), sec 6.3.1.5 p.82 ('a QNaN operand causes an arithmetic operation to supply a QNaN result. When possible, this QNaN result is one of the operand QNaN values'; Table 6.3: new QNaN 0x7fbfffff when none can be copied), sec 6.7.2.1 p.100.
# NOTE legacy encoding (Has2008 = 0): fraction MSB (bit 22) = 1 is SIGNALING, 0 is QUIET, so 0x7fc00001 is an sNaN and 0x7fa00003 a QNaN.
# oracle: known-model-bug mem MD00082 Vol I-A Rev 6.01 FCSR Table 6.8 p.94 (NAN2008 'Required as of Release 5', reset 1 in Release 6: a quiet NaN has the fraction MSB 1) and 6.3.1.5 Table 6.3 p.82; W5: the model is still the legacy (NAN2008 = 0) FPU, so the NaN classes of the operands and the results differ
# oracle: known-model-bug gpr:t1 same (last FCSR)
# oracle: known-model-bug fcsr same (final FCSR flags)
.data
res: .space 192
.text
la $s7, res
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7fc00001
mtc1 $t9, $f4
ctc1 $zero, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 0($s7)
sw $t1, 4($s7)
li $t9, 0x7fc00001
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
ctc1 $zero, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 8($s7)
sw $t1, 12($s7)
li $t9, 0x7fc00001
mtc1 $t9, $f2
li $t9, 0x7fc00002
mtc1 $t9, $f4
ctc1 $zero, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 16($s7)
sw $t1, 20($s7)
li $t9, 0xffc00005
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
ctc1 $zero, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 24($s7)
sw $t1, 28($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7fc00001
mtc1 $t9, $f4
ctc1 $zero, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 32($s7)
sw $t1, 36($s7)
li $t9, 0x7fc00001
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
ctc1 $zero, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 40($s7)
sw $t1, 44($s7)
li $t9, 0x7fc00001
mtc1 $t9, $f2
li $t9, 0x7fc00002
mtc1 $t9, $f4
ctc1 $zero, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 48($s7)
sw $t1, 52($s7)
li $t9, 0xffc00005
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
ctc1 $zero, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 56($s7)
sw $t1, 60($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7fc00001
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 64($s7)
sw $t1, 68($s7)
li $t9, 0x7fc00001
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 72($s7)
sw $t1, 76($s7)
li $t9, 0x7fc00001
mtc1 $t9, $f2
li $t9, 0x7fc00002
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 80($s7)
sw $t1, 84($s7)
li $t9, 0xffc00005
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 88($s7)
sw $t1, 92($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7fc00001
mtc1 $t9, $f4
ctc1 $zero, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 96($s7)
sw $t1, 100($s7)
li $t9, 0x7fc00001
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
ctc1 $zero, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 104($s7)
sw $t1, 108($s7)
li $t9, 0x7fc00001
mtc1 $t9, $f2
li $t9, 0x7fc00002
mtc1 $t9, $f4
ctc1 $zero, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 112($s7)
sw $t1, 116($s7)
li $t9, 0xffc00005
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
ctc1 $zero, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
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
