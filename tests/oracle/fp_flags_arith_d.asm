# add/sub/mul/div/sqrt (.d) in each rounding mode RN RZ RP RM: result bits and FCSR (flags + cause) for exact, inexact, overflow,
# underflow, divide-by-zero and invalid cases. Flags are cleared before every operation, enables are 0.
# MD00082 Vol I-A Rev 6.01 sec 6.7.2 p.99-102 (IEEE exceptions: Invalid, Division-by-zero, Overflow, Underflow, Inexact; default results per rounding mode),
# FCSR Flags bits 6..2 (V Z O U I) and Cause bits 17..12; MD00086 Vol II-A Rev 6.06 ADD.fmt p.34, SUB.fmt p.389, MUL.fmt p.302, DIV.fmt p.170, SQRT.fmt p.382.
# oracle: known-model-bug mem:0x10010060 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x10010068 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x1001006c MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x10010074 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x10010078 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x10010080 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x10010084 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x1001008c MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x10010090 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x10010098 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x1001009c MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x100100a4 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x100100a8 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x100100b0 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x100100b4 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x100100bc MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x10010120 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x10010128 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x1001012c MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x10010134 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x10010138 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x10010140 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x10010144 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x1001014c MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x10010180 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x10010188 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x1001018c MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x10010194 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x10010198 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x100101a0 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x100101a4 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x100101ac MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x10010210 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x10010218 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x1001021c MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x10010224 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x10010228 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x10010230 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
# oracle: known-model-bug mem:0x10010234 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (low word)
# oracle: known-model-bug mem:0x1001023c MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (new QNaN, FCSR.NAN2008 = 1): double 0x7ff80000_00000000; W5: the model still creates the legacy 0x7ff7ffff_ffffffff (high word)
.data
res: .space 784
.text
la $s7, res
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x3c300000
mthc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
add.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 0($s7)
sw $t1, 4($s7)
mfhc1 $t2, $f6
sw $t2, 8($s7)
li $t8, 1
ctc1 $t8, $31
add.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 12($s7)
sw $t1, 16($s7)
mfhc1 $t2, $f6
sw $t2, 20($s7)
li $t8, 2
ctc1 $t8, $31
add.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 24($s7)
sw $t1, 28($s7)
mfhc1 $t2, $f6
sw $t2, 32($s7)
li $t8, 3
ctc1 $t8, $31
add.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 36($s7)
sw $t1, 40($s7)
mfhc1 $t2, $f6
sw $t2, 44($s7)
li $t9, 0xffffffff
mtc1 $t9, $f2
li $t9, 0x7fefffff
mthc1 $t9, $f2
li $t9, 0xffffffff
mtc1 $t9, $f4
li $t9, 0x7fefffff
mthc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
add.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 48($s7)
sw $t1, 52($s7)
mfhc1 $t2, $f6
sw $t2, 56($s7)
li $t8, 1
ctc1 $t8, $31
add.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 60($s7)
sw $t1, 64($s7)
mfhc1 $t2, $f6
sw $t2, 68($s7)
li $t8, 2
ctc1 $t8, $31
add.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 72($s7)
sw $t1, 76($s7)
mfhc1 $t2, $f6
sw $t2, 80($s7)
li $t8, 3
ctc1 $t8, $31
add.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 84($s7)
sw $t1, 88($s7)
mfhc1 $t2, $f6
sw $t2, 92($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x7ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0xfff00000
mthc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
add.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 96($s7)
sw $t1, 100($s7)
mfhc1 $t2, $f6
sw $t2, 104($s7)
li $t8, 1
ctc1 $t8, $31
add.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 108($s7)
sw $t1, 112($s7)
mfhc1 $t2, $f6
sw $t2, 116($s7)
li $t8, 2
ctc1 $t8, $31
add.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 120($s7)
sw $t1, 124($s7)
mfhc1 $t2, $f6
sw $t2, 128($s7)
li $t8, 3
ctc1 $t8, $31
add.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 132($s7)
sw $t1, 136($s7)
mfhc1 $t2, $f6
sw $t2, 140($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x7ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x7ff00000
mthc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sub.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 144($s7)
sw $t1, 148($s7)
mfhc1 $t2, $f6
sw $t2, 152($s7)
li $t8, 1
ctc1 $t8, $31
sub.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 156($s7)
sw $t1, 160($s7)
mfhc1 $t2, $f6
sw $t2, 164($s7)
li $t8, 2
ctc1 $t8, $31
sub.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 168($s7)
sw $t1, 172($s7)
mfhc1 $t2, $f6
sw $t2, 176($s7)
li $t8, 3
ctc1 $t8, $31
sub.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 180($s7)
sw $t1, 184($s7)
mfhc1 $t2, $f6
sw $t2, 188($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x00100000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x3fe00000
mthc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
mul.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 192($s7)
sw $t1, 196($s7)
mfhc1 $t2, $f6
sw $t2, 200($s7)
li $t8, 1
ctc1 $t8, $31
mul.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 204($s7)
sw $t1, 208($s7)
mfhc1 $t2, $f6
sw $t2, 212($s7)
li $t8, 2
ctc1 $t8, $31
mul.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 216($s7)
sw $t1, 220($s7)
mfhc1 $t2, $f6
sw $t2, 224($s7)
li $t8, 3
ctc1 $t8, $31
mul.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 228($s7)
sw $t1, 232($s7)
mfhc1 $t2, $f6
sw $t2, 236($s7)
li $t9, 0x154ef7ac
mtc1 $t9, $f2
li $t9, 0x16687e92
mthc1 $t9, $f2
li $t9, 0x154ef7ac
mtc1 $t9, $f4
li $t9, 0x16687e92
mthc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
mul.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 240($s7)
sw $t1, 244($s7)
mfhc1 $t2, $f6
sw $t2, 248($s7)
li $t8, 1
ctc1 $t8, $31
mul.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 252($s7)
sw $t1, 256($s7)
mfhc1 $t2, $f6
sw $t2, 260($s7)
li $t8, 2
ctc1 $t8, $31
mul.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 264($s7)
sw $t1, 268($s7)
mfhc1 $t2, $f6
sw $t2, 272($s7)
li $t8, 3
ctc1 $t8, $31
mul.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 276($s7)
sw $t1, 280($s7)
mfhc1 $t2, $f6
sw $t2, 284($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x00000000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x7ff00000
mthc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
mul.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 288($s7)
sw $t1, 292($s7)
mfhc1 $t2, $f6
sw $t2, 296($s7)
li $t8, 1
ctc1 $t8, $31
mul.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 300($s7)
sw $t1, 304($s7)
mfhc1 $t2, $f6
sw $t2, 308($s7)
li $t8, 2
ctc1 $t8, $31
mul.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 312($s7)
sw $t1, 316($s7)
mfhc1 $t2, $f6
sw $t2, 320($s7)
li $t8, 3
ctc1 $t8, $31
mul.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 324($s7)
sw $t1, 328($s7)
mfhc1 $t2, $f6
sw $t2, 332($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x00000000
mthc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 336($s7)
sw $t1, 340($s7)
mfhc1 $t2, $f6
sw $t2, 344($s7)
li $t8, 1
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 348($s7)
sw $t1, 352($s7)
mfhc1 $t2, $f6
sw $t2, 356($s7)
li $t8, 2
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 360($s7)
sw $t1, 364($s7)
mfhc1 $t2, $f6
sw $t2, 368($s7)
li $t8, 3
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 372($s7)
sw $t1, 376($s7)
mfhc1 $t2, $f6
sw $t2, 380($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x00000000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x00000000
mthc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 384($s7)
sw $t1, 388($s7)
mfhc1 $t2, $f6
sw $t2, 392($s7)
li $t8, 1
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 396($s7)
sw $t1, 400($s7)
mfhc1 $t2, $f6
sw $t2, 404($s7)
li $t8, 2
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 408($s7)
sw $t1, 412($s7)
mfhc1 $t2, $f6
sw $t2, 416($s7)
li $t8, 3
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 420($s7)
sw $t1, 424($s7)
mfhc1 $t2, $f6
sw $t2, 428($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x40080000
mthc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 432($s7)
sw $t1, 436($s7)
mfhc1 $t2, $f6
sw $t2, 440($s7)
li $t8, 1
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 444($s7)
sw $t1, 448($s7)
mfhc1 $t2, $f6
sw $t2, 452($s7)
li $t8, 2
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 456($s7)
sw $t1, 460($s7)
mfhc1 $t2, $f6
sw $t2, 464($s7)
li $t8, 3
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 468($s7)
sw $t1, 472($s7)
mfhc1 $t2, $f6
sw $t2, 476($s7)
li $t9, 0xffffffff
mtc1 $t9, $f2
li $t9, 0x7fefffff
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x3fe00000
mthc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 480($s7)
sw $t1, 484($s7)
mfhc1 $t2, $f6
sw $t2, 488($s7)
li $t8, 1
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 492($s7)
sw $t1, 496($s7)
mfhc1 $t2, $f6
sw $t2, 500($s7)
li $t8, 2
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 504($s7)
sw $t1, 508($s7)
mfhc1 $t2, $f6
sw $t2, 512($s7)
li $t8, 3
ctc1 $t8, $31
div.d $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 516($s7)
sw $t1, 520($s7)
mfhc1 $t2, $f6
sw $t2, 524($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0xbff00000
mthc1 $t9, $f2
li $t8, 0
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 528($s7)
sw $t1, 532($s7)
mfhc1 $t2, $f6
sw $t2, 536($s7)
li $t8, 1
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 540($s7)
sw $t1, 544($s7)
mfhc1 $t2, $f6
sw $t2, 548($s7)
li $t8, 2
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 552($s7)
sw $t1, 556($s7)
mfhc1 $t2, $f6
sw $t2, 560($s7)
li $t8, 3
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 564($s7)
sw $t1, 568($s7)
mfhc1 $t2, $f6
sw $t2, 572($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40000000
mthc1 $t9, $f2
li $t8, 0
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 576($s7)
sw $t1, 580($s7)
mfhc1 $t2, $f6
sw $t2, 584($s7)
li $t8, 1
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 588($s7)
sw $t1, 592($s7)
mfhc1 $t2, $f6
sw $t2, 596($s7)
li $t8, 2
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 600($s7)
sw $t1, 604($s7)
mfhc1 $t2, $f6
sw $t2, 608($s7)
li $t8, 3
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 612($s7)
sw $t1, 616($s7)
mfhc1 $t2, $f6
sw $t2, 620($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40100000
mthc1 $t9, $f2
li $t8, 0
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 624($s7)
sw $t1, 628($s7)
mfhc1 $t2, $f6
sw $t2, 632($s7)
li $t8, 1
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 636($s7)
sw $t1, 640($s7)
mfhc1 $t2, $f6
sw $t2, 644($s7)
li $t8, 2
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 648($s7)
sw $t1, 652($s7)
mfhc1 $t2, $f6
sw $t2, 656($s7)
li $t8, 3
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 660($s7)
sw $t1, 664($s7)
mfhc1 $t2, $f6
sw $t2, 668($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x80000000
mthc1 $t9, $f2
li $t8, 0
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 672($s7)
sw $t1, 676($s7)
mfhc1 $t2, $f6
sw $t2, 680($s7)
li $t8, 1
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 684($s7)
sw $t1, 688($s7)
mfhc1 $t2, $f6
sw $t2, 692($s7)
li $t8, 2
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 696($s7)
sw $t1, 700($s7)
mfhc1 $t2, $f6
sw $t2, 704($s7)
li $t8, 3
ctc1 $t8, $31
sqrt.d $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 708($s7)
sw $t1, 712($s7)
mfhc1 $t2, $f6
sw $t2, 716($s7)
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
