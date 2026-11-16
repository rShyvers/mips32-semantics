# Randomised (seeded 301) cvtw/rndround/rndtrunc/rndceil/rndfloor on .s over edge-value pools and random normals, in all four rounding modes: result bits + FCSR. No NaN operands (payload choice is unspecified).
# MD00082 Vol I-A Rev 6.01 sec 6.7.2 p.99-102, Table 6.14 p.100 (IEEE default results, flags, rounding modes); MD00086 Vol II-A Rev 6.06 ADD/SUB/MUL/DIV/SQRT.fmt, CVT/ROUND/TRUNC/CEIL/FLOOR.
# oracle: known-model-bug mem:0x10010000 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x10010008 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x10010010 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x10010018 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x100103c0 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x100103c8 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x100103d0 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x100103d8 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x100104e0 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x100104e8 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x100104f0 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x100104f8 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
.data
res: .space 1344
.text
la $s7, res
li $t9, 0xff800000
mtc1 $t9, $f2
li $t9, 0x9ef98a4e
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 0($s7)
sw $t1, 4($s7)
li $t8, 1
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 8($s7)
sw $t1, 12($s7)
li $t8, 2
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 16($s7)
sw $t1, 20($s7)
li $t8, 3
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 24($s7)
sw $t1, 28($s7)
li $t9, 0x00000001
mtc1 $t9, $f2
li $t9, 0x0ce80da8
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 32($s7)
sw $t1, 36($s7)
li $t8, 1
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 40($s7)
sw $t1, 44($s7)
li $t8, 2
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 48($s7)
sw $t1, 52($s7)
li $t8, 3
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 56($s7)
sw $t1, 60($s7)
li $t9, 0xc66c1149
mtc1 $t9, $f2
li $t9, 0x46553ac0
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 64($s7)
sw $t1, 68($s7)
li $t8, 1
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 72($s7)
sw $t1, 76($s7)
li $t8, 2
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 80($s7)
sw $t1, 84($s7)
li $t8, 3
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 88($s7)
sw $t1, 92($s7)
li $t9, 0x4b000000
mtc1 $t9, $f2
li $t9, 0xc11c1bc9
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 96($s7)
sw $t1, 100($s7)
li $t8, 1
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 104($s7)
sw $t1, 108($s7)
li $t8, 2
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 112($s7)
sw $t1, 116($s7)
li $t8, 3
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 120($s7)
sw $t1, 124($s7)
li $t9, 0x4afbbf9e
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 128($s7)
sw $t1, 132($s7)
li $t8, 1
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 136($s7)
sw $t1, 140($s7)
li $t8, 2
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 144($s7)
sw $t1, 148($s7)
li $t8, 3
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 152($s7)
sw $t1, 156($s7)
li $t9, 0x00800001
mtc1 $t9, $f2
li $t9, 0x4b7fffff
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 160($s7)
sw $t1, 164($s7)
li $t8, 1
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 168($s7)
sw $t1, 172($s7)
li $t8, 2
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 176($s7)
sw $t1, 180($s7)
li $t8, 3
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 184($s7)
sw $t1, 188($s7)
li $t9, 0xbc04cc6b
mtc1 $t9, $f2
li $t9, 0x40400000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 192($s7)
sw $t1, 196($s7)
li $t8, 1
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 200($s7)
sw $t1, 204($s7)
li $t8, 2
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 208($s7)
sw $t1, 212($s7)
li $t8, 3
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 216($s7)
sw $t1, 220($s7)
li $t9, 0x7f800000
mtc1 $t9, $f2
li $t9, 0xf67c19b9
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 224($s7)
sw $t1, 228($s7)
li $t8, 1
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 232($s7)
sw $t1, 236($s7)
li $t8, 2
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 240($s7)
sw $t1, 244($s7)
li $t8, 3
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 248($s7)
sw $t1, 252($s7)
li $t9, 0x80ed192a
mtc1 $t9, $f2
li $t9, 0x24fa9cd2
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 256($s7)
sw $t1, 260($s7)
li $t8, 1
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 264($s7)
sw $t1, 268($s7)
li $t8, 2
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 272($s7)
sw $t1, 276($s7)
li $t8, 3
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 280($s7)
sw $t1, 284($s7)
li $t9, 0xa7c94793
mtc1 $t9, $f2
li $t9, 0x3f000000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 288($s7)
sw $t1, 292($s7)
li $t8, 1
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 296($s7)
sw $t1, 300($s7)
li $t8, 2
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 304($s7)
sw $t1, 308($s7)
li $t8, 3
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 312($s7)
sw $t1, 316($s7)
li $t9, 0x40000000
mtc1 $t9, $f2
li $t9, 0x4db29e53
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 320($s7)
sw $t1, 324($s7)
li $t8, 1
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 328($s7)
sw $t1, 332($s7)
li $t8, 2
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 336($s7)
sw $t1, 340($s7)
li $t8, 3
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 344($s7)
sw $t1, 348($s7)
li $t9, 0x40e3ca98
mtc1 $t9, $f2
li $t9, 0x33800000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 352($s7)
sw $t1, 356($s7)
li $t8, 1
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 360($s7)
sw $t1, 364($s7)
li $t8, 2
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 368($s7)
sw $t1, 372($s7)
li $t8, 3
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 376($s7)
sw $t1, 380($s7)
li $t9, 0x00800000
mtc1 $t9, $f2
li $t9, 0xdc4f67f0
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 384($s7)
sw $t1, 388($s7)
li $t8, 1
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 392($s7)
sw $t1, 396($s7)
li $t8, 2
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 400($s7)
sw $t1, 404($s7)
li $t8, 3
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 408($s7)
sw $t1, 412($s7)
li $t9, 0x33800000
mtc1 $t9, $f2
li $t9, 0x00800001
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 416($s7)
sw $t1, 420($s7)
li $t8, 1
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 424($s7)
sw $t1, 428($s7)
li $t8, 2
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 432($s7)
sw $t1, 436($s7)
li $t8, 3
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 440($s7)
sw $t1, 444($s7)
li $t9, 0x29a57127
mtc1 $t9, $f2
li $t9, 0x80000001
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 448($s7)
sw $t1, 452($s7)
li $t8, 1
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 456($s7)
sw $t1, 460($s7)
li $t8, 2
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 464($s7)
sw $t1, 468($s7)
li $t8, 3
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 472($s7)
sw $t1, 476($s7)
li $t9, 0x40400000
mtc1 $t9, $f2
li $t9, 0x34000000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 480($s7)
sw $t1, 484($s7)
li $t8, 1
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 488($s7)
sw $t1, 492($s7)
li $t8, 2
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 496($s7)
sw $t1, 500($s7)
li $t8, 3
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 504($s7)
sw $t1, 508($s7)
li $t9, 0x34000000
mtc1 $t9, $f2
li $t9, 0x564d479c
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 512($s7)
sw $t1, 516($s7)
li $t8, 1
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 520($s7)
sw $t1, 524($s7)
li $t8, 2
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 528($s7)
sw $t1, 532($s7)
li $t8, 3
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 536($s7)
sw $t1, 540($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0xeb9f0ee8
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 544($s7)
sw $t1, 548($s7)
li $t8, 1
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 552($s7)
sw $t1, 556($s7)
li $t8, 2
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 560($s7)
sw $t1, 564($s7)
li $t8, 3
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 568($s7)
sw $t1, 572($s7)
li $t9, 0xc9e2f139
mtc1 $t9, $f2
li $t9, 0x00000001
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 576($s7)
sw $t1, 580($s7)
li $t8, 1
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 584($s7)
sw $t1, 588($s7)
li $t8, 2
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 592($s7)
sw $t1, 596($s7)
li $t8, 3
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 600($s7)
sw $t1, 604($s7)
li $t9, 0x3df70b89
mtc1 $t9, $f2
li $t9, 0x7f7fffff
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 608($s7)
sw $t1, 612($s7)
li $t8, 1
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 616($s7)
sw $t1, 620($s7)
li $t8, 2
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 624($s7)
sw $t1, 628($s7)
li $t8, 3
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 632($s7)
sw $t1, 636($s7)
li $t9, 0x077a1053
mtc1 $t9, $f2
li $t9, 0x7f7fffff
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 640($s7)
sw $t1, 644($s7)
li $t8, 1
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 648($s7)
sw $t1, 652($s7)
li $t8, 2
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 656($s7)
sw $t1, 660($s7)
li $t8, 3
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 664($s7)
sw $t1, 668($s7)
li $t9, 0xcc04a599
mtc1 $t9, $f2
li $t9, 0xbb101cac
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 672($s7)
sw $t1, 676($s7)
li $t8, 1
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 680($s7)
sw $t1, 684($s7)
li $t8, 2
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 688($s7)
sw $t1, 692($s7)
li $t8, 3
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 696($s7)
sw $t1, 700($s7)
li $t9, 0x3cd6a264
mtc1 $t9, $f2
li $t9, 0x0e98010c
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 704($s7)
sw $t1, 708($s7)
li $t8, 1
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 712($s7)
sw $t1, 716($s7)
li $t8, 2
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 720($s7)
sw $t1, 724($s7)
li $t8, 3
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 728($s7)
sw $t1, 732($s7)
li $t9, 0xa8918341
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 736($s7)
sw $t1, 740($s7)
li $t8, 1
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 744($s7)
sw $t1, 748($s7)
li $t8, 2
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 752($s7)
sw $t1, 756($s7)
li $t8, 3
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 760($s7)
sw $t1, 764($s7)
li $t9, 0x047a468f
mtc1 $t9, $f2
li $t9, 0x00000001
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 768($s7)
sw $t1, 772($s7)
li $t8, 1
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 776($s7)
sw $t1, 780($s7)
li $t8, 2
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 784($s7)
sw $t1, 788($s7)
li $t8, 3
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 792($s7)
sw $t1, 796($s7)
li $t9, 0x40400000
mtc1 $t9, $f2
li $t9, 0x3dcccccd
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 800($s7)
sw $t1, 804($s7)
li $t8, 1
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 808($s7)
sw $t1, 812($s7)
li $t8, 2
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 816($s7)
sw $t1, 820($s7)
li $t8, 3
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 824($s7)
sw $t1, 828($s7)
li $t9, 0x80000000
mtc1 $t9, $f2
li $t9, 0xc115000c
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 832($s7)
sw $t1, 836($s7)
li $t8, 1
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 840($s7)
sw $t1, 844($s7)
li $t8, 2
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 848($s7)
sw $t1, 852($s7)
li $t8, 3
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 856($s7)
sw $t1, 860($s7)
li $t9, 0x3dcccccd
mtc1 $t9, $f2
li $t9, 0x4b7fffff
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 864($s7)
sw $t1, 868($s7)
li $t8, 1
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 872($s7)
sw $t1, 876($s7)
li $t8, 2
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 880($s7)
sw $t1, 884($s7)
li $t8, 3
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 888($s7)
sw $t1, 892($s7)
li $t9, 0x33800000
mtc1 $t9, $f2
li $t9, 0xb3f59200
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 896($s7)
sw $t1, 900($s7)
li $t8, 1
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 904($s7)
sw $t1, 908($s7)
li $t8, 2
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 912($s7)
sw $t1, 916($s7)
li $t8, 3
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 920($s7)
sw $t1, 924($s7)
li $t9, 0xc7e9e9f9
mtc1 $t9, $f2
li $t9, 0xc0928c34
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 928($s7)
sw $t1, 932($s7)
li $t8, 1
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 936($s7)
sw $t1, 940($s7)
li $t8, 2
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 944($s7)
sw $t1, 948($s7)
li $t8, 3
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 952($s7)
sw $t1, 956($s7)
li $t9, 0xff800000
mtc1 $t9, $f2
li $t9, 0x03a74b4c
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 960($s7)
sw $t1, 964($s7)
li $t8, 1
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 968($s7)
sw $t1, 972($s7)
li $t8, 2
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 976($s7)
sw $t1, 980($s7)
li $t8, 3
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 984($s7)
sw $t1, 988($s7)
li $t9, 0x00800001
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 992($s7)
sw $t1, 996($s7)
li $t8, 1
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1000($s7)
sw $t1, 1004($s7)
li $t8, 2
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1008($s7)
sw $t1, 1012($s7)
li $t8, 3
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1016($s7)
sw $t1, 1020($s7)
li $t9, 0xcc963ef3
mtc1 $t9, $f2
li $t9, 0x00800001
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1024($s7)
sw $t1, 1028($s7)
li $t8, 1
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1032($s7)
sw $t1, 1036($s7)
li $t8, 2
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1040($s7)
sw $t1, 1044($s7)
li $t8, 3
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1048($s7)
sw $t1, 1052($s7)
li $t9, 0xc4beaa06
mtc1 $t9, $f2
li $t9, 0xff800000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1056($s7)
sw $t1, 1060($s7)
li $t8, 1
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1064($s7)
sw $t1, 1068($s7)
li $t8, 2
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1072($s7)
sw $t1, 1076($s7)
li $t8, 3
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1080($s7)
sw $t1, 1084($s7)
li $t9, 0x477d2a73
mtc1 $t9, $f2
li $t9, 0xbfbfb8ef
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1088($s7)
sw $t1, 1092($s7)
li $t8, 1
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1096($s7)
sw $t1, 1100($s7)
li $t8, 2
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1104($s7)
sw $t1, 1108($s7)
li $t8, 3
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1112($s7)
sw $t1, 1116($s7)
li $t9, 0x33800000
mtc1 $t9, $f2
li $t9, 0xbdc48733
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1120($s7)
sw $t1, 1124($s7)
li $t8, 1
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1128($s7)
sw $t1, 1132($s7)
li $t8, 2
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1136($s7)
sw $t1, 1140($s7)
li $t8, 3
ctc1 $t8, $31
cvt.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1144($s7)
sw $t1, 1148($s7)
li $t9, 0x7f7fffff
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1152($s7)
sw $t1, 1156($s7)
li $t8, 1
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1160($s7)
sw $t1, 1164($s7)
li $t8, 2
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1168($s7)
sw $t1, 1172($s7)
li $t8, 3
ctc1 $t8, $31
round.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1176($s7)
sw $t1, 1180($s7)
li $t9, 0x4e6efb05
mtc1 $t9, $f2
li $t9, 0xaf28bb66
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1184($s7)
sw $t1, 1188($s7)
li $t8, 1
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1192($s7)
sw $t1, 1196($s7)
li $t8, 2
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1200($s7)
sw $t1, 1204($s7)
li $t8, 3
ctc1 $t8, $31
trunc.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1208($s7)
sw $t1, 1212($s7)
li $t9, 0x00800000
mtc1 $t9, $f2
li $t9, 0x61944338
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1216($s7)
sw $t1, 1220($s7)
li $t8, 1
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1224($s7)
sw $t1, 1228($s7)
li $t8, 2
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1232($s7)
sw $t1, 1236($s7)
li $t8, 3
ctc1 $t8, $31
ceil.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1240($s7)
sw $t1, 1244($s7)
li $t9, 0xf23fd74d
mtc1 $t9, $f2
li $t9, 0x007fffff
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1248($s7)
sw $t1, 1252($s7)
li $t8, 1
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1256($s7)
sw $t1, 1260($s7)
li $t8, 2
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1264($s7)
sw $t1, 1268($s7)
li $t8, 3
ctc1 $t8, $31
floor.w.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 1272($s7)
sw $t1, 1276($s7)
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
