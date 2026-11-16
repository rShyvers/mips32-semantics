# round/trunc/ceil/floor.w.d on 2.5 -2.5 1.5 -1.5 0.5 -0.5 3.7 -3.7 1e10 -1e10 +Inf QNaN 2^31 -2^31 (result word and FCSR).
# Out-of-range / NaN / Inf inputs give the invalid-operation result 0x7fffffff (legacy, Has2008=0) and Invalid; inexact results set Inexact.
# MD00086 Vol II-A Rev 6.06: ROUND.W.fmt p.342, TRUNC.W.fmt p.441, CEIL.W.fmt p.128, FLOOR.W.fmt p.186; MD00082 Vol I-A Rev 6.01 Table 6.3 p.82 (word fixed point: 0x7fffffff for a NaN / too-big operand).
# oracle: known-model-bug mem:0x10010120 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x10010128 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x10010130 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x10010138 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a number too small for a word converts to 0x80000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x10010160 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a NaN converts to 0x00000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x10010168 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a NaN converts to 0x00000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x10010170 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a NaN converts to 0x00000000; W5: the model still gives the legacy 0x7fffffff
# oracle: known-model-bug mem:0x10010178 MD00082 Vol I-A Rev 6.01 6.3.1.5 Table 6.3 p.82 (FCSR.NAN2008 = 1): a NaN converts to 0x00000000; W5: the model still gives the legacy 0x7fffffff
.data
res: .space 512
.text
la $s7, res
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x40040000
mthc1 $t9, $f0
ctc1 $zero, $31
round.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 0($s7)
sw $t1, 4($s7)
ctc1 $zero, $31
trunc.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 8($s7)
sw $t1, 12($s7)
ctc1 $zero, $31
ceil.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 16($s7)
sw $t1, 20($s7)
ctc1 $zero, $31
floor.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 24($s7)
sw $t1, 28($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0xc0040000
mthc1 $t9, $f0
ctc1 $zero, $31
round.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 32($s7)
sw $t1, 36($s7)
ctc1 $zero, $31
trunc.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 40($s7)
sw $t1, 44($s7)
ctc1 $zero, $31
ceil.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 48($s7)
sw $t1, 52($s7)
ctc1 $zero, $31
floor.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 56($s7)
sw $t1, 60($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x3ff80000
mthc1 $t9, $f0
ctc1 $zero, $31
round.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 64($s7)
sw $t1, 68($s7)
ctc1 $zero, $31
trunc.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 72($s7)
sw $t1, 76($s7)
ctc1 $zero, $31
ceil.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 80($s7)
sw $t1, 84($s7)
ctc1 $zero, $31
floor.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 88($s7)
sw $t1, 92($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0xbff80000
mthc1 $t9, $f0
ctc1 $zero, $31
round.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 96($s7)
sw $t1, 100($s7)
ctc1 $zero, $31
trunc.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 104($s7)
sw $t1, 108($s7)
ctc1 $zero, $31
ceil.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 112($s7)
sw $t1, 116($s7)
ctc1 $zero, $31
floor.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 120($s7)
sw $t1, 124($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x3fe00000
mthc1 $t9, $f0
ctc1 $zero, $31
round.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 128($s7)
sw $t1, 132($s7)
ctc1 $zero, $31
trunc.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 136($s7)
sw $t1, 140($s7)
ctc1 $zero, $31
ceil.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 144($s7)
sw $t1, 148($s7)
ctc1 $zero, $31
floor.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 152($s7)
sw $t1, 156($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0xbfe00000
mthc1 $t9, $f0
ctc1 $zero, $31
round.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 160($s7)
sw $t1, 164($s7)
ctc1 $zero, $31
trunc.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 168($s7)
sw $t1, 172($s7)
ctc1 $zero, $31
ceil.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 176($s7)
sw $t1, 180($s7)
ctc1 $zero, $31
floor.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 184($s7)
sw $t1, 188($s7)
li $t9, 0x9999999a
mtc1 $t9, $f0
li $t9, 0x400d9999
mthc1 $t9, $f0
ctc1 $zero, $31
round.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 192($s7)
sw $t1, 196($s7)
ctc1 $zero, $31
trunc.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 200($s7)
sw $t1, 204($s7)
ctc1 $zero, $31
ceil.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 208($s7)
sw $t1, 212($s7)
ctc1 $zero, $31
floor.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 216($s7)
sw $t1, 220($s7)
li $t9, 0x9999999a
mtc1 $t9, $f0
li $t9, 0xc00d9999
mthc1 $t9, $f0
ctc1 $zero, $31
round.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 224($s7)
sw $t1, 228($s7)
ctc1 $zero, $31
trunc.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 232($s7)
sw $t1, 236($s7)
ctc1 $zero, $31
ceil.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 240($s7)
sw $t1, 244($s7)
ctc1 $zero, $31
floor.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 248($s7)
sw $t1, 252($s7)
li $t9, 0x20000000
mtc1 $t9, $f0
li $t9, 0x4202a05f
mthc1 $t9, $f0
ctc1 $zero, $31
round.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 256($s7)
sw $t1, 260($s7)
ctc1 $zero, $31
trunc.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 264($s7)
sw $t1, 268($s7)
ctc1 $zero, $31
ceil.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 272($s7)
sw $t1, 276($s7)
ctc1 $zero, $31
floor.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 280($s7)
sw $t1, 284($s7)
li $t9, 0x20000000
mtc1 $t9, $f0
li $t9, 0xc202a05f
mthc1 $t9, $f0
ctc1 $zero, $31
round.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 288($s7)
sw $t1, 292($s7)
ctc1 $zero, $31
trunc.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 296($s7)
sw $t1, 300($s7)
ctc1 $zero, $31
ceil.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 304($s7)
sw $t1, 308($s7)
ctc1 $zero, $31
floor.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 312($s7)
sw $t1, 316($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x7ff00000
mthc1 $t9, $f0
ctc1 $zero, $31
round.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 320($s7)
sw $t1, 324($s7)
ctc1 $zero, $31
trunc.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 328($s7)
sw $t1, 332($s7)
ctc1 $zero, $31
ceil.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 336($s7)
sw $t1, 340($s7)
ctc1 $zero, $31
floor.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 344($s7)
sw $t1, 348($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x7ff80000
mthc1 $t9, $f0
ctc1 $zero, $31
round.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 352($s7)
sw $t1, 356($s7)
ctc1 $zero, $31
trunc.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 360($s7)
sw $t1, 364($s7)
ctc1 $zero, $31
ceil.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 368($s7)
sw $t1, 372($s7)
ctc1 $zero, $31
floor.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 376($s7)
sw $t1, 380($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x41e00000
mthc1 $t9, $f0
ctc1 $zero, $31
round.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 384($s7)
sw $t1, 388($s7)
ctc1 $zero, $31
trunc.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 392($s7)
sw $t1, 396($s7)
ctc1 $zero, $31
ceil.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 400($s7)
sw $t1, 404($s7)
ctc1 $zero, $31
floor.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 408($s7)
sw $t1, 412($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0xc1e00000
mthc1 $t9, $f0
ctc1 $zero, $31
round.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 416($s7)
sw $t1, 420($s7)
ctc1 $zero, $31
trunc.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 424($s7)
sw $t1, 428($s7)
ctc1 $zero, $31
ceil.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 432($s7)
sw $t1, 436($s7)
ctc1 $zero, $31
floor.w.d $f4, $f0
mfc1 $t0, $f4
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
sw $t0, 440($s7)
sw $t1, 444($s7)
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
