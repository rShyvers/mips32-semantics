# Randomised (seeded 500) madd/msub/nmadd/nmsub on .s over edge-value pools and random normals, in all four rounding modes: result bits + FCSR. No NaN operands (payload choice is unspecified).
# MD00082 Vol I-A Rev 6.01 sec 6.7.2 p.99-102, Table 6.14 p.100 (IEEE default results, flags, rounding modes); MD00086 Vol II-A Rev 6.06 ADD/SUB/MUL/DIV/SQRT.fmt, CVT/ROUND/TRUNC/CEIL/FLOOR.
.data
res: .space 1088
.text
la $s7, res
li $t9, 0xc3ca05af
mtc1 $t9, $f2
li $t9, 0x34000000
mtc1 $t9, $f4
li $t9, 0x1be69310
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 0($s7)
sw $t1, 4($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 8($s7)
sw $t1, 12($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 16($s7)
sw $t1, 20($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 24($s7)
sw $t1, 28($s7)
li $t9, 0x4b7fffff
mtc1 $t9, $f2
li $t9, 0x0299ecda
mtc1 $t9, $f4
li $t9, 0x7f7fffff
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 32($s7)
sw $t1, 36($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 40($s7)
sw $t1, 44($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 48($s7)
sw $t1, 52($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 56($s7)
sw $t1, 60($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x33800000
mtc1 $t9, $f4
li $t9, 0x40000000
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 64($s7)
sw $t1, 68($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 72($s7)
sw $t1, 76($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 80($s7)
sw $t1, 84($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 88($s7)
sw $t1, 92($s7)
li $t9, 0x3dcccccd
mtc1 $t9, $f2
li $t9, 0x40400000
mtc1 $t9, $f4
li $t9, 0x00800001
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 96($s7)
sw $t1, 100($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 104($s7)
sw $t1, 108($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 112($s7)
sw $t1, 116($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 120($s7)
sw $t1, 124($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x62ec218c
mtc1 $t9, $f4
li $t9, 0xc1dc5613
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 128($s7)
sw $t1, 132($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 136($s7)
sw $t1, 140($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 144($s7)
sw $t1, 148($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 152($s7)
sw $t1, 156($s7)
li $t9, 0xcebd1c4e
mtc1 $t9, $f2
li $t9, 0x47326e17
mtc1 $t9, $f4
li $t9, 0x4b7fffff
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 160($s7)
sw $t1, 164($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 168($s7)
sw $t1, 172($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 176($s7)
sw $t1, 180($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 184($s7)
sw $t1, 188($s7)
li $t9, 0xef5e3557
mtc1 $t9, $f2
li $t9, 0xc7eb5cc9
mtc1 $t9, $f4
li $t9, 0x6c78f1c1
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 192($s7)
sw $t1, 196($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 200($s7)
sw $t1, 204($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 208($s7)
sw $t1, 212($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 216($s7)
sw $t1, 220($s7)
li $t9, 0xbd221680
mtc1 $t9, $f2
li $t9, 0x3d5a3c1f
mtc1 $t9, $f4
li $t9, 0x80000001
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 224($s7)
sw $t1, 228($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 232($s7)
sw $t1, 236($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 240($s7)
sw $t1, 244($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 248($s7)
sw $t1, 252($s7)
li $t9, 0x97c49ee0
mtc1 $t9, $f2
li $t9, 0x4eec2368
mtc1 $t9, $f4
li $t9, 0x4aae6c0e
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 256($s7)
sw $t1, 260($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 264($s7)
sw $t1, 268($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 272($s7)
sw $t1, 276($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 280($s7)
sw $t1, 284($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40400000
mtc1 $t9, $f4
li $t9, 0x89d9babb
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 288($s7)
sw $t1, 292($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 296($s7)
sw $t1, 300($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 304($s7)
sw $t1, 308($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 312($s7)
sw $t1, 316($s7)
li $t9, 0x01000000
mtc1 $t9, $f2
li $t9, 0x7f7fffff
mtc1 $t9, $f4
li $t9, 0x4096681a
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 320($s7)
sw $t1, 324($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 328($s7)
sw $t1, 332($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 336($s7)
sw $t1, 340($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 344($s7)
sw $t1, 348($s7)
li $t9, 0x75929860
mtc1 $t9, $f2
li $t9, 0xc160b4f4
mtc1 $t9, $f4
li $t9, 0x00800001
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 352($s7)
sw $t1, 356($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 360($s7)
sw $t1, 364($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 368($s7)
sw $t1, 372($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 376($s7)
sw $t1, 380($s7)
li $t9, 0x40000000
mtc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0xb3bd1674
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 384($s7)
sw $t1, 388($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 392($s7)
sw $t1, 396($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 400($s7)
sw $t1, 404($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 408($s7)
sw $t1, 412($s7)
li $t9, 0x485f0881
mtc1 $t9, $f2
li $t9, 0x4b7fffff
mtc1 $t9, $f4
li $t9, 0xab5ce70b
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 416($s7)
sw $t1, 420($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 424($s7)
sw $t1, 428($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 432($s7)
sw $t1, 436($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 440($s7)
sw $t1, 444($s7)
li $t9, 0x7f7fffff
mtc1 $t9, $f2
li $t9, 0x80000000
mtc1 $t9, $f4
li $t9, 0xf8beb121
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 448($s7)
sw $t1, 452($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 456($s7)
sw $t1, 460($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 464($s7)
sw $t1, 468($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 472($s7)
sw $t1, 476($s7)
li $t9, 0xbfc7ace9
mtc1 $t9, $f2
li $t9, 0x561defa9
mtc1 $t9, $f4
li $t9, 0x007fffff
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 480($s7)
sw $t1, 484($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 488($s7)
sw $t1, 492($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 496($s7)
sw $t1, 500($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 504($s7)
sw $t1, 508($s7)
li $t9, 0xb3ae2a61
mtc1 $t9, $f2
li $t9, 0xfa5962aa
mtc1 $t9, $f4
li $t9, 0xac7501bc
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 512($s7)
sw $t1, 516($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 520($s7)
sw $t1, 524($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 528($s7)
sw $t1, 532($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 536($s7)
sw $t1, 540($s7)
li $t9, 0x3f000000
mtc1 $t9, $f2
li $t9, 0x7f7fffff
mtc1 $t9, $f4
li $t9, 0xb32335ae
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 544($s7)
sw $t1, 548($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 552($s7)
sw $t1, 556($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 560($s7)
sw $t1, 564($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 568($s7)
sw $t1, 572($s7)
li $t9, 0x34000000
mtc1 $t9, $f2
li $t9, 0x40400000
mtc1 $t9, $f4
li $t9, 0x3f000000
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 576($s7)
sw $t1, 580($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 584($s7)
sw $t1, 588($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 592($s7)
sw $t1, 596($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 600($s7)
sw $t1, 604($s7)
li $t9, 0x57c33015
mtc1 $t9, $f2
li $t9, 0x33800000
mtc1 $t9, $f4
li $t9, 0x7e800000
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 608($s7)
sw $t1, 612($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 616($s7)
sw $t1, 620($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 624($s7)
sw $t1, 628($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 632($s7)
sw $t1, 636($s7)
li $t9, 0xbc3ba445
mtc1 $t9, $f2
li $t9, 0x007fffff
mtc1 $t9, $f4
li $t9, 0x43057e11
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 640($s7)
sw $t1, 644($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 648($s7)
sw $t1, 652($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 656($s7)
sw $t1, 660($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 664($s7)
sw $t1, 668($s7)
li $t9, 0x00800001
mtc1 $t9, $f2
li $t9, 0x80000001
mtc1 $t9, $f4
li $t9, 0x3f800000
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 672($s7)
sw $t1, 676($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 680($s7)
sw $t1, 684($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 688($s7)
sw $t1, 692($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 696($s7)
sw $t1, 700($s7)
li $t9, 0x33800000
mtc1 $t9, $f2
li $t9, 0x47d9eba7
mtc1 $t9, $f4
li $t9, 0xff800000
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 704($s7)
sw $t1, 708($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 712($s7)
sw $t1, 716($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 720($s7)
sw $t1, 724($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 728($s7)
sw $t1, 732($s7)
li $t9, 0x390bd41c
mtc1 $t9, $f2
li $t9, 0x80000000
mtc1 $t9, $f4
li $t9, 0x00000000
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 736($s7)
sw $t1, 740($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 744($s7)
sw $t1, 748($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 752($s7)
sw $t1, 756($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 760($s7)
sw $t1, 764($s7)
li $t9, 0x4b7fffff
mtc1 $t9, $f2
li $t9, 0x00000001
mtc1 $t9, $f4
li $t9, 0xc408f324
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 768($s7)
sw $t1, 772($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 776($s7)
sw $t1, 780($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 784($s7)
sw $t1, 788($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 792($s7)
sw $t1, 796($s7)
li $t9, 0x69183ab8
mtc1 $t9, $f2
li $t9, 0x331007d7
mtc1 $t9, $f4
li $t9, 0x00800001
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 800($s7)
sw $t1, 804($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 808($s7)
sw $t1, 812($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 816($s7)
sw $t1, 820($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 824($s7)
sw $t1, 828($s7)
li $t9, 0x7e800000
mtc1 $t9, $f2
li $t9, 0x70e16e1a
mtc1 $t9, $f4
li $t9, 0xff800000
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 832($s7)
sw $t1, 836($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 840($s7)
sw $t1, 844($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 848($s7)
sw $t1, 852($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 856($s7)
sw $t1, 860($s7)
li $t9, 0xb32b0727
mtc1 $t9, $f2
li $t9, 0x2b7da0c0
mtc1 $t9, $f4
li $t9, 0x4b000000
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 864($s7)
sw $t1, 868($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 872($s7)
sw $t1, 876($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 880($s7)
sw $t1, 884($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 888($s7)
sw $t1, 892($s7)
li $t9, 0xacc3f910
mtc1 $t9, $f2
li $t9, 0x1f622a3f
mtc1 $t9, $f4
li $t9, 0x45ae582f
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 896($s7)
sw $t1, 900($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 904($s7)
sw $t1, 908($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 912($s7)
sw $t1, 916($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 920($s7)
sw $t1, 924($s7)
li $t9, 0x80000001
mtc1 $t9, $f2
li $t9, 0xb4c65c6a
mtc1 $t9, $f4
li $t9, 0x3f000000
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 928($s7)
sw $t1, 932($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 936($s7)
sw $t1, 940($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 944($s7)
sw $t1, 948($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 952($s7)
sw $t1, 956($s7)
li $t9, 0x0f721115
mtc1 $t9, $f2
li $t9, 0xdf6dcc8a
mtc1 $t9, $f4
li $t9, 0x4772b765
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 960($s7)
sw $t1, 964($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 968($s7)
sw $t1, 972($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 976($s7)
sw $t1, 980($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 984($s7)
sw $t1, 988($s7)
li $t9, 0x00800001
mtc1 $t9, $f2
li $t9, 0xec1a5e09
mtc1 $t9, $f4
li $t9, 0x3dcccccd
mtc1 $t9, $f8
li $t8, 0
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 992($s7)
sw $t1, 996($s7)
li $t8, 1
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1000($s7)
sw $t1, 1004($s7)
li $t8, 2
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1008($s7)
sw $t1, 1012($s7)
li $t8, 3
ctc1 $t8, $31
madd.s $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1016($s7)
sw $t1, 1020($s7)
li $v0, 10
syscall
