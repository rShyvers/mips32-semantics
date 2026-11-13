# Randomised (seeded 101) add/sub/mul/div/sqrt on .s over edge-value pools and random normals, in all four rounding modes: result bits + FCSR. No NaN operands (payload choice is unspecified).
# MD00082 Vol I-A Rev 6.01 sec 6.7.2 p.99-102, Table 6.14 p.100 (IEEE default results, flags, rounding modes); MD00086 Vol II-A Rev 6.06 ADD/SUB/MUL/DIV/SQRT.fmt, CVT/ROUND/TRUNC/CEIL/FLOOR.
.data
res: .space 1344
.text
la $s7, res
li $t9, 0x74fb8d59
mtc1 $t9, $f2
li $t9, 0x3c0635ef
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 0($s7)
sw $t1, 4($s7)
li $t8, 1
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 8($s7)
sw $t1, 12($s7)
li $t8, 2
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 16($s7)
sw $t1, 20($s7)
li $t8, 3
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 24($s7)
sw $t1, 28($s7)
li $t9, 0xa53e23ab
mtc1 $t9, $f2
li $t9, 0x2afc4d33
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 32($s7)
sw $t1, 36($s7)
li $t8, 1
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 40($s7)
sw $t1, 44($s7)
li $t8, 2
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 48($s7)
sw $t1, 52($s7)
li $t8, 3
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 56($s7)
sw $t1, 60($s7)
li $t9, 0x3dcccccd
mtc1 $t9, $f2
li $t9, 0x7f800000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 64($s7)
sw $t1, 68($s7)
li $t8, 1
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 72($s7)
sw $t1, 76($s7)
li $t8, 2
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 80($s7)
sw $t1, 84($s7)
li $t8, 3
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 88($s7)
sw $t1, 92($s7)
li $t9, 0x00800001
mtc1 $t9, $f2
li $t9, 0x7f7fffff
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 96($s7)
sw $t1, 100($s7)
li $t8, 1
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 104($s7)
sw $t1, 108($s7)
li $t8, 2
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 112($s7)
sw $t1, 116($s7)
li $t8, 3
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 120($s7)
sw $t1, 124($s7)
li $t9, 0xff7fffff
mtc1 $t9, $f2
li $t9, 0x3dcccccd
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 128($s7)
sw $t1, 132($s7)
li $t8, 1
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 136($s7)
sw $t1, 140($s7)
li $t8, 2
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 144($s7)
sw $t1, 148($s7)
li $t8, 3
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 152($s7)
sw $t1, 156($s7)
li $t9, 0xd7aa0d52
mtc1 $t9, $f2
li $t9, 0xa2b283a8
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 160($s7)
sw $t1, 164($s7)
li $t8, 1
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 168($s7)
sw $t1, 172($s7)
li $t8, 2
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 176($s7)
sw $t1, 180($s7)
li $t8, 3
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 184($s7)
sw $t1, 188($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7e800000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 192($s7)
sw $t1, 196($s7)
li $t8, 1
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 200($s7)
sw $t1, 204($s7)
li $t8, 2
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 208($s7)
sw $t1, 212($s7)
li $t8, 3
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 216($s7)
sw $t1, 220($s7)
li $t9, 0x7f800000
mtc1 $t9, $f2
li $t9, 0xbf800000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 224($s7)
sw $t1, 228($s7)
li $t8, 1
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 232($s7)
sw $t1, 236($s7)
li $t8, 2
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 240($s7)
sw $t1, 244($s7)
li $t8, 3
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 248($s7)
sw $t1, 252($s7)
li $t9, 0x5aae07c8
mtc1 $t9, $f2
li $t9, 0x4b7fffff
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 256($s7)
sw $t1, 260($s7)
li $t8, 1
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 264($s7)
sw $t1, 268($s7)
li $t8, 2
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 272($s7)
sw $t1, 276($s7)
li $t8, 3
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 280($s7)
sw $t1, 284($s7)
li $t9, 0x37a38d1c
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 288($s7)
sw $t1, 292($s7)
li $t8, 1
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 296($s7)
sw $t1, 300($s7)
li $t8, 2
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 304($s7)
sw $t1, 308($s7)
li $t8, 3
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 312($s7)
sw $t1, 316($s7)
li $t9, 0xea2e6fb7
mtc1 $t9, $f2
li $t9, 0xc1154a52
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 320($s7)
sw $t1, 324($s7)
li $t8, 1
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 328($s7)
sw $t1, 332($s7)
li $t8, 2
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 336($s7)
sw $t1, 340($s7)
li $t8, 3
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 344($s7)
sw $t1, 348($s7)
li $t9, 0xbbef22af
mtc1 $t9, $f2
li $t9, 0xc2d77b80
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 352($s7)
sw $t1, 356($s7)
li $t8, 1
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 360($s7)
sw $t1, 364($s7)
li $t8, 2
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 368($s7)
sw $t1, 372($s7)
li $t8, 3
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 376($s7)
sw $t1, 380($s7)
li $t9, 0x3349afb9
mtc1 $t9, $f2
li $t9, 0x01000000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 384($s7)
sw $t1, 388($s7)
li $t8, 1
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 392($s7)
sw $t1, 396($s7)
li $t8, 2
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 400($s7)
sw $t1, 404($s7)
li $t8, 3
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 408($s7)
sw $t1, 412($s7)
li $t9, 0x47da552e
mtc1 $t9, $f2
li $t9, 0xe83af5a2
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 416($s7)
sw $t1, 420($s7)
li $t8, 1
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 424($s7)
sw $t1, 428($s7)
li $t8, 2
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 432($s7)
sw $t1, 436($s7)
li $t8, 3
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 440($s7)
sw $t1, 444($s7)
li $t9, 0xe599b5d0
mtc1 $t9, $f2
li $t9, 0xc6b92622
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 448($s7)
sw $t1, 452($s7)
li $t8, 1
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 456($s7)
sw $t1, 460($s7)
li $t8, 2
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 464($s7)
sw $t1, 468($s7)
li $t8, 3
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 472($s7)
sw $t1, 476($s7)
li $t9, 0x40000000
mtc1 $t9, $f2
li $t9, 0x3e08a591
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 480($s7)
sw $t1, 484($s7)
li $t8, 1
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 488($s7)
sw $t1, 492($s7)
li $t8, 2
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 496($s7)
sw $t1, 500($s7)
li $t8, 3
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 504($s7)
sw $t1, 508($s7)
li $t9, 0xad3b4413
mtc1 $t9, $f2
li $t9, 0x007fffff
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 512($s7)
sw $t1, 516($s7)
li $t8, 1
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 520($s7)
sw $t1, 524($s7)
li $t8, 2
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 528($s7)
sw $t1, 532($s7)
li $t8, 3
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 536($s7)
sw $t1, 540($s7)
li $t9, 0x40000000
mtc1 $t9, $f2
li $t9, 0x3dcccccd
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 544($s7)
sw $t1, 548($s7)
li $t8, 1
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 552($s7)
sw $t1, 556($s7)
li $t8, 2
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 560($s7)
sw $t1, 564($s7)
li $t8, 3
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 568($s7)
sw $t1, 572($s7)
li $t9, 0x00800001
mtc1 $t9, $f2
li $t9, 0x007fffff
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 576($s7)
sw $t1, 580($s7)
li $t8, 1
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 584($s7)
sw $t1, 588($s7)
li $t8, 2
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 592($s7)
sw $t1, 596($s7)
li $t8, 3
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 600($s7)
sw $t1, 604($s7)
li $t9, 0x34000000
mtc1 $t9, $f2
li $t9, 0x33800000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 608($s7)
sw $t1, 612($s7)
li $t8, 1
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 616($s7)
sw $t1, 620($s7)
li $t8, 2
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 624($s7)
sw $t1, 628($s7)
li $t8, 3
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 632($s7)
sw $t1, 636($s7)
li $t9, 0x672b11a3
mtc1 $t9, $f2
li $t9, 0x007fffff
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 640($s7)
sw $t1, 644($s7)
li $t8, 1
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 648($s7)
sw $t1, 652($s7)
li $t8, 2
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 656($s7)
sw $t1, 660($s7)
li $t8, 3
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 664($s7)
sw $t1, 668($s7)
li $t9, 0xcc448642
mtc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 672($s7)
sw $t1, 676($s7)
li $t8, 1
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 680($s7)
sw $t1, 684($s7)
li $t8, 2
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 688($s7)
sw $t1, 692($s7)
li $t8, 3
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 696($s7)
sw $t1, 700($s7)
li $t9, 0x7e800000
mtc1 $t9, $f2
li $t9, 0x7f7fffff
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 704($s7)
sw $t1, 708($s7)
li $t8, 1
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 712($s7)
sw $t1, 716($s7)
li $t8, 2
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 720($s7)
sw $t1, 724($s7)
li $t8, 3
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 728($s7)
sw $t1, 732($s7)
li $t9, 0x9cc217df
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 736($s7)
sw $t1, 740($s7)
li $t8, 1
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 744($s7)
sw $t1, 748($s7)
li $t8, 2
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 752($s7)
sw $t1, 756($s7)
li $t8, 3
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 760($s7)
sw $t1, 764($s7)
li $t9, 0xbf800000
mtc1 $t9, $f2
li $t9, 0x7f800000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 768($s7)
sw $t1, 772($s7)
li $t8, 1
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 776($s7)
sw $t1, 780($s7)
li $t8, 2
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 784($s7)
sw $t1, 788($s7)
li $t8, 3
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 792($s7)
sw $t1, 796($s7)
li $t9, 0xe9aea315
mtc1 $t9, $f2
li $t9, 0xc69abe06
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 800($s7)
sw $t1, 804($s7)
li $t8, 1
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 808($s7)
sw $t1, 812($s7)
li $t8, 2
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 816($s7)
sw $t1, 820($s7)
li $t8, 3
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 824($s7)
sw $t1, 828($s7)
li $t9, 0x4b000000
mtc1 $t9, $f2
li $t9, 0x7e800000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 832($s7)
sw $t1, 836($s7)
li $t8, 1
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 840($s7)
sw $t1, 844($s7)
li $t8, 2
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 848($s7)
sw $t1, 852($s7)
li $t8, 3
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 856($s7)
sw $t1, 860($s7)
li $t9, 0x7137b22f
mtc1 $t9, $f2
li $t9, 0x00800000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 864($s7)
sw $t1, 868($s7)
li $t8, 1
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 872($s7)
sw $t1, 876($s7)
li $t8, 2
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 880($s7)
sw $t1, 884($s7)
li $t8, 3
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 888($s7)
sw $t1, 892($s7)
li $t9, 0x4b7fffff
mtc1 $t9, $f2
li $t9, 0xce382955
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 896($s7)
sw $t1, 900($s7)
li $t8, 1
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 904($s7)
sw $t1, 908($s7)
li $t8, 2
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 912($s7)
sw $t1, 916($s7)
li $t8, 3
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 920($s7)
sw $t1, 924($s7)
li $t9, 0x475aedc4
mtc1 $t9, $f2
li $t9, 0x80000000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 928($s7)
sw $t1, 932($s7)
li $t8, 1
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 936($s7)
sw $t1, 940($s7)
li $t8, 2
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 944($s7)
sw $t1, 948($s7)
li $t8, 3
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 952($s7)
sw $t1, 956($s7)
li $t9, 0xcfeb83a3
mtc1 $t9, $f2
li $t9, 0xff7fffff
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 960($s7)
sw $t1, 964($s7)
li $t8, 1
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 968($s7)
sw $t1, 972($s7)
li $t8, 2
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 976($s7)
sw $t1, 980($s7)
li $t8, 3
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 984($s7)
sw $t1, 988($s7)
li $t9, 0xcf7a2a16
mtc1 $t9, $f2
li $t9, 0x34000000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 992($s7)
sw $t1, 996($s7)
li $t8, 1
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1000($s7)
sw $t1, 1004($s7)
li $t8, 2
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1008($s7)
sw $t1, 1012($s7)
li $t8, 3
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1016($s7)
sw $t1, 1020($s7)
li $t9, 0x007fffff
mtc1 $t9, $f2
li $t9, 0x588b05f0
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1024($s7)
sw $t1, 1028($s7)
li $t8, 1
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1032($s7)
sw $t1, 1036($s7)
li $t8, 2
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1040($s7)
sw $t1, 1044($s7)
li $t8, 3
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1048($s7)
sw $t1, 1052($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x01000000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1056($s7)
sw $t1, 1060($s7)
li $t8, 1
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1064($s7)
sw $t1, 1068($s7)
li $t8, 2
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1072($s7)
sw $t1, 1076($s7)
li $t8, 3
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1080($s7)
sw $t1, 1084($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3dcccccd
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1088($s7)
sw $t1, 1092($s7)
li $t8, 1
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1096($s7)
sw $t1, 1100($s7)
li $t8, 2
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1104($s7)
sw $t1, 1108($s7)
li $t8, 3
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1112($s7)
sw $t1, 1116($s7)
li $t9, 0xb8535bf7
mtc1 $t9, $f2
li $t9, 0x4b7fffff
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1120($s7)
sw $t1, 1124($s7)
li $t8, 1
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1128($s7)
sw $t1, 1132($s7)
li $t8, 2
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1136($s7)
sw $t1, 1140($s7)
li $t8, 3
ctc1 $t8, $31
add.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1144($s7)
sw $t1, 1148($s7)
li $t9, 0x80000000
mtc1 $t9, $f2
li $t9, 0xc2f88f78
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1152($s7)
sw $t1, 1156($s7)
li $t8, 1
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1160($s7)
sw $t1, 1164($s7)
li $t8, 2
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1168($s7)
sw $t1, 1172($s7)
li $t8, 3
ctc1 $t8, $31
sub.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1176($s7)
sw $t1, 1180($s7)
li $t9, 0x3f000000
mtc1 $t9, $f2
li $t9, 0x4ef72ce3
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1184($s7)
sw $t1, 1188($s7)
li $t8, 1
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1192($s7)
sw $t1, 1196($s7)
li $t8, 2
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1200($s7)
sw $t1, 1204($s7)
li $t8, 3
ctc1 $t8, $31
mul.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1208($s7)
sw $t1, 1212($s7)
li $t9, 0x74907fc4
mtc1 $t9, $f2
li $t9, 0x80000000
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1216($s7)
sw $t1, 1220($s7)
li $t8, 1
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1224($s7)
sw $t1, 1228($s7)
li $t8, 2
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1232($s7)
sw $t1, 1236($s7)
li $t8, 3
ctc1 $t8, $31
div.s $f6, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1240($s7)
sw $t1, 1244($s7)
li $t9, 0xf07f26e6
mtc1 $t9, $f2
li $t9, 0x23b392b4
mtc1 $t9, $f4
li $t8, 0
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1248($s7)
sw $t1, 1252($s7)
li $t8, 1
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1256($s7)
sw $t1, 1260($s7)
li $t8, 2
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1264($s7)
sw $t1, 1268($s7)
li $t8, 3
ctc1 $t8, $31
sqrt.s $f6, $f2
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1272($s7)
sw $t1, 1276($s7)
li $v0, 10
syscall
