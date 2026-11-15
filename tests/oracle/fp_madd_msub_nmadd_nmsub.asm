# madd/msub/nmadd/nmsub .s and .d: a plain case and a case where a fused operation would differ from multiply-then-add (the product rounds);
# result bits and FCSR after each, in RN and RZ.
# MD00086 Vol II-A Rev 6.06: MADD.fmt p.256 ('The intermediate product is rounded ...; the results and flags are as if separate multiply and add instructions were executed'),
# MSUB.fmt p.287, NMADD.fmt p.308, NMSUB.fmt p.310.
.data
res: .space 704
.text
la $s7, res
li $t9, 0x40000000
mtc1 $t9, $f2
li $t9, 0x40400000
mtc1 $t9, $f4
li $t9, 0x40800000
mtc1 $t9, $f6
li $t8, 0
ctc1 $t8, $31
madd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 0($s7)
sw $t1, 4($s7)
li $t8, 0
ctc1 $t8, $31
msub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 8($s7)
sw $t1, 12($s7)
li $t8, 0
ctc1 $t8, $31
nmadd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 16($s7)
sw $t1, 20($s7)
li $t8, 0
ctc1 $t8, $31
nmsub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 24($s7)
sw $t1, 28($s7)
li $t9, 0x3f800800
mtc1 $t9, $f2
li $t9, 0x3f800800
mtc1 $t9, $f4
li $t9, 0xbf801000
mtc1 $t9, $f6
li $t8, 0
ctc1 $t8, $31
madd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 32($s7)
sw $t1, 36($s7)
li $t8, 0
ctc1 $t8, $31
msub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 40($s7)
sw $t1, 44($s7)
li $t8, 0
ctc1 $t8, $31
nmadd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 48($s7)
sw $t1, 52($s7)
li $t8, 0
ctc1 $t8, $31
nmsub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 56($s7)
sw $t1, 60($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x40080000
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f6
li $t9, 0x40100000
mtc1 $t9, $f7
li $t8, 0
ctc1 $t8, $31
madd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 64($s7)
sw $t2, 68($s7)
sw $t1, 72($s7)
li $t8, 0
ctc1 $t8, $31
msub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 76($s7)
sw $t2, 80($s7)
sw $t1, 84($s7)
li $t8, 0
ctc1 $t8, $31
nmadd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 88($s7)
sw $t2, 92($s7)
sw $t1, 96($s7)
li $t8, 0
ctc1 $t8, $31
nmsub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 100($s7)
sw $t2, 104($s7)
sw $t1, 108($s7)
li $t9, 0x02000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mtc1 $t9, $f3
li $t9, 0x02000000
mtc1 $t9, $f4
li $t9, 0x3ff00000
mtc1 $t9, $f5
li $t9, 0x04000000
mtc1 $t9, $f6
li $t9, 0xbff00000
mtc1 $t9, $f7
li $t8, 0
ctc1 $t8, $31
madd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 112($s7)
sw $t2, 116($s7)
sw $t1, 120($s7)
li $t8, 0
ctc1 $t8, $31
msub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 124($s7)
sw $t2, 128($s7)
sw $t1, 132($s7)
li $t8, 0
ctc1 $t8, $31
nmadd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 136($s7)
sw $t2, 140($s7)
sw $t1, 144($s7)
li $t8, 0
ctc1 $t8, $31
nmsub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 148($s7)
sw $t2, 152($s7)
sw $t1, 156($s7)
li $t9, 0x40000000
mtc1 $t9, $f2
li $t9, 0x40400000
mtc1 $t9, $f4
li $t9, 0x40800000
mtc1 $t9, $f6
li $t8, 1
ctc1 $t8, $31
madd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 160($s7)
sw $t1, 164($s7)
li $t8, 1
ctc1 $t8, $31
msub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 168($s7)
sw $t1, 172($s7)
li $t8, 1
ctc1 $t8, $31
nmadd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 176($s7)
sw $t1, 180($s7)
li $t8, 1
ctc1 $t8, $31
nmsub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 184($s7)
sw $t1, 188($s7)
li $t9, 0x3f800800
mtc1 $t9, $f2
li $t9, 0x3f800800
mtc1 $t9, $f4
li $t9, 0xbf801000
mtc1 $t9, $f6
li $t8, 1
ctc1 $t8, $31
madd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 192($s7)
sw $t1, 196($s7)
li $t8, 1
ctc1 $t8, $31
msub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 200($s7)
sw $t1, 204($s7)
li $t8, 1
ctc1 $t8, $31
nmadd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 208($s7)
sw $t1, 212($s7)
li $t8, 1
ctc1 $t8, $31
nmsub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 216($s7)
sw $t1, 220($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x40080000
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f6
li $t9, 0x40100000
mtc1 $t9, $f7
li $t8, 1
ctc1 $t8, $31
madd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 224($s7)
sw $t2, 228($s7)
sw $t1, 232($s7)
li $t8, 1
ctc1 $t8, $31
msub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 236($s7)
sw $t2, 240($s7)
sw $t1, 244($s7)
li $t8, 1
ctc1 $t8, $31
nmadd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 248($s7)
sw $t2, 252($s7)
sw $t1, 256($s7)
li $t8, 1
ctc1 $t8, $31
nmsub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 260($s7)
sw $t2, 264($s7)
sw $t1, 268($s7)
li $t9, 0x02000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mtc1 $t9, $f3
li $t9, 0x02000000
mtc1 $t9, $f4
li $t9, 0x3ff00000
mtc1 $t9, $f5
li $t9, 0x04000000
mtc1 $t9, $f6
li $t9, 0xbff00000
mtc1 $t9, $f7
li $t8, 1
ctc1 $t8, $31
madd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 272($s7)
sw $t2, 276($s7)
sw $t1, 280($s7)
li $t8, 1
ctc1 $t8, $31
msub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 284($s7)
sw $t2, 288($s7)
sw $t1, 292($s7)
li $t8, 1
ctc1 $t8, $31
nmadd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 296($s7)
sw $t2, 300($s7)
sw $t1, 304($s7)
li $t8, 1
ctc1 $t8, $31
nmsub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 308($s7)
sw $t2, 312($s7)
sw $t1, 316($s7)
li $t9, 0x40000000
mtc1 $t9, $f2
li $t9, 0x40400000
mtc1 $t9, $f4
li $t9, 0x40800000
mtc1 $t9, $f6
li $t8, 2
ctc1 $t8, $31
madd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 320($s7)
sw $t1, 324($s7)
li $t8, 2
ctc1 $t8, $31
msub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 328($s7)
sw $t1, 332($s7)
li $t8, 2
ctc1 $t8, $31
nmadd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 336($s7)
sw $t1, 340($s7)
li $t8, 2
ctc1 $t8, $31
nmsub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 344($s7)
sw $t1, 348($s7)
li $t9, 0x3f800800
mtc1 $t9, $f2
li $t9, 0x3f800800
mtc1 $t9, $f4
li $t9, 0xbf801000
mtc1 $t9, $f6
li $t8, 2
ctc1 $t8, $31
madd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 352($s7)
sw $t1, 356($s7)
li $t8, 2
ctc1 $t8, $31
msub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 360($s7)
sw $t1, 364($s7)
li $t8, 2
ctc1 $t8, $31
nmadd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 368($s7)
sw $t1, 372($s7)
li $t8, 2
ctc1 $t8, $31
nmsub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 376($s7)
sw $t1, 380($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x40080000
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f6
li $t9, 0x40100000
mtc1 $t9, $f7
li $t8, 2
ctc1 $t8, $31
madd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 384($s7)
sw $t2, 388($s7)
sw $t1, 392($s7)
li $t8, 2
ctc1 $t8, $31
msub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 396($s7)
sw $t2, 400($s7)
sw $t1, 404($s7)
li $t8, 2
ctc1 $t8, $31
nmadd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 408($s7)
sw $t2, 412($s7)
sw $t1, 416($s7)
li $t8, 2
ctc1 $t8, $31
nmsub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 420($s7)
sw $t2, 424($s7)
sw $t1, 428($s7)
li $t9, 0x02000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mtc1 $t9, $f3
li $t9, 0x02000000
mtc1 $t9, $f4
li $t9, 0x3ff00000
mtc1 $t9, $f5
li $t9, 0x04000000
mtc1 $t9, $f6
li $t9, 0xbff00000
mtc1 $t9, $f7
li $t8, 2
ctc1 $t8, $31
madd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 432($s7)
sw $t2, 436($s7)
sw $t1, 440($s7)
li $t8, 2
ctc1 $t8, $31
msub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 444($s7)
sw $t2, 448($s7)
sw $t1, 452($s7)
li $t8, 2
ctc1 $t8, $31
nmadd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 456($s7)
sw $t2, 460($s7)
sw $t1, 464($s7)
li $t8, 2
ctc1 $t8, $31
nmsub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 468($s7)
sw $t2, 472($s7)
sw $t1, 476($s7)
li $t9, 0x40000000
mtc1 $t9, $f2
li $t9, 0x40400000
mtc1 $t9, $f4
li $t9, 0x40800000
mtc1 $t9, $f6
li $t8, 3
ctc1 $t8, $31
madd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 480($s7)
sw $t1, 484($s7)
li $t8, 3
ctc1 $t8, $31
msub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 488($s7)
sw $t1, 492($s7)
li $t8, 3
ctc1 $t8, $31
nmadd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 496($s7)
sw $t1, 500($s7)
li $t8, 3
ctc1 $t8, $31
nmsub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 504($s7)
sw $t1, 508($s7)
li $t9, 0x3f800800
mtc1 $t9, $f2
li $t9, 0x3f800800
mtc1 $t9, $f4
li $t9, 0xbf801000
mtc1 $t9, $f6
li $t8, 3
ctc1 $t8, $31
madd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 512($s7)
sw $t1, 516($s7)
li $t8, 3
ctc1 $t8, $31
msub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 520($s7)
sw $t1, 524($s7)
li $t8, 3
ctc1 $t8, $31
nmadd.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 528($s7)
sw $t1, 532($s7)
li $t8, 3
ctc1 $t8, $31
nmsub.s $f8, $f6, $f2, $f4
mfc1 $t0, $f8
cfc1 $t1, $31
sw $t0, 536($s7)
sw $t1, 540($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x40080000
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f6
li $t9, 0x40100000
mtc1 $t9, $f7
li $t8, 3
ctc1 $t8, $31
madd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 544($s7)
sw $t2, 548($s7)
sw $t1, 552($s7)
li $t8, 3
ctc1 $t8, $31
msub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 556($s7)
sw $t2, 560($s7)
sw $t1, 564($s7)
li $t8, 3
ctc1 $t8, $31
nmadd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 568($s7)
sw $t2, 572($s7)
sw $t1, 576($s7)
li $t8, 3
ctc1 $t8, $31
nmsub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 580($s7)
sw $t2, 584($s7)
sw $t1, 588($s7)
li $t9, 0x02000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mtc1 $t9, $f3
li $t9, 0x02000000
mtc1 $t9, $f4
li $t9, 0x3ff00000
mtc1 $t9, $f5
li $t9, 0x04000000
mtc1 $t9, $f6
li $t9, 0xbff00000
mtc1 $t9, $f7
li $t8, 3
ctc1 $t8, $31
madd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 592($s7)
sw $t2, 596($s7)
sw $t1, 600($s7)
li $t8, 3
ctc1 $t8, $31
msub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 604($s7)
sw $t2, 608($s7)
sw $t1, 612($s7)
li $t8, 3
ctc1 $t8, $31
nmadd.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 616($s7)
sw $t2, 620($s7)
sw $t1, 624($s7)
li $t8, 3
ctc1 $t8, $31
nmsub.d $f8, $f6, $f2, $f4
mfc1 $t0, $f8
mfc1 $t2, $f9
cfc1 $t1, $31
sw $t0, 628($s7)
sw $t2, 632($s7)
sw $t1, 636($s7)
li $v0, 10
syscall
