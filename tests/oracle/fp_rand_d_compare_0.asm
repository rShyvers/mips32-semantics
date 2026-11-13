# Randomised (seeded 800) compare of .d operands including NaNs (quiet and signaling) and edge values: all 16 predicates, the FCSR (condition code + Invalid) stored after each.
# MD00086 Vol II-A Rev 6.06 C.cond.fmt p.110-113; MD00082 Vol I-A Rev 6.01 Table 6.2 (legacy NaN encodings).
.data
res: .space 832
.text
la $s7, res
li $t9, 0xffffffff
mtc1 $t9, $f0
li $t9, 0x7ff7ffff
mtc1 $t9, $f1
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3ca00000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 0($s7)
ctc1 $zero, $31
c.un.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 4($s7)
ctc1 $zero, $31
c.eq.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 8($s7)
ctc1 $zero, $31
c.ueq.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 12($s7)
ctc1 $zero, $31
c.olt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 16($s7)
ctc1 $zero, $31
c.ult.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 20($s7)
ctc1 $zero, $31
c.ole.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 24($s7)
ctc1 $zero, $31
c.ule.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 28($s7)
ctc1 $zero, $31
c.sf.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 32($s7)
ctc1 $zero, $31
c.ngle.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 36($s7)
ctc1 $zero, $31
c.seq.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 40($s7)
ctc1 $zero, $31
c.ngl.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 44($s7)
ctc1 $zero, $31
c.lt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 48($s7)
ctc1 $zero, $31
c.nge.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 52($s7)
ctc1 $zero, $31
c.le.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 56($s7)
ctc1 $zero, $31
c.ngt.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 60($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x80000000
mtc1 $t9, $f1
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3ca00000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 64($s7)
ctc1 $zero, $31
c.un.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 68($s7)
ctc1 $zero, $31
c.eq.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 72($s7)
ctc1 $zero, $31
c.ueq.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 76($s7)
ctc1 $zero, $31
c.olt.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 80($s7)
ctc1 $zero, $31
c.ult.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 84($s7)
ctc1 $zero, $31
c.ole.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 88($s7)
ctc1 $zero, $31
c.ule.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 92($s7)
ctc1 $zero, $31
c.sf.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 96($s7)
ctc1 $zero, $31
c.ngle.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 100($s7)
ctc1 $zero, $31
c.seq.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 104($s7)
ctc1 $zero, $31
c.ngl.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 108($s7)
ctc1 $zero, $31
c.lt.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 112($s7)
ctc1 $zero, $31
c.nge.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 116($s7)
ctc1 $zero, $31
c.le.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 120($s7)
ctc1 $zero, $31
c.ngt.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 124($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x7fd00000
mtc1 $t9, $f1
li $t9, 0xffffffff
mtc1 $t9, $f2
li $t9, 0x7fefffff
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 128($s7)
ctc1 $zero, $31
c.un.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 132($s7)
ctc1 $zero, $31
c.eq.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 136($s7)
ctc1 $zero, $31
c.ueq.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 140($s7)
ctc1 $zero, $31
c.olt.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 144($s7)
ctc1 $zero, $31
c.ult.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 148($s7)
ctc1 $zero, $31
c.ole.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 152($s7)
ctc1 $zero, $31
c.ule.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 156($s7)
ctc1 $zero, $31
c.sf.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 160($s7)
ctc1 $zero, $31
c.ngle.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 164($s7)
ctc1 $zero, $31
c.seq.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 168($s7)
ctc1 $zero, $31
c.ngl.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 172($s7)
ctc1 $zero, $31
c.lt.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 176($s7)
ctc1 $zero, $31
c.nge.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 180($s7)
ctc1 $zero, $31
c.le.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 184($s7)
ctc1 $zero, $31
c.ngt.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 188($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x3ca00000
mtc1 $t9, $f1
li $t9, 0x00000001
mtc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 192($s7)
ctc1 $zero, $31
c.un.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 196($s7)
ctc1 $zero, $31
c.eq.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 200($s7)
ctc1 $zero, $31
c.ueq.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 204($s7)
ctc1 $zero, $31
c.olt.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 208($s7)
ctc1 $zero, $31
c.ult.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 212($s7)
ctc1 $zero, $31
c.ole.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 216($s7)
ctc1 $zero, $31
c.ule.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 220($s7)
ctc1 $zero, $31
c.sf.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 224($s7)
ctc1 $zero, $31
c.ngle.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 228($s7)
ctc1 $zero, $31
c.seq.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 232($s7)
ctc1 $zero, $31
c.ngl.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 236($s7)
ctc1 $zero, $31
c.lt.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 240($s7)
ctc1 $zero, $31
c.nge.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 244($s7)
ctc1 $zero, $31
c.le.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 248($s7)
ctc1 $zero, $31
c.ngt.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 252($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x80000000
mtc1 $t9, $f1
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x80000000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 256($s7)
ctc1 $zero, $31
c.un.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 260($s7)
ctc1 $zero, $31
c.eq.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 264($s7)
ctc1 $zero, $31
c.ueq.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 268($s7)
ctc1 $zero, $31
c.olt.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 272($s7)
ctc1 $zero, $31
c.ult.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 276($s7)
ctc1 $zero, $31
c.ole.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 280($s7)
ctc1 $zero, $31
c.ule.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 284($s7)
ctc1 $zero, $31
c.sf.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 288($s7)
ctc1 $zero, $31
c.ngle.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 292($s7)
ctc1 $zero, $31
c.seq.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 296($s7)
ctc1 $zero, $31
c.ngl.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 300($s7)
ctc1 $zero, $31
c.lt.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 304($s7)
ctc1 $zero, $31
c.nge.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 308($s7)
ctc1 $zero, $31
c.le.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 312($s7)
ctc1 $zero, $31
c.ngt.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 316($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x00200000
mtc1 $t9, $f1
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x7ff00000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 320($s7)
ctc1 $zero, $31
c.un.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 324($s7)
ctc1 $zero, $31
c.eq.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 328($s7)
ctc1 $zero, $31
c.ueq.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 332($s7)
ctc1 $zero, $31
c.olt.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 336($s7)
ctc1 $zero, $31
c.ult.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 340($s7)
ctc1 $zero, $31
c.ole.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 344($s7)
ctc1 $zero, $31
c.ule.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 348($s7)
ctc1 $zero, $31
c.sf.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 352($s7)
ctc1 $zero, $31
c.ngle.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 356($s7)
ctc1 $zero, $31
c.seq.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 360($s7)
ctc1 $zero, $31
c.ngl.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 364($s7)
ctc1 $zero, $31
c.lt.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 368($s7)
ctc1 $zero, $31
c.nge.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 372($s7)
ctc1 $zero, $31
c.le.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 376($s7)
ctc1 $zero, $31
c.ngt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 380($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x7ff00000
mtc1 $t9, $f1
li $t9, 0x00000001
mtc1 $t9, $f2
li $t9, 0x00100000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 384($s7)
ctc1 $zero, $31
c.un.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 388($s7)
ctc1 $zero, $31
c.eq.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 392($s7)
ctc1 $zero, $31
c.ueq.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 396($s7)
ctc1 $zero, $31
c.olt.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 400($s7)
ctc1 $zero, $31
c.ult.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 404($s7)
ctc1 $zero, $31
c.ole.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 408($s7)
ctc1 $zero, $31
c.ule.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 412($s7)
ctc1 $zero, $31
c.sf.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 416($s7)
ctc1 $zero, $31
c.ngle.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 420($s7)
ctc1 $zero, $31
c.seq.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 424($s7)
ctc1 $zero, $31
c.ngl.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 428($s7)
ctc1 $zero, $31
c.lt.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 432($s7)
ctc1 $zero, $31
c.nge.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 436($s7)
ctc1 $zero, $31
c.le.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 440($s7)
ctc1 $zero, $31
c.ngt.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 444($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x7ff00000
mtc1 $t9, $f1
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x7ff00000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 448($s7)
ctc1 $zero, $31
c.un.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 452($s7)
ctc1 $zero, $31
c.eq.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 456($s7)
ctc1 $zero, $31
c.ueq.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 460($s7)
ctc1 $zero, $31
c.olt.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 464($s7)
ctc1 $zero, $31
c.ult.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 468($s7)
ctc1 $zero, $31
c.ole.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 472($s7)
ctc1 $zero, $31
c.ule.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 476($s7)
ctc1 $zero, $31
c.sf.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 480($s7)
ctc1 $zero, $31
c.ngle.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 484($s7)
ctc1 $zero, $31
c.seq.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 488($s7)
ctc1 $zero, $31
c.ngl.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 492($s7)
ctc1 $zero, $31
c.lt.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 496($s7)
ctc1 $zero, $31
c.nge.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 500($s7)
ctc1 $zero, $31
c.le.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 504($s7)
ctc1 $zero, $31
c.ngt.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 508($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x43400000
mtc1 $t9, $f1
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x43400000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 512($s7)
ctc1 $zero, $31
c.un.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 516($s7)
ctc1 $zero, $31
c.eq.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 520($s7)
ctc1 $zero, $31
c.ueq.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 524($s7)
ctc1 $zero, $31
c.olt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 528($s7)
ctc1 $zero, $31
c.ult.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 532($s7)
ctc1 $zero, $31
c.ole.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 536($s7)
ctc1 $zero, $31
c.ule.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 540($s7)
ctc1 $zero, $31
c.sf.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 544($s7)
ctc1 $zero, $31
c.ngle.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 548($s7)
ctc1 $zero, $31
c.seq.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 552($s7)
ctc1 $zero, $31
c.ngl.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 556($s7)
ctc1 $zero, $31
c.lt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 560($s7)
ctc1 $zero, $31
c.nge.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 564($s7)
ctc1 $zero, $31
c.le.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 568($s7)
ctc1 $zero, $31
c.ngt.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 572($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0xbff00000
mtc1 $t9, $f1
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0xbff00000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 576($s7)
ctc1 $zero, $31
c.un.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 580($s7)
ctc1 $zero, $31
c.eq.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 584($s7)
ctc1 $zero, $31
c.ueq.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 588($s7)
ctc1 $zero, $31
c.olt.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 592($s7)
ctc1 $zero, $31
c.ult.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 596($s7)
ctc1 $zero, $31
c.ole.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 600($s7)
ctc1 $zero, $31
c.ule.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 604($s7)
ctc1 $zero, $31
c.sf.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 608($s7)
ctc1 $zero, $31
c.ngle.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 612($s7)
ctc1 $zero, $31
c.seq.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 616($s7)
ctc1 $zero, $31
c.ngl.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 620($s7)
ctc1 $zero, $31
c.lt.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 624($s7)
ctc1 $zero, $31
c.nge.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 628($s7)
ctc1 $zero, $31
c.le.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 632($s7)
ctc1 $zero, $31
c.ngt.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 636($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x7fd00000
mtc1 $t9, $f1
li $t9, 0x9999999a
mtc1 $t9, $f2
li $t9, 0x3fb99999
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 640($s7)
ctc1 $zero, $31
c.un.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 644($s7)
ctc1 $zero, $31
c.eq.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 648($s7)
ctc1 $zero, $31
c.ueq.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 652($s7)
ctc1 $zero, $31
c.olt.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 656($s7)
ctc1 $zero, $31
c.ult.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 660($s7)
ctc1 $zero, $31
c.ole.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 664($s7)
ctc1 $zero, $31
c.ule.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 668($s7)
ctc1 $zero, $31
c.sf.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 672($s7)
ctc1 $zero, $31
c.ngle.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 676($s7)
ctc1 $zero, $31
c.seq.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 680($s7)
ctc1 $zero, $31
c.ngl.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 684($s7)
ctc1 $zero, $31
c.lt.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 688($s7)
ctc1 $zero, $31
c.nge.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 692($s7)
ctc1 $zero, $31
c.le.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 696($s7)
ctc1 $zero, $31
c.ngt.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 700($s7)
li $t9, 0xffffffff
mtc1 $t9, $f0
li $t9, 0x000fffff
mtc1 $t9, $f1
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 704($s7)
ctc1 $zero, $31
c.un.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 708($s7)
ctc1 $zero, $31
c.eq.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 712($s7)
ctc1 $zero, $31
c.ueq.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 716($s7)
ctc1 $zero, $31
c.olt.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 720($s7)
ctc1 $zero, $31
c.ult.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 724($s7)
ctc1 $zero, $31
c.ole.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 728($s7)
ctc1 $zero, $31
c.ule.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 732($s7)
ctc1 $zero, $31
c.sf.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 736($s7)
ctc1 $zero, $31
c.ngle.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 740($s7)
ctc1 $zero, $31
c.seq.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 744($s7)
ctc1 $zero, $31
c.ngl.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 748($s7)
ctc1 $zero, $31
c.lt.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 752($s7)
ctc1 $zero, $31
c.nge.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 756($s7)
ctc1 $zero, $31
c.le.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 760($s7)
ctc1 $zero, $31
c.ngt.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 764($s7)
li $v0, 10
syscall
