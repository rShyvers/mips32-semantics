# Randomised (seeded 701) compare of .s operands including NaNs (quiet and signaling) and edge values: all 16 predicates, the FCSR (condition code + Invalid) stored after each.
# MD00086 Vol II-A Rev 6.06 C.cond.fmt p.110-113; MD00082 Vol I-A Rev 6.01 Table 6.2 (legacy NaN encodings).
.data
res: .space 832
.text
la $s7, res
li $t9, 0x7fc00000
mtc1 $t9, $f0
li $t9, 0x007fffff
mtc1 $t9, $f2
ctc1 $zero, $31
c.f.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 0($s7)
ctc1 $zero, $31
c.un.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 4($s7)
ctc1 $zero, $31
c.eq.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 8($s7)
ctc1 $zero, $31
c.ueq.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 12($s7)
ctc1 $zero, $31
c.olt.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 16($s7)
ctc1 $zero, $31
c.ult.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 20($s7)
ctc1 $zero, $31
c.ole.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 24($s7)
ctc1 $zero, $31
c.ule.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 28($s7)
ctc1 $zero, $31
c.sf.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 32($s7)
ctc1 $zero, $31
c.ngle.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 36($s7)
ctc1 $zero, $31
c.seq.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 40($s7)
ctc1 $zero, $31
c.ngl.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 44($s7)
ctc1 $zero, $31
c.lt.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 48($s7)
ctc1 $zero, $31
c.nge.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 52($s7)
ctc1 $zero, $31
c.le.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 56($s7)
ctc1 $zero, $31
c.ngt.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 60($s7)
li $t9, 0xbf800000
mtc1 $t9, $f0
li $t9, 0xffc00001
mtc1 $t9, $f2
ctc1 $zero, $31
c.f.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 64($s7)
ctc1 $zero, $31
c.un.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 68($s7)
ctc1 $zero, $31
c.eq.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 72($s7)
ctc1 $zero, $31
c.ueq.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 76($s7)
ctc1 $zero, $31
c.olt.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 80($s7)
ctc1 $zero, $31
c.ult.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 84($s7)
ctc1 $zero, $31
c.ole.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 88($s7)
ctc1 $zero, $31
c.ule.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 92($s7)
ctc1 $zero, $31
c.sf.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 96($s7)
ctc1 $zero, $31
c.ngle.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 100($s7)
ctc1 $zero, $31
c.seq.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 104($s7)
ctc1 $zero, $31
c.ngl.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 108($s7)
ctc1 $zero, $31
c.lt.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 112($s7)
ctc1 $zero, $31
c.nge.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 116($s7)
ctc1 $zero, $31
c.le.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 120($s7)
ctc1 $zero, $31
c.ngt.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 124($s7)
li $t9, 0x00000001
mtc1 $t9, $f0
li $t9, 0x00000001
mtc1 $t9, $f2
ctc1 $zero, $31
c.f.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 128($s7)
ctc1 $zero, $31
c.un.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 132($s7)
ctc1 $zero, $31
c.eq.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 136($s7)
ctc1 $zero, $31
c.ueq.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 140($s7)
ctc1 $zero, $31
c.olt.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 144($s7)
ctc1 $zero, $31
c.ult.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 148($s7)
ctc1 $zero, $31
c.ole.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 152($s7)
ctc1 $zero, $31
c.ule.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 156($s7)
ctc1 $zero, $31
c.sf.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 160($s7)
ctc1 $zero, $31
c.ngle.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 164($s7)
ctc1 $zero, $31
c.seq.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 168($s7)
ctc1 $zero, $31
c.ngl.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 172($s7)
ctc1 $zero, $31
c.lt.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 176($s7)
ctc1 $zero, $31
c.nge.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 180($s7)
ctc1 $zero, $31
c.le.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 184($s7)
ctc1 $zero, $31
c.ngt.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 188($s7)
li $t9, 0xff800000
mtc1 $t9, $f0
li $t9, 0x4b000000
mtc1 $t9, $f2
ctc1 $zero, $31
c.f.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 192($s7)
ctc1 $zero, $31
c.un.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 196($s7)
ctc1 $zero, $31
c.eq.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 200($s7)
ctc1 $zero, $31
c.ueq.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 204($s7)
ctc1 $zero, $31
c.olt.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 208($s7)
ctc1 $zero, $31
c.ult.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 212($s7)
ctc1 $zero, $31
c.ole.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 216($s7)
ctc1 $zero, $31
c.ule.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 220($s7)
ctc1 $zero, $31
c.sf.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 224($s7)
ctc1 $zero, $31
c.ngle.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 228($s7)
ctc1 $zero, $31
c.seq.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 232($s7)
ctc1 $zero, $31
c.ngl.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 236($s7)
ctc1 $zero, $31
c.lt.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 240($s7)
ctc1 $zero, $31
c.nge.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 244($s7)
ctc1 $zero, $31
c.le.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 248($s7)
ctc1 $zero, $31
c.ngt.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 252($s7)
li $t9, 0x00800000
mtc1 $t9, $f0
li $t9, 0x40400000
mtc1 $t9, $f2
ctc1 $zero, $31
c.f.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 256($s7)
ctc1 $zero, $31
c.un.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 260($s7)
ctc1 $zero, $31
c.eq.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 264($s7)
ctc1 $zero, $31
c.ueq.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 268($s7)
ctc1 $zero, $31
c.olt.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 272($s7)
ctc1 $zero, $31
c.ult.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 276($s7)
ctc1 $zero, $31
c.ole.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 280($s7)
ctc1 $zero, $31
c.ule.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 284($s7)
ctc1 $zero, $31
c.sf.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 288($s7)
ctc1 $zero, $31
c.ngle.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 292($s7)
ctc1 $zero, $31
c.seq.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 296($s7)
ctc1 $zero, $31
c.ngl.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 300($s7)
ctc1 $zero, $31
c.lt.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 304($s7)
ctc1 $zero, $31
c.nge.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 308($s7)
ctc1 $zero, $31
c.le.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 312($s7)
ctc1 $zero, $31
c.ngt.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 316($s7)
li $t9, 0xbf800000
mtc1 $t9, $f0
li $t9, 0x40000000
mtc1 $t9, $f2
ctc1 $zero, $31
c.f.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 320($s7)
ctc1 $zero, $31
c.un.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 324($s7)
ctc1 $zero, $31
c.eq.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 328($s7)
ctc1 $zero, $31
c.ueq.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 332($s7)
ctc1 $zero, $31
c.olt.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 336($s7)
ctc1 $zero, $31
c.ult.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 340($s7)
ctc1 $zero, $31
c.ole.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 344($s7)
ctc1 $zero, $31
c.ule.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 348($s7)
ctc1 $zero, $31
c.sf.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 352($s7)
ctc1 $zero, $31
c.ngle.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 356($s7)
ctc1 $zero, $31
c.seq.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 360($s7)
ctc1 $zero, $31
c.ngl.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 364($s7)
ctc1 $zero, $31
c.lt.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 368($s7)
ctc1 $zero, $31
c.nge.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 372($s7)
ctc1 $zero, $31
c.le.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 376($s7)
ctc1 $zero, $31
c.ngt.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 380($s7)
li $t9, 0x80000000
mtc1 $t9, $f0
li $t9, 0x00800001
mtc1 $t9, $f2
ctc1 $zero, $31
c.f.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 384($s7)
ctc1 $zero, $31
c.un.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 388($s7)
ctc1 $zero, $31
c.eq.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 392($s7)
ctc1 $zero, $31
c.ueq.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 396($s7)
ctc1 $zero, $31
c.olt.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 400($s7)
ctc1 $zero, $31
c.ult.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 404($s7)
ctc1 $zero, $31
c.ole.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 408($s7)
ctc1 $zero, $31
c.ule.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 412($s7)
ctc1 $zero, $31
c.sf.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 416($s7)
ctc1 $zero, $31
c.ngle.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 420($s7)
ctc1 $zero, $31
c.seq.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 424($s7)
ctc1 $zero, $31
c.ngl.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 428($s7)
ctc1 $zero, $31
c.lt.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 432($s7)
ctc1 $zero, $31
c.nge.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 436($s7)
ctc1 $zero, $31
c.le.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 440($s7)
ctc1 $zero, $31
c.ngt.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 444($s7)
li $t9, 0x00800001
mtc1 $t9, $f0
li $t9, 0x007fffff
mtc1 $t9, $f2
ctc1 $zero, $31
c.f.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 448($s7)
ctc1 $zero, $31
c.un.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 452($s7)
ctc1 $zero, $31
c.eq.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 456($s7)
ctc1 $zero, $31
c.ueq.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 460($s7)
ctc1 $zero, $31
c.olt.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 464($s7)
ctc1 $zero, $31
c.ult.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 468($s7)
ctc1 $zero, $31
c.ole.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 472($s7)
ctc1 $zero, $31
c.ule.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 476($s7)
ctc1 $zero, $31
c.sf.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 480($s7)
ctc1 $zero, $31
c.ngle.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 484($s7)
ctc1 $zero, $31
c.seq.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 488($s7)
ctc1 $zero, $31
c.ngl.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 492($s7)
ctc1 $zero, $31
c.lt.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 496($s7)
ctc1 $zero, $31
c.nge.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 500($s7)
ctc1 $zero, $31
c.le.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 504($s7)
ctc1 $zero, $31
c.ngt.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 508($s7)
li $t9, 0xbf800000
mtc1 $t9, $f0
li $t9, 0x7fbfffff
mtc1 $t9, $f2
ctc1 $zero, $31
c.f.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 512($s7)
ctc1 $zero, $31
c.un.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 516($s7)
ctc1 $zero, $31
c.eq.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 520($s7)
ctc1 $zero, $31
c.ueq.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 524($s7)
ctc1 $zero, $31
c.olt.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 528($s7)
ctc1 $zero, $31
c.ult.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 532($s7)
ctc1 $zero, $31
c.ole.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 536($s7)
ctc1 $zero, $31
c.ule.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 540($s7)
ctc1 $zero, $31
c.sf.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 544($s7)
ctc1 $zero, $31
c.ngle.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 548($s7)
ctc1 $zero, $31
c.seq.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 552($s7)
ctc1 $zero, $31
c.ngl.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 556($s7)
ctc1 $zero, $31
c.lt.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 560($s7)
ctc1 $zero, $31
c.nge.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 564($s7)
ctc1 $zero, $31
c.le.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 568($s7)
ctc1 $zero, $31
c.ngt.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 572($s7)
li $t9, 0x007fffff
mtc1 $t9, $f0
li $t9, 0x40400000
mtc1 $t9, $f2
ctc1 $zero, $31
c.f.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 576($s7)
ctc1 $zero, $31
c.un.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 580($s7)
ctc1 $zero, $31
c.eq.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 584($s7)
ctc1 $zero, $31
c.ueq.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 588($s7)
ctc1 $zero, $31
c.olt.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 592($s7)
ctc1 $zero, $31
c.ult.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 596($s7)
ctc1 $zero, $31
c.ole.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 600($s7)
ctc1 $zero, $31
c.ule.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 604($s7)
ctc1 $zero, $31
c.sf.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 608($s7)
ctc1 $zero, $31
c.ngle.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 612($s7)
ctc1 $zero, $31
c.seq.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 616($s7)
ctc1 $zero, $31
c.ngl.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 620($s7)
ctc1 $zero, $31
c.lt.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 624($s7)
ctc1 $zero, $31
c.nge.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 628($s7)
ctc1 $zero, $31
c.le.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 632($s7)
ctc1 $zero, $31
c.ngt.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 636($s7)
li $t9, 0x3f000000
mtc1 $t9, $f0
li $t9, 0x3f000000
mtc1 $t9, $f2
ctc1 $zero, $31
c.f.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 640($s7)
ctc1 $zero, $31
c.un.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 644($s7)
ctc1 $zero, $31
c.eq.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 648($s7)
ctc1 $zero, $31
c.ueq.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 652($s7)
ctc1 $zero, $31
c.olt.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 656($s7)
ctc1 $zero, $31
c.ult.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 660($s7)
ctc1 $zero, $31
c.ole.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 664($s7)
ctc1 $zero, $31
c.ule.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 668($s7)
ctc1 $zero, $31
c.sf.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 672($s7)
ctc1 $zero, $31
c.ngle.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 676($s7)
ctc1 $zero, $31
c.seq.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 680($s7)
ctc1 $zero, $31
c.ngl.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 684($s7)
ctc1 $zero, $31
c.lt.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 688($s7)
ctc1 $zero, $31
c.nge.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 692($s7)
ctc1 $zero, $31
c.le.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 696($s7)
ctc1 $zero, $31
c.ngt.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 700($s7)
li $t9, 0x34000000
mtc1 $t9, $f0
li $t9, 0xff7fffff
mtc1 $t9, $f2
ctc1 $zero, $31
c.f.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 704($s7)
ctc1 $zero, $31
c.un.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 708($s7)
ctc1 $zero, $31
c.eq.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 712($s7)
ctc1 $zero, $31
c.ueq.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 716($s7)
ctc1 $zero, $31
c.olt.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 720($s7)
ctc1 $zero, $31
c.ult.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 724($s7)
ctc1 $zero, $31
c.ole.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 728($s7)
ctc1 $zero, $31
c.ule.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 732($s7)
ctc1 $zero, $31
c.sf.s $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 736($s7)
ctc1 $zero, $31
c.ngle.s $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 740($s7)
ctc1 $zero, $31
c.seq.s $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 744($s7)
ctc1 $zero, $31
c.ngl.s $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 748($s7)
ctc1 $zero, $31
c.lt.s $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 752($s7)
ctc1 $zero, $31
c.nge.s $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 756($s7)
ctc1 $zero, $31
c.le.s $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 760($s7)
ctc1 $zero, $31
c.ngt.s $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 764($s7)
li $v0, 10
syscall
