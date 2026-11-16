# CMP.condn.fmt for every condn of Table A.17 (MD00086 Vol II-A Rev 6.06 p.457) on ordered, equal, signed-zero, infinite, QNaN and SNaN
# operand pairs: the mask (all ones / all zeros of the format width) and FCSR (Invalid for an SNaN, and for a QNaN with the signalling cond3).
# MD00086 Vol II-A Rev 6.06 CMP.condn.fmt p.136-140 (Operation p.140; Table 3.9 p.138-139). cmp.or/une/ne/sor/sune/sne are emitted as .word
# (llvm-mc 21 does not assemble them); the words follow the p.136 diagram. Only the low 32 bits of a .S result are recorded (the upper
# half is UNPREDICTABLE, p.136).
.data
res: .space 2112
.text
la $s7, res
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x40000000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
cmp.af.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 0($s7)
mfhc1 $t0, $f6
sw $t0, 4($s7)
cfc1 $t1, $31
sw $t1, 8($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.un.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 12($s7)
mfhc1 $t0, $f6
sw $t0, 16($s7)
cfc1 $t1, $31
sw $t1, 20($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.eq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 24($s7)
mfhc1 $t0, $f6
sw $t0, 28($s7)
cfc1 $t1, $31
sw $t1, 32($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 36($s7)
mfhc1 $t0, $f6
sw $t0, 40($s7)
cfc1 $t1, $31
sw $t1, 44($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.lt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 48($s7)
mfhc1 $t0, $f6
sw $t0, 52($s7)
cfc1 $t1, $31
sw $t1, 56($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 60($s7)
mfhc1 $t0, $f6
sw $t0, 64($s7)
cfc1 $t1, $31
sw $t1, 68($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.le.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 72($s7)
mfhc1 $t0, $f6
sw $t0, 76($s7)
cfc1 $t1, $31
sw $t1, 80($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 84($s7)
mfhc1 $t0, $f6
sw $t0, 88($s7)
cfc1 $t1, $31
sw $t1, 92($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.saf.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 96($s7)
mfhc1 $t0, $f6
sw $t0, 100($s7)
cfc1 $t1, $31
sw $t1, 104($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sun.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 108($s7)
mfhc1 $t0, $f6
sw $t0, 112($s7)
cfc1 $t1, $31
sw $t1, 116($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.seq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 120($s7)
mfhc1 $t0, $f6
sw $t0, 124($s7)
cfc1 $t1, $31
sw $t1, 128($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 132($s7)
mfhc1 $t0, $f6
sw $t0, 136($s7)
cfc1 $t1, $31
sw $t1, 140($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.slt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 144($s7)
mfhc1 $t0, $f6
sw $t0, 148($s7)
cfc1 $t1, $31
sw $t1, 152($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 156($s7)
mfhc1 $t0, $f6
sw $t0, 160($s7)
cfc1 $t1, $31
sw $t1, 164($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sle.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 168($s7)
mfhc1 $t0, $f6
sw $t0, 172($s7)
cfc1 $t1, $31
sw $t1, 176($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 180($s7)
mfhc1 $t0, $f6
sw $t0, 184($s7)
cfc1 $t1, $31
sw $t1, 188($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41191  # cmp.or.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 192($s7)
mfhc1 $t0, $f6
sw $t0, 196($s7)
cfc1 $t1, $31
sw $t1, 200($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41192  # cmp.une.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 204($s7)
mfhc1 $t0, $f6
sw $t0, 208($s7)
cfc1 $t1, $31
sw $t1, 212($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41193  # cmp.ne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 216($s7)
mfhc1 $t0, $f6
sw $t0, 220($s7)
cfc1 $t1, $31
sw $t1, 224($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41199  # cmp.sor.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 228($s7)
mfhc1 $t0, $f6
sw $t0, 232($s7)
cfc1 $t1, $31
sw $t1, 236($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119a  # cmp.sune.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 240($s7)
mfhc1 $t0, $f6
sw $t0, 244($s7)
cfc1 $t1, $31
sw $t1, 248($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119b  # cmp.sne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 252($s7)
mfhc1 $t0, $f6
sw $t0, 256($s7)
cfc1 $t1, $31
sw $t1, 260($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40000000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x3ff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
cmp.af.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 264($s7)
mfhc1 $t0, $f6
sw $t0, 268($s7)
cfc1 $t1, $31
sw $t1, 272($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.un.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 276($s7)
mfhc1 $t0, $f6
sw $t0, 280($s7)
cfc1 $t1, $31
sw $t1, 284($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.eq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 288($s7)
mfhc1 $t0, $f6
sw $t0, 292($s7)
cfc1 $t1, $31
sw $t1, 296($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 300($s7)
mfhc1 $t0, $f6
sw $t0, 304($s7)
cfc1 $t1, $31
sw $t1, 308($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.lt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 312($s7)
mfhc1 $t0, $f6
sw $t0, 316($s7)
cfc1 $t1, $31
sw $t1, 320($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 324($s7)
mfhc1 $t0, $f6
sw $t0, 328($s7)
cfc1 $t1, $31
sw $t1, 332($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.le.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 336($s7)
mfhc1 $t0, $f6
sw $t0, 340($s7)
cfc1 $t1, $31
sw $t1, 344($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 348($s7)
mfhc1 $t0, $f6
sw $t0, 352($s7)
cfc1 $t1, $31
sw $t1, 356($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.saf.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 360($s7)
mfhc1 $t0, $f6
sw $t0, 364($s7)
cfc1 $t1, $31
sw $t1, 368($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sun.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 372($s7)
mfhc1 $t0, $f6
sw $t0, 376($s7)
cfc1 $t1, $31
sw $t1, 380($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.seq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 384($s7)
mfhc1 $t0, $f6
sw $t0, 388($s7)
cfc1 $t1, $31
sw $t1, 392($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 396($s7)
mfhc1 $t0, $f6
sw $t0, 400($s7)
cfc1 $t1, $31
sw $t1, 404($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.slt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 408($s7)
mfhc1 $t0, $f6
sw $t0, 412($s7)
cfc1 $t1, $31
sw $t1, 416($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 420($s7)
mfhc1 $t0, $f6
sw $t0, 424($s7)
cfc1 $t1, $31
sw $t1, 428($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sle.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 432($s7)
mfhc1 $t0, $f6
sw $t0, 436($s7)
cfc1 $t1, $31
sw $t1, 440($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 444($s7)
mfhc1 $t0, $f6
sw $t0, 448($s7)
cfc1 $t1, $31
sw $t1, 452($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41191  # cmp.or.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 456($s7)
mfhc1 $t0, $f6
sw $t0, 460($s7)
cfc1 $t1, $31
sw $t1, 464($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41192  # cmp.une.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 468($s7)
mfhc1 $t0, $f6
sw $t0, 472($s7)
cfc1 $t1, $31
sw $t1, 476($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41193  # cmp.ne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 480($s7)
mfhc1 $t0, $f6
sw $t0, 484($s7)
cfc1 $t1, $31
sw $t1, 488($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41199  # cmp.sor.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 492($s7)
mfhc1 $t0, $f6
sw $t0, 496($s7)
cfc1 $t1, $31
sw $t1, 500($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119a  # cmp.sune.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 504($s7)
mfhc1 $t0, $f6
sw $t0, 508($s7)
cfc1 $t1, $31
sw $t1, 512($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119b  # cmp.sne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 516($s7)
mfhc1 $t0, $f6
sw $t0, 520($s7)
cfc1 $t1, $31
sw $t1, 524($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x3ff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
cmp.af.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 528($s7)
mfhc1 $t0, $f6
sw $t0, 532($s7)
cfc1 $t1, $31
sw $t1, 536($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.un.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 540($s7)
mfhc1 $t0, $f6
sw $t0, 544($s7)
cfc1 $t1, $31
sw $t1, 548($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.eq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 552($s7)
mfhc1 $t0, $f6
sw $t0, 556($s7)
cfc1 $t1, $31
sw $t1, 560($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 564($s7)
mfhc1 $t0, $f6
sw $t0, 568($s7)
cfc1 $t1, $31
sw $t1, 572($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.lt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 576($s7)
mfhc1 $t0, $f6
sw $t0, 580($s7)
cfc1 $t1, $31
sw $t1, 584($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 588($s7)
mfhc1 $t0, $f6
sw $t0, 592($s7)
cfc1 $t1, $31
sw $t1, 596($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.le.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 600($s7)
mfhc1 $t0, $f6
sw $t0, 604($s7)
cfc1 $t1, $31
sw $t1, 608($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 612($s7)
mfhc1 $t0, $f6
sw $t0, 616($s7)
cfc1 $t1, $31
sw $t1, 620($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.saf.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 624($s7)
mfhc1 $t0, $f6
sw $t0, 628($s7)
cfc1 $t1, $31
sw $t1, 632($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sun.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 636($s7)
mfhc1 $t0, $f6
sw $t0, 640($s7)
cfc1 $t1, $31
sw $t1, 644($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.seq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 648($s7)
mfhc1 $t0, $f6
sw $t0, 652($s7)
cfc1 $t1, $31
sw $t1, 656($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 660($s7)
mfhc1 $t0, $f6
sw $t0, 664($s7)
cfc1 $t1, $31
sw $t1, 668($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.slt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 672($s7)
mfhc1 $t0, $f6
sw $t0, 676($s7)
cfc1 $t1, $31
sw $t1, 680($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 684($s7)
mfhc1 $t0, $f6
sw $t0, 688($s7)
cfc1 $t1, $31
sw $t1, 692($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sle.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 696($s7)
mfhc1 $t0, $f6
sw $t0, 700($s7)
cfc1 $t1, $31
sw $t1, 704($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 708($s7)
mfhc1 $t0, $f6
sw $t0, 712($s7)
cfc1 $t1, $31
sw $t1, 716($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41191  # cmp.or.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 720($s7)
mfhc1 $t0, $f6
sw $t0, 724($s7)
cfc1 $t1, $31
sw $t1, 728($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41192  # cmp.une.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 732($s7)
mfhc1 $t0, $f6
sw $t0, 736($s7)
cfc1 $t1, $31
sw $t1, 740($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41193  # cmp.ne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 744($s7)
mfhc1 $t0, $f6
sw $t0, 748($s7)
cfc1 $t1, $31
sw $t1, 752($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41199  # cmp.sor.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 756($s7)
mfhc1 $t0, $f6
sw $t0, 760($s7)
cfc1 $t1, $31
sw $t1, 764($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119a  # cmp.sune.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 768($s7)
mfhc1 $t0, $f6
sw $t0, 772($s7)
cfc1 $t1, $31
sw $t1, 776($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119b  # cmp.sne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 780($s7)
mfhc1 $t0, $f6
sw $t0, 784($s7)
cfc1 $t1, $31
sw $t1, 788($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x00000000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x80000000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
cmp.af.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 792($s7)
mfhc1 $t0, $f6
sw $t0, 796($s7)
cfc1 $t1, $31
sw $t1, 800($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.un.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 804($s7)
mfhc1 $t0, $f6
sw $t0, 808($s7)
cfc1 $t1, $31
sw $t1, 812($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.eq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 816($s7)
mfhc1 $t0, $f6
sw $t0, 820($s7)
cfc1 $t1, $31
sw $t1, 824($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 828($s7)
mfhc1 $t0, $f6
sw $t0, 832($s7)
cfc1 $t1, $31
sw $t1, 836($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.lt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 840($s7)
mfhc1 $t0, $f6
sw $t0, 844($s7)
cfc1 $t1, $31
sw $t1, 848($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 852($s7)
mfhc1 $t0, $f6
sw $t0, 856($s7)
cfc1 $t1, $31
sw $t1, 860($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.le.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 864($s7)
mfhc1 $t0, $f6
sw $t0, 868($s7)
cfc1 $t1, $31
sw $t1, 872($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 876($s7)
mfhc1 $t0, $f6
sw $t0, 880($s7)
cfc1 $t1, $31
sw $t1, 884($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.saf.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 888($s7)
mfhc1 $t0, $f6
sw $t0, 892($s7)
cfc1 $t1, $31
sw $t1, 896($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sun.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 900($s7)
mfhc1 $t0, $f6
sw $t0, 904($s7)
cfc1 $t1, $31
sw $t1, 908($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.seq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 912($s7)
mfhc1 $t0, $f6
sw $t0, 916($s7)
cfc1 $t1, $31
sw $t1, 920($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 924($s7)
mfhc1 $t0, $f6
sw $t0, 928($s7)
cfc1 $t1, $31
sw $t1, 932($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.slt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 936($s7)
mfhc1 $t0, $f6
sw $t0, 940($s7)
cfc1 $t1, $31
sw $t1, 944($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 948($s7)
mfhc1 $t0, $f6
sw $t0, 952($s7)
cfc1 $t1, $31
sw $t1, 956($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sle.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 960($s7)
mfhc1 $t0, $f6
sw $t0, 964($s7)
cfc1 $t1, $31
sw $t1, 968($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 972($s7)
mfhc1 $t0, $f6
sw $t0, 976($s7)
cfc1 $t1, $31
sw $t1, 980($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41191  # cmp.or.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 984($s7)
mfhc1 $t0, $f6
sw $t0, 988($s7)
cfc1 $t1, $31
sw $t1, 992($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41192  # cmp.une.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 996($s7)
mfhc1 $t0, $f6
sw $t0, 1000($s7)
cfc1 $t1, $31
sw $t1, 1004($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41193  # cmp.ne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1008($s7)
mfhc1 $t0, $f6
sw $t0, 1012($s7)
cfc1 $t1, $31
sw $t1, 1016($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41199  # cmp.sor.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1020($s7)
mfhc1 $t0, $f6
sw $t0, 1024($s7)
cfc1 $t1, $31
sw $t1, 1028($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119a  # cmp.sune.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1032($s7)
mfhc1 $t0, $f6
sw $t0, 1036($s7)
cfc1 $t1, $31
sw $t1, 1040($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119b  # cmp.sne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1044($s7)
mfhc1 $t0, $f6
sw $t0, 1048($s7)
cfc1 $t1, $31
sw $t1, 1052($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0xfff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x7ff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
cmp.af.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1056($s7)
mfhc1 $t0, $f6
sw $t0, 1060($s7)
cfc1 $t1, $31
sw $t1, 1064($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.un.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1068($s7)
mfhc1 $t0, $f6
sw $t0, 1072($s7)
cfc1 $t1, $31
sw $t1, 1076($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.eq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1080($s7)
mfhc1 $t0, $f6
sw $t0, 1084($s7)
cfc1 $t1, $31
sw $t1, 1088($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1092($s7)
mfhc1 $t0, $f6
sw $t0, 1096($s7)
cfc1 $t1, $31
sw $t1, 1100($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.lt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1104($s7)
mfhc1 $t0, $f6
sw $t0, 1108($s7)
cfc1 $t1, $31
sw $t1, 1112($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1116($s7)
mfhc1 $t0, $f6
sw $t0, 1120($s7)
cfc1 $t1, $31
sw $t1, 1124($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.le.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1128($s7)
mfhc1 $t0, $f6
sw $t0, 1132($s7)
cfc1 $t1, $31
sw $t1, 1136($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1140($s7)
mfhc1 $t0, $f6
sw $t0, 1144($s7)
cfc1 $t1, $31
sw $t1, 1148($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.saf.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1152($s7)
mfhc1 $t0, $f6
sw $t0, 1156($s7)
cfc1 $t1, $31
sw $t1, 1160($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sun.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1164($s7)
mfhc1 $t0, $f6
sw $t0, 1168($s7)
cfc1 $t1, $31
sw $t1, 1172($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.seq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1176($s7)
mfhc1 $t0, $f6
sw $t0, 1180($s7)
cfc1 $t1, $31
sw $t1, 1184($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1188($s7)
mfhc1 $t0, $f6
sw $t0, 1192($s7)
cfc1 $t1, $31
sw $t1, 1196($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.slt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1200($s7)
mfhc1 $t0, $f6
sw $t0, 1204($s7)
cfc1 $t1, $31
sw $t1, 1208($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1212($s7)
mfhc1 $t0, $f6
sw $t0, 1216($s7)
cfc1 $t1, $31
sw $t1, 1220($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sle.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1224($s7)
mfhc1 $t0, $f6
sw $t0, 1228($s7)
cfc1 $t1, $31
sw $t1, 1232($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1236($s7)
mfhc1 $t0, $f6
sw $t0, 1240($s7)
cfc1 $t1, $31
sw $t1, 1244($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41191  # cmp.or.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1248($s7)
mfhc1 $t0, $f6
sw $t0, 1252($s7)
cfc1 $t1, $31
sw $t1, 1256($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41192  # cmp.une.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1260($s7)
mfhc1 $t0, $f6
sw $t0, 1264($s7)
cfc1 $t1, $31
sw $t1, 1268($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41193  # cmp.ne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1272($s7)
mfhc1 $t0, $f6
sw $t0, 1276($s7)
cfc1 $t1, $31
sw $t1, 1280($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41199  # cmp.sor.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1284($s7)
mfhc1 $t0, $f6
sw $t0, 1288($s7)
cfc1 $t1, $31
sw $t1, 1292($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119a  # cmp.sune.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1296($s7)
mfhc1 $t0, $f6
sw $t0, 1300($s7)
cfc1 $t1, $31
sw $t1, 1304($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119b  # cmp.sne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1308($s7)
mfhc1 $t0, $f6
sw $t0, 1312($s7)
cfc1 $t1, $31
sw $t1, 1316($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x7ff80000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x3ff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
cmp.af.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1320($s7)
mfhc1 $t0, $f6
sw $t0, 1324($s7)
cfc1 $t1, $31
sw $t1, 1328($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.un.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1332($s7)
mfhc1 $t0, $f6
sw $t0, 1336($s7)
cfc1 $t1, $31
sw $t1, 1340($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.eq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1344($s7)
mfhc1 $t0, $f6
sw $t0, 1348($s7)
cfc1 $t1, $31
sw $t1, 1352($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1356($s7)
mfhc1 $t0, $f6
sw $t0, 1360($s7)
cfc1 $t1, $31
sw $t1, 1364($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.lt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1368($s7)
mfhc1 $t0, $f6
sw $t0, 1372($s7)
cfc1 $t1, $31
sw $t1, 1376($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1380($s7)
mfhc1 $t0, $f6
sw $t0, 1384($s7)
cfc1 $t1, $31
sw $t1, 1388($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.le.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1392($s7)
mfhc1 $t0, $f6
sw $t0, 1396($s7)
cfc1 $t1, $31
sw $t1, 1400($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1404($s7)
mfhc1 $t0, $f6
sw $t0, 1408($s7)
cfc1 $t1, $31
sw $t1, 1412($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.saf.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1416($s7)
mfhc1 $t0, $f6
sw $t0, 1420($s7)
cfc1 $t1, $31
sw $t1, 1424($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sun.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1428($s7)
mfhc1 $t0, $f6
sw $t0, 1432($s7)
cfc1 $t1, $31
sw $t1, 1436($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.seq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1440($s7)
mfhc1 $t0, $f6
sw $t0, 1444($s7)
cfc1 $t1, $31
sw $t1, 1448($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1452($s7)
mfhc1 $t0, $f6
sw $t0, 1456($s7)
cfc1 $t1, $31
sw $t1, 1460($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.slt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1464($s7)
mfhc1 $t0, $f6
sw $t0, 1468($s7)
cfc1 $t1, $31
sw $t1, 1472($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1476($s7)
mfhc1 $t0, $f6
sw $t0, 1480($s7)
cfc1 $t1, $31
sw $t1, 1484($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sle.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1488($s7)
mfhc1 $t0, $f6
sw $t0, 1492($s7)
cfc1 $t1, $31
sw $t1, 1496($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1500($s7)
mfhc1 $t0, $f6
sw $t0, 1504($s7)
cfc1 $t1, $31
sw $t1, 1508($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41191  # cmp.or.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1512($s7)
mfhc1 $t0, $f6
sw $t0, 1516($s7)
cfc1 $t1, $31
sw $t1, 1520($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41192  # cmp.une.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1524($s7)
mfhc1 $t0, $f6
sw $t0, 1528($s7)
cfc1 $t1, $31
sw $t1, 1532($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41193  # cmp.ne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1536($s7)
mfhc1 $t0, $f6
sw $t0, 1540($s7)
cfc1 $t1, $31
sw $t1, 1544($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41199  # cmp.sor.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1548($s7)
mfhc1 $t0, $f6
sw $t0, 1552($s7)
cfc1 $t1, $31
sw $t1, 1556($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119a  # cmp.sune.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1560($s7)
mfhc1 $t0, $f6
sw $t0, 1564($s7)
cfc1 $t1, $31
sw $t1, 1568($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119b  # cmp.sne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1572($s7)
mfhc1 $t0, $f6
sw $t0, 1576($s7)
cfc1 $t1, $31
sw $t1, 1580($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mthc1 $t9, $f2
li $t9, 0x00000001
mtc1 $t9, $f4
li $t9, 0x7ff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
cmp.af.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1584($s7)
mfhc1 $t0, $f6
sw $t0, 1588($s7)
cfc1 $t1, $31
sw $t1, 1592($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.un.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1596($s7)
mfhc1 $t0, $f6
sw $t0, 1600($s7)
cfc1 $t1, $31
sw $t1, 1604($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.eq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1608($s7)
mfhc1 $t0, $f6
sw $t0, 1612($s7)
cfc1 $t1, $31
sw $t1, 1616($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1620($s7)
mfhc1 $t0, $f6
sw $t0, 1624($s7)
cfc1 $t1, $31
sw $t1, 1628($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.lt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1632($s7)
mfhc1 $t0, $f6
sw $t0, 1636($s7)
cfc1 $t1, $31
sw $t1, 1640($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1644($s7)
mfhc1 $t0, $f6
sw $t0, 1648($s7)
cfc1 $t1, $31
sw $t1, 1652($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.le.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1656($s7)
mfhc1 $t0, $f6
sw $t0, 1660($s7)
cfc1 $t1, $31
sw $t1, 1664($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1668($s7)
mfhc1 $t0, $f6
sw $t0, 1672($s7)
cfc1 $t1, $31
sw $t1, 1676($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.saf.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1680($s7)
mfhc1 $t0, $f6
sw $t0, 1684($s7)
cfc1 $t1, $31
sw $t1, 1688($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sun.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1692($s7)
mfhc1 $t0, $f6
sw $t0, 1696($s7)
cfc1 $t1, $31
sw $t1, 1700($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.seq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1704($s7)
mfhc1 $t0, $f6
sw $t0, 1708($s7)
cfc1 $t1, $31
sw $t1, 1712($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1716($s7)
mfhc1 $t0, $f6
sw $t0, 1720($s7)
cfc1 $t1, $31
sw $t1, 1724($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.slt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1728($s7)
mfhc1 $t0, $f6
sw $t0, 1732($s7)
cfc1 $t1, $31
sw $t1, 1736($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1740($s7)
mfhc1 $t0, $f6
sw $t0, 1744($s7)
cfc1 $t1, $31
sw $t1, 1748($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sle.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1752($s7)
mfhc1 $t0, $f6
sw $t0, 1756($s7)
cfc1 $t1, $31
sw $t1, 1760($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1764($s7)
mfhc1 $t0, $f6
sw $t0, 1768($s7)
cfc1 $t1, $31
sw $t1, 1772($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41191  # cmp.or.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1776($s7)
mfhc1 $t0, $f6
sw $t0, 1780($s7)
cfc1 $t1, $31
sw $t1, 1784($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41192  # cmp.une.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1788($s7)
mfhc1 $t0, $f6
sw $t0, 1792($s7)
cfc1 $t1, $31
sw $t1, 1796($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41193  # cmp.ne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1800($s7)
mfhc1 $t0, $f6
sw $t0, 1804($s7)
cfc1 $t1, $31
sw $t1, 1808($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41199  # cmp.sor.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1812($s7)
mfhc1 $t0, $f6
sw $t0, 1816($s7)
cfc1 $t1, $31
sw $t1, 1820($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119a  # cmp.sune.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1824($s7)
mfhc1 $t0, $f6
sw $t0, 1828($s7)
cfc1 $t1, $31
sw $t1, 1832($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119b  # cmp.sne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1836($s7)
mfhc1 $t0, $f6
sw $t0, 1840($s7)
cfc1 $t1, $31
sw $t1, 1844($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x7ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x7ff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
cmp.af.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1848($s7)
mfhc1 $t0, $f6
sw $t0, 1852($s7)
cfc1 $t1, $31
sw $t1, 1856($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.un.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1860($s7)
mfhc1 $t0, $f6
sw $t0, 1864($s7)
cfc1 $t1, $31
sw $t1, 1868($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.eq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1872($s7)
mfhc1 $t0, $f6
sw $t0, 1876($s7)
cfc1 $t1, $31
sw $t1, 1880($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1884($s7)
mfhc1 $t0, $f6
sw $t0, 1888($s7)
cfc1 $t1, $31
sw $t1, 1892($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.lt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1896($s7)
mfhc1 $t0, $f6
sw $t0, 1900($s7)
cfc1 $t1, $31
sw $t1, 1904($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1908($s7)
mfhc1 $t0, $f6
sw $t0, 1912($s7)
cfc1 $t1, $31
sw $t1, 1916($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.le.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1920($s7)
mfhc1 $t0, $f6
sw $t0, 1924($s7)
cfc1 $t1, $31
sw $t1, 1928($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.ule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1932($s7)
mfhc1 $t0, $f6
sw $t0, 1936($s7)
cfc1 $t1, $31
sw $t1, 1940($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.saf.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1944($s7)
mfhc1 $t0, $f6
sw $t0, 1948($s7)
cfc1 $t1, $31
sw $t1, 1952($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sun.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1956($s7)
mfhc1 $t0, $f6
sw $t0, 1960($s7)
cfc1 $t1, $31
sw $t1, 1964($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.seq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1968($s7)
mfhc1 $t0, $f6
sw $t0, 1972($s7)
cfc1 $t1, $31
sw $t1, 1976($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sueq.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1980($s7)
mfhc1 $t0, $f6
sw $t0, 1984($s7)
cfc1 $t1, $31
sw $t1, 1988($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.slt.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 1992($s7)
mfhc1 $t0, $f6
sw $t0, 1996($s7)
cfc1 $t1, $31
sw $t1, 2000($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sult.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 2004($s7)
mfhc1 $t0, $f6
sw $t0, 2008($s7)
cfc1 $t1, $31
sw $t1, 2012($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sle.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 2016($s7)
mfhc1 $t0, $f6
sw $t0, 2020($s7)
cfc1 $t1, $31
sw $t1, 2024($s7)
li $t8, 0x00000000
ctc1 $t8, $31
cmp.sule.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 2028($s7)
mfhc1 $t0, $f6
sw $t0, 2032($s7)
cfc1 $t1, $31
sw $t1, 2036($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41191  # cmp.or.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 2040($s7)
mfhc1 $t0, $f6
sw $t0, 2044($s7)
cfc1 $t1, $31
sw $t1, 2048($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41192  # cmp.une.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 2052($s7)
mfhc1 $t0, $f6
sw $t0, 2056($s7)
cfc1 $t1, $31
sw $t1, 2060($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41193  # cmp.ne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 2064($s7)
mfhc1 $t0, $f6
sw $t0, 2068($s7)
cfc1 $t1, $31
sw $t1, 2072($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a41199  # cmp.sor.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 2076($s7)
mfhc1 $t0, $f6
sw $t0, 2080($s7)
cfc1 $t1, $31
sw $t1, 2084($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119a  # cmp.sune.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 2088($s7)
mfhc1 $t0, $f6
sw $t0, 2092($s7)
cfc1 $t1, $31
sw $t1, 2096($s7)
li $t8, 0x00000000
ctc1 $t8, $31
.word 0x46a4119b  # cmp.sne.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 2100($s7)
mfhc1 $t0, $f6
sw $t0, 2104($s7)
cfc1 $t1, $31
sw $t1, 2108($s7)
li $v0, 10
syscall
