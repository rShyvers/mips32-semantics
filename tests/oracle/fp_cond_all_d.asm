# All 16 compare predicates x {1<2, 1=1, 2>1, (1,QNaN), (1,SNaN)} on .d with a different cc per predicate; the whole FCSR
# (condition codes + Invalid flag/cause) after each compare is stored to memory.
# MD00086 Vol II-A Rev 6.06 C.cond.fmt p.110-113 (Tables 3.1/3.2: 16 predicates; the signaling ones (cond bit 3) raise Invalid on ANY NaN,
# the quiet ones only on a signaling NaN); FCSR layout MD00082 Vol I-A Rev 6.01 FCSR, FCC0..7 in bits 23, 31..25.
.data
res: .space 384
.text
la $s7, res
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x3ff00000
mtc1 $t9, $f1
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 0($s7)
ctc1 $zero, $31
c.un.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 4($s7)
ctc1 $zero, $31
c.eq.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 8($s7)
ctc1 $zero, $31
c.ueq.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 12($s7)
ctc1 $zero, $31
c.olt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 16($s7)
ctc1 $zero, $31
c.ult.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 20($s7)
ctc1 $zero, $31
c.ole.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 24($s7)
ctc1 $zero, $31
c.ule.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 28($s7)
ctc1 $zero, $31
c.sf.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 32($s7)
ctc1 $zero, $31
c.ngle.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 36($s7)
ctc1 $zero, $31
c.seq.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 40($s7)
ctc1 $zero, $31
c.ngl.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 44($s7)
ctc1 $zero, $31
c.lt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 48($s7)
ctc1 $zero, $31
c.nge.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 52($s7)
ctc1 $zero, $31
c.le.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 56($s7)
ctc1 $zero, $31
c.ngt.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 60($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x3ff00000
mtc1 $t9, $f1
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 64($s7)
ctc1 $zero, $31
c.un.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 68($s7)
ctc1 $zero, $31
c.eq.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 72($s7)
ctc1 $zero, $31
c.ueq.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 76($s7)
ctc1 $zero, $31
c.olt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 80($s7)
ctc1 $zero, $31
c.ult.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 84($s7)
ctc1 $zero, $31
c.ole.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 88($s7)
ctc1 $zero, $31
c.ule.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 92($s7)
ctc1 $zero, $31
c.sf.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 96($s7)
ctc1 $zero, $31
c.ngle.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 100($s7)
ctc1 $zero, $31
c.seq.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 104($s7)
ctc1 $zero, $31
c.ngl.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 108($s7)
ctc1 $zero, $31
c.lt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 112($s7)
ctc1 $zero, $31
c.nge.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 116($s7)
ctc1 $zero, $31
c.le.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 120($s7)
ctc1 $zero, $31
c.ngt.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 124($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x40000000
mtc1 $t9, $f1
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 128($s7)
ctc1 $zero, $31
c.un.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 132($s7)
ctc1 $zero, $31
c.eq.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 136($s7)
ctc1 $zero, $31
c.ueq.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 140($s7)
ctc1 $zero, $31
c.olt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 144($s7)
ctc1 $zero, $31
c.ult.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 148($s7)
ctc1 $zero, $31
c.ole.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 152($s7)
ctc1 $zero, $31
c.ule.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 156($s7)
ctc1 $zero, $31
c.sf.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 160($s7)
ctc1 $zero, $31
c.ngle.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 164($s7)
ctc1 $zero, $31
c.seq.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 168($s7)
ctc1 $zero, $31
c.ngl.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 172($s7)
ctc1 $zero, $31
c.lt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 176($s7)
ctc1 $zero, $31
c.nge.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 180($s7)
ctc1 $zero, $31
c.le.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 184($s7)
ctc1 $zero, $31
c.ngt.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 188($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x3ff00000
mtc1 $t9, $f1
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x7ff80000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 192($s7)
ctc1 $zero, $31
c.un.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 196($s7)
ctc1 $zero, $31
c.eq.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 200($s7)
ctc1 $zero, $31
c.ueq.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 204($s7)
ctc1 $zero, $31
c.olt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 208($s7)
ctc1 $zero, $31
c.ult.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 212($s7)
ctc1 $zero, $31
c.ole.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 216($s7)
ctc1 $zero, $31
c.ule.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 220($s7)
ctc1 $zero, $31
c.sf.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 224($s7)
ctc1 $zero, $31
c.ngle.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 228($s7)
ctc1 $zero, $31
c.seq.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 232($s7)
ctc1 $zero, $31
c.ngl.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 236($s7)
ctc1 $zero, $31
c.lt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 240($s7)
ctc1 $zero, $31
c.nge.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 244($s7)
ctc1 $zero, $31
c.le.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 248($s7)
ctc1 $zero, $31
c.ngt.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 252($s7)
li $t9, 0x00000000
mtc1 $t9, $f0
li $t9, 0x3ff00000
mtc1 $t9, $f1
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x7ff40000
mtc1 $t9, $f3
ctc1 $zero, $31
c.f.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 256($s7)
ctc1 $zero, $31
c.un.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 260($s7)
ctc1 $zero, $31
c.eq.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 264($s7)
ctc1 $zero, $31
c.ueq.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 268($s7)
ctc1 $zero, $31
c.olt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 272($s7)
ctc1 $zero, $31
c.ult.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 276($s7)
ctc1 $zero, $31
c.ole.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 280($s7)
ctc1 $zero, $31
c.ule.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 284($s7)
ctc1 $zero, $31
c.sf.d $fcc0, $f0, $f2
cfc1 $t0, $31
sw $t0, 288($s7)
ctc1 $zero, $31
c.ngle.d $fcc3, $f0, $f2
cfc1 $t0, $31
sw $t0, 292($s7)
ctc1 $zero, $31
c.seq.d $fcc6, $f0, $f2
cfc1 $t0, $31
sw $t0, 296($s7)
ctc1 $zero, $31
c.ngl.d $fcc1, $f0, $f2
cfc1 $t0, $31
sw $t0, 300($s7)
ctc1 $zero, $31
c.lt.d $fcc4, $f0, $f2
cfc1 $t0, $31
sw $t0, 304($s7)
ctc1 $zero, $31
c.nge.d $fcc7, $f0, $f2
cfc1 $t0, $31
sw $t0, 308($s7)
ctc1 $zero, $31
c.le.d $fcc2, $f0, $f2
cfc1 $t0, $31
sw $t0, 312($s7)
ctc1 $zero, $31
c.ngt.d $fcc5, $f0, $f2
cfc1 $t0, $31
sw $t0, 316($s7)
li $v0, 10
syscall
