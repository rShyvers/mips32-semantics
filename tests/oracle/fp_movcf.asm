# movf/movt (GPR), movf.s/movt.s/movf.d/movt.d and movn/movz.s/.d with condition codes 0 and non-zero.
# cc0 = 1, cc3 = 0, cc5 = 1 are set by compares; a conditional move that does not move leaves the destination unchanged.
# MD00086 Vol II-A Rev 6.06: MOVF p.276, MOVT p.281 (GPR), MOVF.fmt p.277, MOVT.fmt p.282, MOVN.fmt p.280, MOVZ.fmt p.285; C.cond.fmt p.110.
# oracle: expect gpr:s0=0xdead gpr:s1=0x11 gpr:s2=0x11 gpr:s3=0xdead gpr:s4=0x11 gpr:s5=0xdead gpr:s6=0xdead
.data
res: .space 64
.text
la $s7, res
li $t9, 0x3f800000
mtc1 $t9, $f0
li $t9, 0x40000000
mtc1 $t9, $f4
c.lt.s $fcc0, $f0, $f4
c.eq.s $fcc3, $f0, $f4
c.lt.s $fcc5, $f0, $f4
li $t0, 0x11
li $s0, 0xdead
li $s1, 0xdead
li $s2, 0xdead
li $s3, 0xdead
li $s4, 0xdead
li $s5, 0xdead
li $s6, 0xdead
movf $s0, $t0, $fcc0
movt $s1, $t0, $fcc0
movf $s2, $t0, $fcc3
movt $s3, $t0, $fcc3
movt $s4, $t0, $fcc5
movf $s5, $t0, $fcc5
movf $s6, $t0
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f3
li $t9, 0xa00a0000
mtc1 $t9, $f10
mtc1 $t9, $f11
li $t9, 0xa00c0000
mtc1 $t9, $f12
mtc1 $t9, $f13
li $t9, 0xa00e0000
mtc1 $t9, $f14
mtc1 $t9, $f15
li $t9, 0xa0100000
mtc1 $t9, $f16
mtc1 $t9, $f17
li $t9, 0xa0120000
mtc1 $t9, $f18
mtc1 $t9, $f19
li $t9, 0xa0140000
mtc1 $t9, $f20
mtc1 $t9, $f21
li $t9, 0xa0160000
mtc1 $t9, $f22
mtc1 $t9, $f23
li $t9, 0xa0180000
mtc1 $t9, $f24
mtc1 $t9, $f25
movf.s $f10, $f0, $fcc3
movt.s $f12, $f0, $fcc3
movt.d $f14, $f2, $fcc5
movf.d $f16, $f2, $fcc5
movf.s $f18, $f0
movt.s $f20, $f0
movn.s $f22, $f0, $t0
movz.s $f24, $f0, $t0
li $t9, 0xbbbb0000
mtc1 $t9, $f26
mtc1 $t9, $f27
mtc1 $t9, $f28
mtc1 $t9, $f29
movz.d $f26, $f2, $zero
movn.d $f28, $f2, $zero
li $v0, 10
syscall
