# C.cond.fmt: quiet vs signaling predicates on a QNaN, condition codes other than 0,
# FCCR, bc1t/bc1f/bc1tl/bc1fl with a cc operand, movf/movt (GPR) and
# movf.s/movt.s/movn.s/movz.s.
# MD00086 Vol II-A Rev 6.06 C.cond.fmt (p.110-113), BC1TL (p.62), MOVF (p.276).
# Expected output: "0 8388608 65600 8454208 134217728 8 10 15 11 22 1101004800 1092616192 1092616192 1101004800 "
# Standard syntax; every branch/jump is followed by its delay-slot instruction.
        .set noreorder
        .text
main:
        li    $t0, 0x7fbfffff
        mtc1  $t0, $f4
        li    $t0, 0x3f800000
        mtc1  $t0, $f6
        c.eq.s $f4, $f6           # quiet predicate, QNaN: false, no exception
        cfc1  $a0, $31
        jal   pint
        nop
        c.un.s $f4, $f6           # unordered: true -> FCC0 (bit 23)
        cfc1  $a0, $31
        jal   pint
        nop
        ctc1  $zero, $31
        c.seq.s $f4, $f6          # signaling predicate, QNaN: Invalid, false
        cfc1  $a0, $31
        jal   pint
        nop
        ctc1  $zero, $31
        c.ngle.s $f4, $f6         # signaling, unordered: Invalid, true
        cfc1  $a0, $31
        jal   pint
        nop
        ctc1  $zero, $31
        li    $t0, 0x3f800000
        mtc1  $t0, $f4
        li    $t0, 0x40000000
        mtc1  $t0, $f6
        c.lt.s $fcc3, $f4, $f6    # 1.0 < 2.0 -> FCC3 (bit 27)
        cfc1  $a0, $31
        jal   pint
        nop
        cfc1  $a0, $25            # FCCR: FCC3 is bit 3
        jal   pint
        nop
        c.ngt.s $fcc7, $f6, $f4   # 2.0 not-greater-than 1.0: false
        c.nge.s $fcc1, $f4, $f6   # 1.0 not-greater-or-equal 2.0: true -> FCC1
        cfc1  $a0, $25
        jal   pint
        nop
        li    $s0, 0
        bc1t  $fcc3, L1           # taken
        nop
        li    $s0, 100
L1:     bc1f  $fcc3, L2           # not taken: delay slot runs, then falls through
        addiu $s0, $s0, 1
        addiu $s0, $s0, 2
L2:     bc1tl $fcc7, L3           # likely, not taken: delay slot nullified
        addiu $s0, $s0, 50
        addiu $s0, $s0, 4
L3:     bc1fl $fcc7, L4           # likely, taken: delay slot runs
        addiu $s0, $s0, 8
        addiu $s0, $s0, 100
L4:
        move  $a0, $s0
        jal   pint
        nop
        li    $t1, 11
        li    $t2, 22
        li    $t3, 33
        movt  $t3, $t1, $fcc3     # FCC3 = 1: moves
        movf  $t3, $t2, $fcc3     # no move
        move  $a0, $t3
        jal   pint
        nop
        movf  $t3, $t2, $fcc7     # FCC7 = 0: moves
        move  $a0, $t3
        jal   pint
        nop
        li    $t0, 0x41200000
        mtc1  $t0, $f8
        li    $t0, 0x41a00000
        mtc1  $t0, $f10
        movt.s $f8, $f10, $fcc3
        mfc1  $a0, $f8
        jal   pint
        nop
        li    $t0, 0x41200000
        mtc1  $t0, $f8
        movf.s $f8, $f10, $fcc3
        mfc1  $a0, $f8
        jal   pint
        nop
        movn.s $f8, $f10, $zero
        mfc1  $a0, $f8
        jal   pint
        nop
        movz.s $f8, $f10, $zero
        mfc1  $a0, $f8
        jal   pint
        nop
        li    $v0, 10
        syscall

# pint: print $a0 as a signed decimal followed by a space
pint:   li    $v0, 1
        syscall
        li    $a0, 32
        li    $v0, 11
        syscall
        jr    $ra
        nop
