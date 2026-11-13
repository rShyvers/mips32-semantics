# round/trunc/ceil/floor.w.s and .w.d use their own rounding direction whatever
# FCSR.RM is; NaN, infinities and out-of-range values (either sign) convert to
# 0x7fffffff with Invalid Operation (FCSR 0x00010040 = 65600).
# MD00082 Vol I-A Rev 6.01 Table 6.3 (p.82); MD00086 Vol II-A Rev 6.06 ROUND.W.fmt (p.342).
# Expected output: "2 2 3 2 -2 -2 -2 -3 4 3 4 3 2147483647 2147483647 2147483647 2147483647 2147483647 65600 2 2 3 2 "
# Standard syntax; every branch/jump is followed by its delay-slot instruction.
        .set noreorder
        .text
main:
        li    $t1, 3
        ctc1  $t1, $31            # RM = 3: must not affect round/trunc/ceil/floor
        li    $t0, 0x40200000
        mtc1  $t0, $f4
        round.w.s $f2, $f4        # round(2.5)
        mfc1  $a0, $f2
        jal   pint
        nop
        trunc.w.s $f2, $f4        # trunc(2.5)
        mfc1  $a0, $f2
        jal   pint
        nop
        ceil.w.s $f2, $f4        # ceil(2.5)
        mfc1  $a0, $f2
        jal   pint
        nop
        floor.w.s $f2, $f4        # floor(2.5)
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t0, 0xc0200000
        mtc1  $t0, $f4
        round.w.s $f2, $f4        # round(-2.5)
        mfc1  $a0, $f2
        jal   pint
        nop
        trunc.w.s $f2, $f4        # trunc(-2.5)
        mfc1  $a0, $f2
        jal   pint
        nop
        ceil.w.s $f2, $f4        # ceil(-2.5)
        mfc1  $a0, $f2
        jal   pint
        nop
        floor.w.s $f2, $f4        # floor(-2.5)
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t0, 0x40600000
        mtc1  $t0, $f4
        round.w.s $f2, $f4        # round(3.5)
        mfc1  $a0, $f2
        jal   pint
        nop
        trunc.w.s $f2, $f4        # trunc(3.5)
        mfc1  $a0, $f2
        jal   pint
        nop
        ceil.w.s $f2, $f4        # ceil(3.5)
        mfc1  $a0, $f2
        jal   pint
        nop
        floor.w.s $f2, $f4        # floor(3.5)
        mfc1  $a0, $f2
        jal   pint
        nop
        ctc1  $zero, $31
        li    $t0, 0x7fbfffff
        mtc1  $t0, $f4
        cvt.w.s $f2, $f4          # QNaN: invalid -> 0x7fffffff
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t0, 0x7f800000
        mtc1  $t0, $f4
        cvt.w.s $f2, $f4          # +inf: invalid -> 0x7fffffff
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t0, 0xff800000
        mtc1  $t0, $f4
        cvt.w.s $f2, $f4          # -inf: invalid -> 0x7fffffff
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t0, 0x4f000000
        mtc1  $t0, $f4
        cvt.w.s $f2, $f4          # 2^31: invalid -> 0x7fffffff
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t0, 0xdf000000
        mtc1  $t0, $f4
        cvt.w.s $f2, $f4          # -2^63: invalid -> 0x7fffffff
        mfc1  $a0, $f2
        jal   pint
        nop
        cfc1  $a0, $31
        jal   pint
        nop
        ctc1  $zero, $31
        li    $t0, 0x40040000     # 2.5 as a double: high word in $f5, low in $f4
        mtc1  $t0, $f5
        mtc1  $zero, $f4
        round.w.d $f2, $f4
        mfc1  $a0, $f2
        jal   pint
        nop
        trunc.w.d $f2, $f4
        mfc1  $a0, $f2
        jal   pint
        nop
        ceil.w.d $f2, $f4
        mfc1  $a0, $f2
        jal   pint
        nop
        floor.w.d $f2, $f4
        mfc1  $a0, $f2
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
