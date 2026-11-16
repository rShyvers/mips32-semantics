# round/trunc/ceil/floor.w.s and .w.d use their own rounding direction whatever
# FCSR.RM is; with FCSR.NAN2008 = 1 (Release 6) a NaN converts to 0, +inf and values too big to
# 0x7fffffff, -inf and values too small to 0x80000000, with Invalid Operation (FCSR 0x000d0040 =
# 852032: Cause V, Flags V and the read-only ABS2008/NAN2008 bits).
# MD00082 Vol I-A Rev 6.01 Table 6.3 (p.82), Table 6.8 (p.93-94); MD00086 Vol II-A Rev 6.06
# ROUND.W.fmt (p.342).
# Expected output: "2 2 3 2 -2 -2 -2 -3 4 3 4 3 0 2147483647 -2147483648 2147483647 -2147483648 852032 2 2 3 2 "
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
        cvt.w.s $f2, $f4          # SNaN: invalid -> 0
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
        cvt.w.s $f2, $f4          # -inf: invalid -> 0x80000000
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
        cvt.w.s $f2, $f4          # -2^63: invalid -> 0x80000000
        mfc1  $a0, $f2
        jal   pint
        nop
        cfc1  $a0, $31
        jal   pint
        nop
        ctc1  $zero, $31
        li    $t0, 0x40040000     # 2.5 as a double: low word 0, high word via mthc1 (Status.FR = 1: the upper half of $f4)
        mtc1  $zero, $f4
        mthc1 $t0, $f4
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
