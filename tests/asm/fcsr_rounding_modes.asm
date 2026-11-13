# FCSR.RM selects the rounding of div.s and cvt.w.s; Inexact is recorded in
# FCSR Cause (bit 12) and Flags (bit 2). For each RM = 0..3 prints: bits of 1.0/3.0,
# FCSR after it, cvt.w.s(2.5), cvt.w.s(-2.5).
# MD00082 Vol I-A Rev 6.01 Table 6.10 (p.95); MD00086 Vol II-A Rev 6.06 CVT.W.fmt (p.160).
# Not a MARS test: MARS has no FCSR and its cvt.w.s truncates.
# Expected output: "1051372203 4100 2 -2 1051372202 4101 2 -2 1051372203 4102 3 -2 1051372202 4103 2 -3 "
# Standard syntax; every branch/jump is followed by its delay-slot instruction.
        .set noreorder
        .text
main:
        li    $t1, 0
        ctc1  $t1, $31            # FCSR.RM = 0, flags and cause cleared
        li    $t0, 0x3f800000
        mtc1  $t0, $f4
        li    $t0, 0x40400000
        mtc1  $t0, $f6
        div.s $f2, $f4, $f6       # 1.0 / 3.0: inexact
        mfc1  $a0, $f2
        jal   pint
        nop
        cfc1  $a0, $31
        jal   pint
        nop
        li    $t0, 0x40200000
        mtc1  $t0, $f4
        cvt.w.s $f2, $f4          # 2.5 under FCSR.RM
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t0, 0xc0200000
        mtc1  $t0, $f4
        cvt.w.s $f2, $f4          # -2.5 under FCSR.RM
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t1, 1
        ctc1  $t1, $31            # FCSR.RM = 1, flags and cause cleared
        li    $t0, 0x3f800000
        mtc1  $t0, $f4
        li    $t0, 0x40400000
        mtc1  $t0, $f6
        div.s $f2, $f4, $f6       # 1.0 / 3.0: inexact
        mfc1  $a0, $f2
        jal   pint
        nop
        cfc1  $a0, $31
        jal   pint
        nop
        li    $t0, 0x40200000
        mtc1  $t0, $f4
        cvt.w.s $f2, $f4          # 2.5 under FCSR.RM
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t0, 0xc0200000
        mtc1  $t0, $f4
        cvt.w.s $f2, $f4          # -2.5 under FCSR.RM
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t1, 2
        ctc1  $t1, $31            # FCSR.RM = 2, flags and cause cleared
        li    $t0, 0x3f800000
        mtc1  $t0, $f4
        li    $t0, 0x40400000
        mtc1  $t0, $f6
        div.s $f2, $f4, $f6       # 1.0 / 3.0: inexact
        mfc1  $a0, $f2
        jal   pint
        nop
        cfc1  $a0, $31
        jal   pint
        nop
        li    $t0, 0x40200000
        mtc1  $t0, $f4
        cvt.w.s $f2, $f4          # 2.5 under FCSR.RM
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t0, 0xc0200000
        mtc1  $t0, $f4
        cvt.w.s $f2, $f4          # -2.5 under FCSR.RM
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t1, 3
        ctc1  $t1, $31            # FCSR.RM = 3, flags and cause cleared
        li    $t0, 0x3f800000
        mtc1  $t0, $f4
        li    $t0, 0x40400000
        mtc1  $t0, $f6
        div.s $f2, $f4, $f6       # 1.0 / 3.0: inexact
        mfc1  $a0, $f2
        jal   pint
        nop
        cfc1  $a0, $31
        jal   pint
        nop
        li    $t0, 0x40200000
        mtc1  $t0, $f4
        cvt.w.s $f2, $f4          # 2.5 under FCSR.RM
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t0, 0xc0200000
        mtc1  $t0, $f4
        cvt.w.s $f2, $f4          # -2.5 under FCSR.RM
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
