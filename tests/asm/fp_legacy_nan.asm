# Legacy (FIR.Has2008 = 0) NaN behaviour: invalid operations create the default
# QNaN 0x7fbfffff; a signaling NaN (fraction MSB 1) signals Invalid; a quiet NaN
# operand is propagated unchanged; abs.s is arithmetic.
# MD00082 Vol I-A Rev 6.01 6.3.1.4-6.3.1.5 and Table 6.3 (p.81-82); MD00086 Vol II-A
# Rev 6.06 ABS.fmt (p.32). QEMU/Unicorn deviate on abs.s of a NaN; the manual wins.
# Expected output: "2143289343 65600 2143289343 2143289343 2143289343 65600 2139095331 0 2139095331 2139095331 65600 "
# Standard syntax; every branch/jump is followed by its delay-slot instruction.
        .set noreorder
        .text
main:
        li    $t0, 0
        mtc1  $t0, $f4
        li    $t0, 0
        mtc1  $t0, $f6
        div.s $f2, $f4, $f6       # 0/0
        mfc1  $a0, $f2
        jal   pint
        nop
        cfc1  $a0, $31
        jal   pint
        nop
        ctc1  $zero, $31
        li    $t0, 0x7f800000
        mtc1  $t0, $f4
        sub.s $f2, $f4, $f4       # inf - inf
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t0, 0xbf800000
        mtc1  $t0, $f4
        sqrt.s $f2, $f4           # sqrt(-1)
        mfc1  $a0, $f2
        jal   pint
        nop
        ctc1  $zero, $31
        li    $t0, 0x7fc00000
        mtc1  $t0, $f4
        abs.s $f2, $f4            # legacy SNaN: abs is arithmetic -> Invalid
        mfc1  $a0, $f2
        jal   pint
        nop
        cfc1  $a0, $31
        jal   pint
        nop
        ctc1  $zero, $31
        li    $t0, 0x7f800123
        mtc1  $t0, $f4
        li    $t0, 0x3f800000
        mtc1  $t0, $f6
        add.s $f2, $f4, $f6       # QNaN + 1.0: the QNaN is propagated, no exception
        mfc1  $a0, $f2
        jal   pint
        nop
        cfc1  $a0, $31
        jal   pint
        nop
        mov.s $f2, $f4            # non-arithmetic
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t0, 0x7fc00000
        mtc1  $t0, $f6
        add.s $f2, $f6, $f4       # SNaN + QNaN: Invalid, the QNaN operand is the result
        mfc1  $a0, $f2
        jal   pint
        nop
        cfc1  $a0, $31
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
