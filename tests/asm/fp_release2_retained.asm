# Release 2 FP instructions Release 6 keeps: MFHC1/MTHC1, RECIP and RSQRT (the indexed
# loads/stores, PREFX and the unfused MADD family are removed in Release 6: MD00086 Vol II-A
# Rev 6.06, Table A.21, p.459). LDC1/SDC1 move a little-endian doubleword: the word at the lower
# address is the low half.
# MD00086 Vol II-A Rev 6.06 MFHC1 (p.271), RECIP.fmt (p.336).
# Expected output: "1073217536 1074266112 1056964608 1056964608 1056964608 1073741824 0 "
# Standard syntax; every branch/jump is followed by its delay-slot instruction.
        .set noreorder
        .data
        .align 3
buf:    .double 1.5                       # low word 0x00000000, high word 0x3ff80000
        .word 0, 0
        .float 2.0
        .text
main:
        la    $s0, buf
        ldc1  $f4, 0($s0)         # 1.5
        mfhc1 $a0, $f4            # high word 0x3ff80000
        jal   pint
        nop
        add.d $f6, $f4, $f4       # 3.0
        sdc1  $f6, 8($s0)
        lw    $a0, 12($s0)        # high word of 3.0 at the higher address: 0x40080000
        jal   pint
        nop
        lwc1  $f8, 16($s0)        # 2.0f
        recip.s $f2, $f8          # 0.5
        mfc1  $a0, $f2
        jal   pint
        nop
        li    $t0, 0x40800000
        mtc1  $t0, $f14
        rsqrt.s $f2, $f14         # 1/sqrt(4) = 0.5
        mfc1  $a0, $f2
        jal   pint
        nop
        swc1  $f2, 8($s0)
        lw    $a0, 8($s0)
        jal   pint
        nop
        li    $t0, 0x40100000
        mthc1 $t0, $f4            # high word := 0x40100000 -> 4.0
        sqrt.d $f6, $f4           # 2.0
        mfhc1 $a0, $f6            # 0x40000000
        jal   pint
        nop
        cfc1  $a0, $31            # nothing raised
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
