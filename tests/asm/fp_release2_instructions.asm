# Release 2 FP instructions: indexed loads/stores (LWXC1/LDXC1/SWXC1/SDXC1), PREFX,
# MFHC1/MTHC1, the unfused MADD/MSUB/NMADD/NMSUB, RECIP and RSQRT.
# MD00086 Vol II-A Rev 6.06 MADD.fmt (p.256), LDXC1 (p.218), MFHC1 (p.271), RECIP.fmt (p.336).
# Expected output: "1073217536 1074266112 1088421888 1084227584 -1059061760 -1063256064 1056964608 1056964608 1056964608 1073741824 0 "
# Standard syntax; every branch/jump is followed by its delay-slot instruction.
        .set noreorder
        .data
        .align 3
buf:    .word 0x3ff80000, 0x00000000      # 1.5 as a big-endian doubleword
        .word 0, 0
        .float 2.0
        .text
main:
        la    $s0, buf
        li    $s1, 8
        li    $s2, 16
        ldxc1 $f4, $zero($s0)     # 1.5
        mfhc1 $a0, $f4            # high word 0x3ff80000
        jal   pint
        nop
        add.d $f6, $f4, $f4       # 3.0
        sdxc1 $f6, $s1($s0)
        lw    $a0, 8($s0)         # 0x40080000
        jal   pint
        nop
        lwxc1 $f8, $s2($s0)       # 2.0f
        li    $t0, 0x40400000
        mtc1  $t0, $f10           # 3.0f
        li    $t0, 0x3f800000
        mtc1  $t0, $f12           # 1.0f
        madd.s $f2, $f12, $f8, $f10   # 2*3+1 = 7.0
        mfc1  $a0, $f2
        jal   pint
        nop
        msub.s $f2, $f12, $f8, $f10   # 5.0
        mfc1  $a0, $f2
        jal   pint
        nop
        nmadd.s $f2, $f12, $f8, $f10  # -7.0
        mfc1  $a0, $f2
        jal   pint
        nop
        nmsub.s $f2, $f12, $f8, $f10  # -5.0
        mfc1  $a0, $f2
        jal   pint
        nop
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
        swxc1 $f2, $s1($s0)
        lw    $a0, 8($s0)
        jal   pint
        nop
        li    $t0, 0x40100000
        mthc1 $t0, $f4            # high word := 0x40100000 -> 4.0
        sqrt.d $f6, $f4           # 2.0
        mfhc1 $a0, $f6            # 0x40000000
        jal   pint
        nop
        prefx 0, $s1($s0)
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
