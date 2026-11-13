# An enabled IEEE exception takes the Floating Point exception (ExcCode 15) without
# writing the destination; FCSR.Cause records it and FCSR.Flags is not updated.
# MD00082 Vol I-A Rev 6.01 6.7.1 (p.98-99); MD00090 Vol III Rev 6.02 6.2.23 (p.100).
# Expected output: "15 4224 7 1051372203 4100 "
# Standard syntax; every branch/jump is followed by its delay-slot instruction.
        .set noreorder
        .ktext
handler:
        mfc0  $k0, $13
        srl   $k1, $k0, 2
        andi  $a0, $k1, 31        # ExcCode: 15 = FPE
        li    $v0, 1
        syscall
        li    $a0, 32
        li    $v0, 11
        syscall
        cfc1  $a0, $31            # FCSR: Cause.I (bit 12) | Enables.I (bit 7), Flags untouched
        li    $v0, 1
        syscall
        li    $a0, 32
        li    $v0, 11
        syscall
        ctc1  $zero, $31          # clear the enabled Cause bit before returning
        mfc0  $k0, $14
        addiu $k0, $k0, 4         # skip the trapping instruction
        mtc0  $k0, $14
        eret
        .text
main:
        li    $t0, 7
        mtc1  $t0, $f2            # destination's old contents
        li    $t0, 0x3f800000
        mtc1  $t0, $f4
        li    $t0, 0x40400000
        mtc1  $t0, $f6
        li    $t0, 0x80
        ctc1  $t0, $31            # enable the Inexact trap
        div.s $f2, $f4, $f6       # 1/3 is inexact: Floating Point exception, $f2 not written
        mfc1  $a0, $f2            # still 7
        jal   pint
        nop
        div.s $f2, $f4, $f6       # trap now disabled: default result, Flags.I set
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
