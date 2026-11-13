# Coprocessor Unusable: with Status.CU1 = 0 an FP instruction raises ExcCode 11 with
# Cause.CE = 1; the .ktext handler prints both, sets CU1 and returns with eret, and
# the instruction is re-executed. MD00090 Vol III Rev 6.02 6.2.22 (p.100).
# Expected output: "11 1 1077936128 2 "
# Standard syntax; every branch/jump is followed by its delay-slot instruction.
        .set noreorder
        .ktext
handler:
        mfc0  $k0, $13            # Cause
        srl   $k1, $k0, 2
        andi  $a0, $k1, 31        # ExcCode: 11 = CpU
        li    $v0, 1
        syscall
        li    $a0, 32
        li    $v0, 11
        syscall
        srl   $k1, $k0, 28
        andi  $a0, $k1, 3         # CE: 1
        li    $v0, 1
        syscall
        li    $a0, 32
        li    $v0, 11
        syscall
        lui   $k0, 0x2000
        ori   $k0, $k0, 2         # CU1 | EXL
        mtc0  $k0, $12            # enable coprocessor 1
        eret                      # re-executes the faulting instruction
        .text
main:
        li    $t0, 0x3f800000
        mtc1  $t0, $f4            # CU1 = 1 initially
        li    $t0, 0x40000000
        mtc1  $t0, $f6
        mtc0  $zero, $12          # Status = 0: CU1 cleared
        add.s $f2, $f4, $f6       # Coprocessor Unusable -> handler -> retried
        mfc1  $a0, $f2            # 3.0
        jal   pint
        nop
        mfc0  $a0, $12            # Status: CU1 set, EXL clear
        srl   $a0, $a0, 28
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
