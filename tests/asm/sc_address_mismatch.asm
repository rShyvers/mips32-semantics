# SC fails when its address differs from the preceding LL's.
# MD00086 Vol II-A Rev 6.06 SC (p.347): 'An SC will fail if the aligned address of the
# SC does not match that of the preceding LL.'
# Expected output: "0 6 1 6 0 "
# Standard syntax; every branch/jump is followed by its delay-slot instruction.
        .set noreorder
        .data
cell:   .word 5, 6
        .text
main:
        la    $t0, cell
        ll    $t1, 0($t0)
        li    $t2, 99
        sc    $t2, 4($t0)         # address differs from the ll's: fails, no store
        move  $a0, $t2
        jal   pint
        nop
        lw    $a0, 4($t0)
        jal   pint
        nop
        ll    $t1, 0($t0)
        addiu $t2, $t1, 1
        sc    $t2, 0($t0)         # same address: succeeds
        move  $a0, $t2
        jal   pint
        nop
        lw    $a0, 0($t0)
        jal   pint
        nop
        li    $t2, 77
        sc    $t2, 0($t0)         # no ll since the last sc: fails
        move  $a0, $t2
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
