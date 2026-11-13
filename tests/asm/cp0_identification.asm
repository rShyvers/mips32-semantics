# Read-only identification registers PRId (15,0), Config (16,0), Config1 (16,1), the
# DI/EI instructions, the writable Cause bits, and PREF as a no-op.
# MD00090 Vol III Rev 6.02 9.40 (p.221), 9.45 (p.233), 9.46, 9.36 (p.209);
# MD00086 Vol II-A Rev 6.06 DI (p.164), EI (p.176), PREF (p.321).
# Expected output: "65536 10748037 1 2 1 0 142607104 255 "
# Standard syntax; every branch/jump is followed by its delay-slot instruction.
        .set noreorder
        .text
main:
        mfc0  $a0, $15            # PRId
        jal   pint
        nop
        mfc0  $a0, $16            # Config: M | K23=2 | KU=2 | BE | AR=1 | MT=3 (Fixed Mapping) | K0=2 = 0xA4008582
        srl   $a0, $a0, 8
        jal   pint
        nop
        mfc0  $a0, $16, 1         # Config1: FP
        jal   pint
        nop
        ei    $t0                 # $t0 = old Status, IE := 1
        srl   $a0, $t0, 28
        jal   pint
        nop
        di    $t1                 # $t1 = Status with IE set, IE := 0
        andi  $a0, $t1, 1
        jal   pint
        nop
        mfc0  $a0, $12
        andi  $a0, $a0, 1
        jal   pint
        nop
        li    $t0, -1
        mtc0  $t0, $13            # Cause: only DC, IV, IP1..0 are writable
        mfc0  $a0, $13
        jal   pint
        nop
        pref  0, 1($zero)         # prefetch never raises
        sb    $t0, 0($sp)
        lbu   $a0, 0($sp)
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
