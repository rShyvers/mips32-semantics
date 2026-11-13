# EBase (CP0 register 15, select 1) relocates the general exception vector when
# Status.BEV = 0: after EBase = 0x80001000 a break enters the handler at 0x80001180.
# MD00090 Vol III Rev 6.02 9.41 (p.223-224), 6.2.3 (p.88).
# Expected output: "E1"
# Standard syntax; every branch/jump is followed by its delay-slot instruction.
        .set noreorder
        .ktext 0x80001180
handler:
        li    $a0, 'E'
        li    $v0, 11
        syscall
        mfc0  $a0, $15, 1         # EBase
        srl   $a0, $a0, 12
        andi  $a0, $a0, 0xff
        li    $v0, 1
        syscall
        li    $v0, 10
        syscall
        .text
main:
        mfc0  $t9, $12
        lui   $t0, 0x0040
        or    $t1, $t9, $t0
        mtc0  $t1, $12            # BEV = 1 while EBase is changed
        lui   $t2, 0x8000
        ori   $t2, $t2, 0x1000
        mtc0  $t2, $15, 1         # EBase = 0x80001000
        mtc0  $t9, $12            # BEV = 0 again
        break                     # vectors to EBase + 0x180
        li    $a0, '!'            # not reached
        li    $v0, 11
        syscall
        li    $v0, 10
        syscall
