# LDC1 requires a doubleword-aligned address: 'An Address Error exception occurs if
# EffectiveAddress2..0 != 0' (MD00086 Vol II-A Rev 6.06 LDC1, p.215). With no handler
# installed the model halts with unhandledException 4 (AdEL).
# Expected output: "4"
# Expected halt: unhandledException 4
# Standard syntax; every branch/jump is followed by its delay-slot instruction.
        .set noreorder
        .data
        .align 3
buf:    .word 1, 2, 3, 4
        .text
main:
        la    $t0, buf
        ldc1  $f2, 8($t0)         # doubleword-aligned: fine
        mfc1  $a0, $f2            # low word = the word at buf+12
        li    $v0, 1
        syscall
        ldc1  $f2, 4($t0)         # word-aligned only: Address Error (AdEL), no handler
        li    $v0, 10
        syscall
