# mul_const5_base.asm — $t9 = $a0 * 5 (mod 2^32), as 4*x + x with wrapping doublings (addu).
# Release 6 removed MULT/MFLO; the Release 6 MUL is not modeled yet (W4).
.text
main:
    addu $t1, $a0, $a0
    addu $t1, $t1, $t1
    addu $t9, $t1, $a0
    li   $v0, 10
    syscall
