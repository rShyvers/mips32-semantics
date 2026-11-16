# mul_pow2_base.asm — $t9 = $a0 * 8 (mod 2^32), computed by three wrapping doublings (addu).
# Release 6 removed MULT/MFLO; the Release 6 MUL is not modeled yet (W4). Input: $a0 (signed).
# Output: $t9. Exits cleanly (syscall 10) so EquivHarness can read $t9 back.
.text
main:
    addu $t9, $a0, $a0
    addu $t9, $t9, $t9
    addu $t9, $t9, $t9
    li   $v0, 10
    syscall
