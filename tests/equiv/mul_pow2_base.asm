# mul_pow2_base.asm — $t9 = $a0 * 8 (mod 2^32), with the Release 6 MUL (MD00086 Vol II-A Rev 6.06,
# MUL MUH MULU MUHU, p.300-301). Input: $a0 (signed). Output: $t9. Exits cleanly (syscall 10) so
# EquivHarness can read $t9 back.
.text
main:
    li   $t1, 8
    mul  $t9, $a0, $t1
    li   $v0, 10
    syscall
