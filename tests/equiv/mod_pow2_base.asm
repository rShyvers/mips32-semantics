# mod_pow2_base.asm — $t9 = $a0 % 4, signed, the remainder taking the sign of the dividend (as
# the truncating division of div_pow2_base.asm): e.g. -1 % 4 = -1, not 3. Branch-free:
# ((x + b) & 3) - b with b = 3 for a negative x, else 0.
# Release 6 removed DIV/MFHI; the Release 6 MOD is not modeled yet (W4).
.text
main:
    sra  $t1, $a0, 31        # 0 or -1
    srl  $t1, $t1, 30        # 0 or 3
    addu $t2, $a0, $t1
    andi $t2, $t2, 3
    subu $t9, $t2, $t1
    li   $v0, 10
    syscall
