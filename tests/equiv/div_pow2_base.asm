# div_pow2_base.asm — $t9 = $a0 / 4, signed, truncating toward zero, branch-free: add the bias 3
# only for a negative dividend (the sign mask shifted right logically by 30), then sra by 2.
# Release 6 removed DIV/MFLO; the Release 6 DIV is not modeled yet (W4).
.text
main:
    sra  $t1, $a0, 31        # 0 or -1
    srl  $t1, $t1, 30        # 0 or 3
    addu $t1, $a0, $t1
    sra  $t9, $t1, 2
    li   $v0, 10
    syscall
