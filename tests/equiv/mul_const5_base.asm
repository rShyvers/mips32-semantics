# mul_const5_base.asm — $t9 = $a0 * 5 (mod 2^32), with the Release 6 MUL (low word of the product;
# MD00086 Vol II-A Rev 6.06, MUL MUH MULU MUHU, p.300-301).
.text
main:
    li   $t1, 5
    mul  $t9, $a0, $t1
    li   $v0, 10
    syscall
