# r_arith.asm — add, sub (Release 6: MULT/DIV/MFHI/MFLO removed; $t4..$t6 stay 0).
# No overflow: all operands well within signed 32-bit range.
.text
main:
    li   $t0, 50
    li   $t1, 20
    add  $t2, $t0, $t1       # 70
    sub  $t3, $t0, $t1       # 30
    andi $a0, $t2, 0x7f
    li   $v0, 11
    syscall
    andi $a0, $t3, 0x7f
    li   $v0, 11
    syscall
    andi $a0, $t4, 0x7f
    li   $v0, 11
    syscall
    andi $a0, $t5, 0x7f
    li   $v0, 11
    syscall
    andi $a0, $t6, 0x7f
    li   $v0, 11
    syscall
    li   $v0, 10
    syscall
