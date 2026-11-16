# div_pow2_base.asm — $t9 = $a0 / 4, signed, truncating toward zero, with the Release 6 DIV
# (MD00086 Vol II-A Rev 6.06, DIV MOD DIVU MODU, p.168-169: "(A div B)*B + (A mod B) = A, where
# (A mod B) has same sign as the dividend A").
.text
main:
    li   $t1, 4
    div  $t9, $a0, $t1
    li   $v0, 10
    syscall
