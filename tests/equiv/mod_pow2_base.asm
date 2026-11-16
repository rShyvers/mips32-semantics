# mod_pow2_base.asm — $t9 = $a0 % 4, signed, the remainder taking the sign of the dividend: e.g.
# -1 % 4 = -1, not 3. The Release 6 MOD (MD00086 Vol II-A Rev 6.06, DIV MOD DIVU MODU, p.168-169).
.text
main:
    li   $t1, 4
    mod  $t9, $a0, $t1
    li   $v0, 10
    syscall
