# Release 6 same-width multiply and divide: MUL/MUH/MULU/MUHU, DIV/MOD/DIVU/MODU (no HI/LO), incl. the edge cases
# -2^31 / -1 (quotient 0x80000000, remainder 0: "(A div B)*B + (A mod B) = A", truncated division) and a zero divisor.
# MD00086 Vol II-A Rev 6.06: MUL MUH MULU MUHU p.300-301; DIV MOD DIVU MODU p.168-169 (Restrictions p.168: "If the divisor in GPR rt
# is zero, the result value is UNPREDICTABLE"; the model's pin, Manual.modelOracle.divByZero: the quotient forms give the dividend,
# the remainder forms 0, the result of dividing by 1, which is what QEMU mips32r6-generic gives).
# oracle: expect gpr:s0=0xfffffff2 gpr:s1=0xffffffff gpr:s2=0xfffffff2 gpr:s3=0x00000006
.data
res: .space 128
.text
la $s7, res
li $t0, 7
li $t1, -2
mul $s0, $t0, $t1           # -14
muh $s1, $t0, $t1           # -1
mulu $s2, $t0, $t1          # low word of 7 * 0xfffffffe = 0xfffffff2
muhu $s3, $t0, $t1          # high word = 6
li $t2, 0x12345678
li $t3, 0x9abcdef0
mul $t4, $t2, $t3
sw $t4, 0($s7)
muh $t4, $t2, $t3
sw $t4, 4($s7)
mulu $t4, $t2, $t3
sw $t4, 8($s7)
muhu $t4, $t2, $t3
sw $t4, 12($s7)
li $t5, 0x80000000
li $t6, -1
mul $t4, $t5, $t6
sw $t4, 16($s7)
muh $t4, $t5, $t5
sw $t4, 20($s7)
muhu $t4, $t6, $t6
sw $t4, 24($s7)
# divide: signs, truncation toward zero, remainder with the sign of the dividend
li $t0, -7
li $t1, 2
div $t4, $t0, $t1           # -3
sw $t4, 28($s7)
mod $t4, $t0, $t1           # -1
sw $t4, 32($s7)
li $t1, -2
div $t4, $t0, $t1           # 3
sw $t4, 36($s7)
mod $t4, $t0, $t1           # -1
sw $t4, 40($s7)
divu $t4, $t0, $t1          # 0xfffffff9 / 0xfffffffe = 0
sw $t4, 44($s7)
modu $t4, $t0, $t1          # 0xfffffff9
sw $t4, 48($s7)
li $t1, 3
divu $t4, $t2, $t1
sw $t4, 52($s7)
modu $t4, $t2, $t1
sw $t4, 56($s7)
# -2^31 / -1
div $t4, $t5, $t6           # 0x80000000
sw $t4, 60($s7)
mod $t4, $t5, $t6           # 0
sw $t4, 64($s7)
divu $t4, $t5, $t6          # 0
sw $t4, 68($s7)
modu $t4, $t5, $t6          # 0x80000000
sw $t4, 72($s7)
# zero divisor (UNPREDICTABLE result; the pin)
div $t4, $t2, $zero
sw $t4, 76($s7)
mod $t4, $t2, $zero
sw $t4, 80($s7)
divu $t4, $t3, $zero
sw $t4, 84($s7)
modu $t4, $t3, $zero
sw $t4, 88($s7)
# rd = $zero: no effect
div $zero, $t2, $zero
mul $zero, $t2, $t3
sw $zero, 92($s7)
li $v0, 10
syscall
