# mult/multu/div/divu incl. INT_MIN*INT_MIN, INT_MIN / -1, signed remainder sign; mfhi/mflo/mthi/mtlo.
# MD00086 Vol II-A Rev 6.06: MULT p.303, MULTU p.304-305, DIV p.165-169 ("No arithmetic exception occurs under any
# circumstances", only a zero divisor is UNPREDICTABLE), DIVU p.171, MFHI p.273, MFLO p.274, MTHI p.297, MTLO p.298.
# INT_MIN/-1 : quotient 0x80000000 (two's complement wrap), remainder 0.
# oracle: expect gpr:s0=0x80000000 gpr:s1=0x00000000 gpr:s2=0x00000000 gpr:s3=0x40000000
li $t0, 0x80000000
li $t1, -1
div $t0, $t1
mflo $s0
mfhi $s1
mult $t0, $t0              # 0x4000000000000000
mfhi $s3
mflo $s2
li $t2, -7
li $t3, 2
div $t2, $t3               # q=-3 r=-1 (remainder has the sign of the dividend)
mflo $s4
mfhi $s5
divu $t2, $t3              # 0xfffffff9 / 2 = 0x7ffffffc r 1
mflo $s6
mfhi $s7
multu $t2, $t2
mfhi $t4
mflo $t5
mult $t2, $t3
mfhi $t6
mflo $t7
mthi $t0
mtlo $t1
mfhi $t8
mflo $t9
li $v0, 10
syscall
