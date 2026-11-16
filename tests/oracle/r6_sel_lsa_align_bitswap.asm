# Release 6 SELEQZ/SELNEZ, LSA, ALIGN, BITSWAP.
# MD00086 Vol II-A Rev 6.06: SELEQZ SELNEZ p.369 ("SELEQZ: cond <- GPR[rt] = 0 ... if cond then tmp <- GPR[rs] else tmp <- 0"); LSA p.232
# ("GPR[rd] <- sign_extend.32( GPR[rs] << (sa+1) + GPR[rt] )", the assembler operand is sa+1 = 1..4); ALIGN p.39 (an image page:
# "GPR[rd] <- (GPR[rt] << (8*bp)) or (GPR[rs] >> (GPRLEN-8*bp))"); BITSWAP p.92 (the bits of each byte reversed).
# oracle: expect gpr:s0=0x12345678 gpr:s1=0 gpr:s2=0 gpr:s3=0x12345678 gpr:s4=0x8040c001 gpr:s5=0x91a2b3c5 gpr:s6=0x567889ab
.data
res: .space 96
.text
la $s7, res
li $t0, 0x12345678
li $t1, 5
seleqz $s0, $t0, $zero      # rt = 0: rs
seleqz $s1, $t0, $t1        # 0
selnez $s2, $t0, $zero      # 0
selnez $s3, $t0, $t1        # rs
li $t2, 0x01020380
bitswap $s4, $t2            # 0x8040c001
lsa $s5, $t0, $t1, 3        # (0x12345678 << 3) + 5 = 0x91a2b3c5
li $t3, 0x89abcdef
align $s6, $t3, $t0, 2      # (0x12345678 << 16) | (0x89abcdef >> 16) = 0x567889ab
lsa $t4, $t0, $t1, 1
sw $t4, 0($s7)
lsa $t4, $t0, $t1, 2
sw $t4, 4($s7)
lsa $t4, $t0, $t1, 4
sw $t4, 8($s7)
li $t5, -1
lsa $t4, $t5, $t5, 4        # wraps
sw $t4, 12($s7)
align $t4, $t3, $t0, 0      # GPR[rt]
sw $t4, 16($s7)
align $t4, $t3, $t0, 1
sw $t4, 20($s7)
align $t4, $t3, $t0, 3
sw $t4, 24($s7)
bitswap $t4, $t3
sw $t4, 28($s7)
bitswap $t4, $t5
sw $t4, 32($s7)
seleqz $t4, $t0, $t0
sw $t4, 36($s7)
selnez $t4, $t0, $t0
sw $t4, 40($s7)
li $v0, 10
syscall
