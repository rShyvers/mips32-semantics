# CACHE in Kernel Mode is a no-op (the profile has no caches), in User Mode it raises Coprocessor Unusable with Cause.CE = 0.
# MD00086 Vol II-A Rev 6.06 CACHE p.114-119: Restrictions p.119 ("The operation of this instruction is UNDEFINED for any operation/cache combination
# that is not implemented. In Release 6, the instruction in this case should perform no operation"; "If access to Coprocessor 0 is not enabled, a
# Coprocessor Unusable Exception is signaled"; "This instruction does not produce an exception for a misaligned memory address"); DECISIONS D8.
# MD00090 Vol III Rev 6.02 Table 9.52 p.209 (CE: "Coprocessor unit number referenced when a Coprocessor Unusable exception is taken"),
# Table 9.53 p.212 (ExcCode 11 = CpU). Kernel Mode: ops on the data word, on a text address, a misaligned address and the next word; memory and
# registers unchanged, no exception. User Mode (Status = CU1|UM|EXL, eret): each cache raises CpU.
# The handler counts entries (s4), keeps Cause & 0x3000007c (s5, CE and ExcCode) and skips the instruction.
# oracle: expect gpr:s4=3 gpr:s5=0x2c gpr:s6=0x1234 mem:0x10010000=0x00001234
.data
w: .word 0x1234
.ktext
addiu $s4, $s4, 1
mfc0 $k0, $13
li $k1, 0x3000007c
and $s5, $k0, $k1
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
li $k1, 0
eret
.text
li $s4, 0
li $s5, 0
la $t0, w
la $t1, k0addr
cache 0x15, 0($t0)
cache 0x10, 0($t1)
cache 0x01, 3($t0)
cache 0x1c, 4($t0)
k0addr:
lw $s6, 0($t0)
# User Mode: Coprocessor Unusable for each cache
la $t2, user
mtc0 $t2, $14
lui $t3, 0x2000
ori $t3, $t3, 0x12
mtc0 $t3, $12
eret
user:
cache 0x15, 0($t0)
cache 0x10, 0($t1)
cache 0x01, 3($t0)
li $t2, 0
li $t3, 0
