# DVP and EVP are no-ops without multi-threading: in Kernel Mode they leave GPR[rt] (and everything else) unchanged and raise
# nothing; in User Mode they raise Coprocessor Unusable with Cause.CE = 0.
# MD00086 Vol II-A Rev 6.06 DVP p.172 ("For implementations that do not support multi-threading (Config5VP=0), this instruction
# must be treated as a NOP instruction"; Restrictions: "If access to Coprocessor 0 is not enabled, a Coprocessor Unusable Exception
# is signaled"), EVP p.181 (same two sentences); MD00090 Vol III Rev 6.02 Table 9.69 p.263 (Config5.VP = 0: "No multi-threading
# support"); Table 9.52 p.209 (CE), Table 9.53 p.212 (ExcCode 11 = CpU).
# The handler counts entries (s4), keeps Cause & 0x3000007c (s5, CE and ExcCode) and skips the instruction.
# oracle: expect gpr:t0=0x1234 gpr:t1=0x5678 gpr:s4=2 gpr:s5=0x2c gpr:s6=0x1234
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
li $t0, 0x1234
li $t1, 0x5678
# Kernel Mode: no operation, rt not written
dvp $t0
evp $t1
dvp
evp
move $s6, $t0
# User Mode (Status = CU1|UM|EXL, eret): each raises Coprocessor Unusable, CE = 0
la $t2, user
mtc0 $t2, $14
lui $t3, 0x2000
ori $t3, $t3, 0x12
mtc0 $t3, $12
eret
user:
dvp $t0
evp $t1
li $t2, 0
li $t3, 0
