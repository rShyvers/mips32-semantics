# Overflow in the delay slot of a TAKEN branch-likely: EPC = the branch, Cause.BD = 1.
# MD00086 Vol II-A Rev 6.06: BEQL p.73-74, ADD p.33; MD00090 Vol III Rev 6.02 sec 9.36 Cause.BD.
# The beql is at 0x00400010 (li of a 32-bit constant is lui+ori).
# oracle: expect cause=0x80000030 epc=0x00400010
li $t0, 0x7fffffff
li $t1, 1
nop
beql $zero, $zero, tgt
add $t2, $t0, $t1
nop
tgt: nop
