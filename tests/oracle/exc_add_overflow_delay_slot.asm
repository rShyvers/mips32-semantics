# overflow in a branch delay slot: EPC = address of the BRANCH, Cause.BD = 1.
# MD00086 Vol II-A Rev 6.06: ADD p.33; MD00090 Vol III Rev 6.02 Cause register BD field (sec 9.36), EPC (sec 9.37).
# The branch is at 0x00400010 (li of a 32-bit constant is lui+ori) => EPC = 0x00400010, Cause = BD|ExcCode12.
# oracle: expect cause=0x80000030 epc=0x00400010
li $t0, 0x7fffffff
li $t1, 1
nop
beq $zero, $zero, tgt
add $t2, $t0, $t1
nop
tgt: nop
