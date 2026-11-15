# j (Jump): forward and backward PC-region jumps; the delay-slot instruction executes before the jump completes, the skipped
# instructions do not. A backward j closes a 3-iteration loop. $t0 accumulates which instructions ran.
# MD00086 Vol II-A Rev 6.06 J p.194 ("The low 28 bits of the target address is the instr_index field shifted left 2 bits. The remaining
# upper bits are the corresponding bits of the address of the instruction in the delay slot"; "Execute the instruction that follows the
# jump, in the branch delay slot, before executing the jump itself").
# oracle: expect gpr:t0=4 gpr:t1=3 gpr:t2=2
    li $t0, 1
    j T1
    addiu $t0, $t0, 1
    addiu $t0, $t0, 100
T1: j T2
    addiu $t0, $t0, 2
T0: addiu $t0, $t0, 1000
T2: li $t1, 0
    li $t2, 0
LOOP: addiu $t1, $t1, 1
    slti $t3, $t1, 3
    beq $t3, $zero, DONE
    nop
    j LOOP
    addiu $t2, $t2, 1
    addiu $t2, $t2, 100
DONE: li $v0, 10
    syscall
