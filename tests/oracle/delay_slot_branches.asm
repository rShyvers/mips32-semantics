# Branch delay slots: the slot always executes (taken and not taken); conditional branch conditions.
# MD00086 Vol II-A Rev 6.06: BEQ p.72, BNE p.103, BLEZ p.94, BGTZ p.88, BLTZ p.97, BGEZ p.75.
# Each slot does addiu $s0,$s0,1 so s0 counts slot executions (8 branches => 8).
# oracle: expect gpr:s0=8 gpr:s1=0x15
li $s0, 0
li $s1, 0
li $t0, 5
li $t1, -5
beq $t0, $t0, a1
addiu $s0, $s0, 1
ori $s1, $s1, 0x80        # skipped
a1: beq $t0, $t1, a2      # not taken
addiu $s0, $s0, 1
ori $s1, $s1, 1
a2: bne $t0, $t1, a3
addiu $s0, $s0, 1
ori $s1, $s1, 0x80        # skipped
a3: blez $t1, a4
addiu $s0, $s0, 1
ori $s1, $s1, 0x80        # skipped
a4: bgtz $t1, a5          # not taken
addiu $s0, $s0, 1
ori $s1, $s1, 4
a5: bltz $t1, a6
addiu $s0, $s0, 1
ori $s1, $s1, 0x80        # skipped
a6: bgez $t1, a7          # not taken
addiu $s0, $s0, 1
ori $s1, $s1, 0x10
a7: bgez $zero, a8
addiu $s0, $s0, 1
ori $s1, $s1, 0x80        # skipped
a8: li $v0, 10
syscall
