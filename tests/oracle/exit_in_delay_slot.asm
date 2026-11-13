# exit (syscall 10) executed in a delay slot: the machine stops; pc/state as at the syscall.
# oracle: expect gpr:s0=1
li $s0, 1
li $v0, 10
beq $zero, $zero, never
syscall
li $s0, 2
never: li $s0, 3
