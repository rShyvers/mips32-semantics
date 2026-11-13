# Serviced syscalls in branch delay slots (jr / beq / jal / branch-likely): the service completes and the
# branch is then taken or not. On QEMU the harness handler decodes the branch at EPC (Cause.BD = 1).
la $t0, a
li $v0, 11
li $a0, 65
jr $t0
syscall                    # delay slot: prints 'A', then the jump takes effect
li $s7, 99                 # skipped
a: li $a0, 66
beq $zero, $zero, b
syscall                    # prints 'B'
li $s7, 98                 # skipped
b: li $a0, 67
bne $zero, $zero, c        # not taken
syscall                    # prints 'C'
c: li $a0, 68
jal d
syscall                    # prints 'D'; ra = address after this slot
move $s0, $ra
b e
nop
d: jr $ra
nop
e: li $a0, 69
bltz $zero, f              # not taken
syscall
f: li $a0, 70
bgezl $zero, g             # taken branch-likely: slot executes
syscall                    # prints 'F'
g: nop
li $v0, 10
syscall
