.text
main:
    li $s0, 0
    li $t0, -5
    li $t1, 5
    bltz $t0, a1
    nop
    addiu $s0, $s0, 1000
a1: bltz $t1, a2
    nop
    addiu $s0, $s0, 1
a2: bltz $zero, a3
    nop
    addiu $s0, $s0, 2
a3: bgez $t1, a4
    nop
    addiu $s0, $s0, 1000
a4: bgez $zero, a5
    nop
    addiu $s0, $s0, 1000
a5: bgez $t0, a6
    nop
    addiu $s0, $s0, 4
a6: bltzal $t0, sub
    nop
    bltzal $t1, sub
    nop
    bgezal $t1, sub
    nop
    bgezal $t0, sub
    nop
    bgezal $zero, sub
    nop
    move $a0, $s0
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    li $v0, 10
    syscall
sub:
    addiu $s0, $s0, 16
    jr $ra
    nop
