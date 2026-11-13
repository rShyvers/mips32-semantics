.text
main:
    li $s0, 0
    jal f
    nop
    la $t0, g
    jalr $t0
    nop
    la $t0, g
    jalr $s7, $t0
    nop
    la $t0, done
    jr $t0
    nop
    li $s0, 999
done:
    move $a0, $s0
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    li $v0, 10
    syscall
f:
    addiu $s0, $s0, 1
    jr $ra
    nop
g:
    addiu $s0, $s0, 10
    bne $s7, $zero, g2
    nop
    jr $ra
    nop
g2:
    jr $s7
    nop
