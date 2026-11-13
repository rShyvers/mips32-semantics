.data
cell: .word 41
.text
    la $t0, cell
    ll $t1, 0($t0)
    addiu $t1, $t1, 1
    sc $t1, 0($t0)
    lw $t2, 0($t0)
    move $a0, $t1
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $t2
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    li $v0, 10
    syscall
