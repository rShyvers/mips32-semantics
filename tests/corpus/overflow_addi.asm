.text
    li $t0, 0x7fffffff
    li $a0, 65
    li $v0, 11
    syscall
    addi $t1, $t0, 1
    li $a0, 66
    li $v0, 11
    syscall
    li $v0, 10
    syscall
