.text
    li $t0, 0x7fffffff
    li $a0, 65
    li $v0, 11
    syscall
    li $t2, 1
    add $t1, $t0, $t2
    li $a0, 66
    li $v0, 11
    syscall
    li $v0, 10
    syscall
