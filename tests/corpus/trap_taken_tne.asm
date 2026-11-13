.text
    li $t0, 1
    tne $t0, $zero
    li $a0, 88
    li $v0, 11
    syscall
    li $v0, 10
    syscall
