.text
    li $t0, 1
    tlt $zero, $t0
    li $a0, 88
    li $v0, 11
    syscall
    li $v0, 10
    syscall
