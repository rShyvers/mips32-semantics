.text
    li $t0, 1
    li $t1, 2
    teq $t0, $t1
    tne $t0, $t0
    tlt $t1, $t0
    tge $t0, $t1
    tltu $t1, $t0
    tgeu $t0, $t1
    teqi $t0, 2
    tnei $t0, 1
    tlti $t0, 1
    tgei $t0, 2
    tltiu $t0, 1
    tgeiu $t0, 2
    li $a0, 79
    li $v0, 11
    syscall
    li $v0, 10
    syscall
