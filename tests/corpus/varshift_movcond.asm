.text
    li $t0, 0x80000010
    li $t1, 4
    li $t2, 36
    sllv $t3, $t0, $t1
    srlv $t4, $t0, $t1
    srav $t5, $t0, $t1
    sllv $t6, $t0, $t2
    li $s0, 7
    li $s1, 9
    movn $s0, $s1, $t1
    li $s2, 7
    movn $s2, $s1, $zero
    li $s3, 7
    movz $s3, $s1, $zero
    li $s4, 7
    movz $s4, $s1, $t1
    move $a0, $t3
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $t4
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $t5
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $t6
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $s0
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $s2
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $s3
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $s4
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    li $v0, 10
    syscall
