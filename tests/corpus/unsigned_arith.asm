.text
    li $t0, 0x7fffffff
    li $t1, 1
    addu $s0, $t0, $t1
    subu $s1, $zero, $t1
    addiu $s2, $t0, 1
    addiu $s3, $zero, -32768
    slti $s4, $t1, -1
    slti $s5, $s1, 0
    sltiu $s6, $t1, -1
    sltiu $s7, $s1, 1
    lui $a3, 0x8000
    xori $v1, $s1, 0xffff
    move $a0, $s0
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $s1
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
    move $a0, $s5
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $s6
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $s7
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
    move $a0, $t3
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
    move $a0, $t7
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $t8
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $t9
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $a1
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $a2
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $a3
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    move $a0, $v1
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
    li $v0, 10
    syscall
