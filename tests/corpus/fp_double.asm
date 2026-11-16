.data
buf: .word 0, 0, 0, 0
out: .space 64
.text
    li $t0, 7
    mtc1 $t0, $f0
    cvt.d.w $f2, $f0
    li $t0, -2
    mtc1 $t0, $f4
    cvt.d.w $f4, $f4
    add.d $f6, $f2, $f4
    sub.d $f8, $f2, $f4
    mul.d $f10, $f2, $f4
    div.d $f12, $f2, $f4
    mov.d $f14, $f12
    neg.d $f16, $f12
    abs.d $f18, $f12
    li $t0, 16
    mtc1 $t0, $f20
    cvt.d.w $f20, $f20
    sqrt.d $f20, $f20
    la $t9, buf
    sdc1 $f12, 8($t9)
    ldc1 $f22, 8($t9)
    cvt.s.d $f24, $f12
    cvt.d.s $f26, $f24
    cvt.w.d $f28, $f10
    # each double is read through memory (sdc1, then lw of its low and high word), so the program
    # behaves the same with a 32-bit FPU (FR = 0, MARS) and the 64-bit FPU of Release 6 (FR = 1)
    la $v1, out
    sdc1 $f6, 0($v1)
    lw $s0, 0($v1)
    lw $s1, 4($v1)
    sdc1 $f8, 8($v1)
    lw $s2, 8($v1)
    lw $s3, 12($v1)
    sdc1 $f12, 16($v1)
    lw $s4, 16($v1)
    lw $s5, 20($v1)
    sdc1 $f16, 24($v1)
    lw $s6, 24($v1)
    lw $s7, 28($v1)
    sdc1 $f18, 32($v1)
    lw $t0, 32($v1)
    lw $t1, 36($v1)
    sdc1 $f20, 40($v1)
    lw $t2, 40($v1)
    lw $t3, 44($v1)
    sdc1 $f22, 48($v1)
    lw $t4, 48($v1)
    lw $t5, 52($v1)
    sdc1 $f26, 56($v1)
    lw $t7, 56($v1)
    lw $t8, 60($v1)
    sdc1 $f14, 64($v1)
    lw $a2, 64($v1)
    lw $a3, 68($v1)
    mfc1 $t6, $f24
    mfc1 $a1, $f28
    li $v1, 0
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
    move $a0, $t0
    li $v0, 1
    syscall
    li $a0, 32
    li $v0, 11
    syscall
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
