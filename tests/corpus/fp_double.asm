.data
buf: .word 0, 0, 0, 0
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
    mfc1 $s0, $f6
    mfc1 $s1, $f7
    mfc1 $s2, $f8
    mfc1 $s3, $f9
    mfc1 $s4, $f12
    mfc1 $s5, $f13
    mfc1 $s6, $f16
    mfc1 $s7, $f17
    mfc1 $t0, $f18
    mfc1 $t1, $f19
    mfc1 $t2, $f20
    mfc1 $t3, $f21
    mfc1 $t4, $f22
    mfc1 $t5, $f23
    mfc1 $t6, $f24
    mfc1 $t7, $f26
    mfc1 $t8, $f27
    mfc1 $a1, $f28
    mfc1 $a2, $f14
    mfc1 $a3, $f15
    li $v1, 0
    c.eq.d $f12, $f14
    bc1f n1
    nop
    addiu $v1, $v1, 1
n1: c.lt.d $f12, $f16
    bc1f n2
    nop
    addiu $v1, $v1, 2
n2: c.le.d $f16, $f12
    bc1t n3
    nop
    addiu $v1, $v1, 4
n3: c.le.d $f12, $f12
    bc1f n4
    nop
    addiu $v1, $v1, 8
n4:
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
