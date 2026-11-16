.data
buf: .word 0, 0
.text
    li $t0, 7
    mtc1 $t0, $f0
    cvt.s.w $f2, $f0
    li $t0, 2
    mtc1 $t0, $f4
    cvt.s.w $f4, $f4
    add.s $f6, $f2, $f4
    sub.s $f8, $f2, $f4
    mul.s $f10, $f2, $f4
    div.s $f12, $f2, $f4
    mov.s $f14, $f12
    neg.s $f16, $f12
    abs.s $f18, $f16
    li $t0, 16
    mtc1 $t0, $f20
    cvt.s.w $f20, $f20
    sqrt.s $f20, $f20
    la $t9, buf
    swc1 $f12, 0($t9)
    lwc1 $f22, 0($t9)
    lw $s7, 0($t9)
    mfc1 $s0, $f6
    mfc1 $s1, $f8
    mfc1 $s2, $f10
    mfc1 $s3, $f12
    mfc1 $s4, $f16
    mfc1 $s5, $f18
    mfc1 $s6, $f20
    mfc1 $t8, $f22
    mfc1 $t7, $f14
    cvt.w.s $f24, $f10
    mfc1 $t0, $f24
    trunc.w.s $f24, $f16
    mfc1 $t1, $f24
    floor.w.s $f24, $f16
    mfc1 $t2, $f24
    ceil.w.s $f24, $f16
    mfc1 $t3, $f24
    div.s $f26, $f2, $f20
    round.w.s $f24, $f26
    mfc1 $t4, $f24
    li $t5, 0
n5:
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
    move $a0, $t8
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
    li $v0, 10
    syscall
