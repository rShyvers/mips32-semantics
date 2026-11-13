# FP condition codes other than 0, movf/movt (GPR and FP), movn.s/movz.s,
# trunc/round/ceil/floor.w.s on values where MARS and the architecture agree,
# and sb/lbu. Branch delay slots are nop-padded so the program means the same
# with and without delay slots.
.data
buf: .word 0, 0
.text
    li $t0, 1
    mtc1 $t0, $f0
    cvt.s.w $f0, $f0          # 1.0
    li $t0, 2
    mtc1 $t0, $f2
    cvt.s.w $f2, $f2          # 2.0
    c.lt.s 1, $f0, $f2        # FCC1 := true
    c.eq.s 2, $f0, $f2        # FCC2 := false
    c.le.s $f2, $f0           # FCC0 := false
    li $s0, 10
    li $s1, 20
    li $s2, 30
    movt $s2, $s0, 1          # taken
    movf $s2, $s1, 1          # not taken
    li $s3, 40
    movf $s3, $s1, 2          # taken
    movt $s3, $s0, 0          # not taken
    li $s4, 0
    bc1t 1, L1
    nop
    li $s4, 100
L1: bc1f 2, L2
    nop
    addi $s4, $s4, 200
L2: addi $s4, $s4, 1
    mov.s $f4, $f0
    movt.s $f4, $f2, 1        # 2.0
    mov.s $f6, $f0
    movf.s $f6, $f2, 1        # stays 1.0
    mov.s $f8, $f0
    movn.s $f8, $f2, $s0      # $s0 != 0: 2.0
    mov.s $f10, $f0
    movz.s $f10, $f2, $s0     # stays 1.0
    li $t0, 7
    mtc1 $t0, $f12
    cvt.s.w $f12, $f12
    div.s $f12, $f12, $f2     # 3.5
    trunc.w.s $f14, $f12      # 3
    ceil.w.s $f16, $f12       # 4
    floor.w.s $f18, $f12      # 3
    round.w.s $f20, $f12      # 4 (ties to even)
    la $t9, buf
    li $t1, 0x1ab
    sb $t1, 1($t9)
    lbu $s5, 1($t9)
    lb $s6, 1($t9)
    mfc1 $t2, $f4
    mfc1 $t3, $f6
    mfc1 $t4, $f8
    mfc1 $t5, $f10
    mfc1 $t6, $f14
    mfc1 $t7, $f16
    mfc1 $t8, $f18
    mfc1 $v1, $f20
    li $v0, 10
    syscall
