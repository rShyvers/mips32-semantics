# Assembler idioms (b, beqz, bnez, blt/bge/bgt/ble, bltu/bgeu/bgtu/bleu, neg,
# negu, not, abs), character literals, octal/hex literals and label+const.
# Every branch is followed by an explicit nop: this model has real delay
# slots and the assembler never inserts one. MARS 4.5 (delayed branching
# off) prints the same output.
# Expected output: "ABCDEFGHIJ -7 7 -6 7 7 8 22"
        .data
tab:    .word 11, 22, 33
        .text
        li   $t0, -3
        li   $t1, 5
        blt  $t0, $t1, L1          # -3 < 5 signed: taken
        nop
        b    fail
        nop
L1:     li   $a0, 'A'
        li   $v0, 11
        syscall
        bge  $t0, $t1, fail        # not taken
        nop
        li   $a0, 'B'
        syscall
        bgt  $t1, $t0, L2          # 5 > -3: taken
        nop
        b    fail
        nop
L2:     li   $a0, 'C'
        syscall
        ble  $t1, $t0, fail        # not taken
        nop
        li   $a0, 'D'
        syscall
        bltu $t1, $t0, L3          # 5 <u 0xfffffffd: taken
        nop
        b    fail
        nop
L3:     li   $a0, 'E'
        syscall
        bgeu $t1, $t0, fail        # not taken
        nop
        li   $a0, 'F'
        syscall
        bgtu $t0, $t1, L4          # taken
        nop
        b    fail
        nop
L4:     li   $a0, 'G'
        syscall
        bleu $t0, $t1, fail        # not taken
        nop
        li   $a0, 'H'
        syscall
        beqz $zero, L5             # taken
        nop
        b    fail
        nop
L5:     li   $a0, 'I'
        syscall
        bnez $t1, L6               # taken
        nop
        b    fail
        nop
L6:     li   $a0, 'J'
        syscall
        li   $a0, ' '
        syscall
        li   $t2, 7
        neg  $a0, $t2              # -7
        li   $v0, 1
        syscall
        li   $a0, ' '
        li   $v0, 11
        syscall
        li   $t3, -7
        negu $a0, $t3              # 7
        li   $v0, 1
        syscall
        li   $a0, ' '
        li   $v0, 11
        syscall
        not  $a0, $t1              # ~5 = -6
        li   $v0, 1
        syscall
        li   $a0, ' '
        li   $v0, 11
        syscall
        abs  $a0, $t3              # |-7| = 7
        li   $v0, 1
        syscall
        li   $a0, ' '
        li   $v0, 11
        syscall
        abs  $t2, $t2              # |7| = 7, rd = rs form
        move $a0, $t2
        li   $v0, 1
        syscall
        li   $a0, ' '
        li   $v0, 11
        syscall
        li   $a0, 010              # octal: 8
        li   $v0, 1
        syscall
        li   $a0, ' '
        li   $v0, 11
        syscall
        la   $t4, tab+4            # label+const
        lw   $a0, 0($t4)           # 22
        li   $v0, 1
        syscall
        li   $v0, 10
        syscall
fail:   li   $a0, '!'
        li   $v0, 11
        syscall
        li   $v0, 10
        syscall
