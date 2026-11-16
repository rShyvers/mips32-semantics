# Release 6 compact branches: no delay slot. Taken, the next instruction is NOT executed; not taken, it
# is (the forbidden slot holds an ordinary instruction here). MD00086 Vol II-A Rev 6.06: B<cond>C p.82-85
# ("Compact branches have no delay slot: the instruction after the branch is NOT executed if the branch
# is taken"), BOVC/BNVC p.107, BC p.53. Each branch is followed by `addiu $s0,$s0,1` (counts the
# not-taken ones) and, when taken, skips an `ori` into $s1 (bit set = wrongly executed); $s2 collects a
# bit per not-taken branch whose slot ran. (`bovc $zero, $zero` is in bovc_zero_zero.asm.)
# oracle: expect gpr:s0=13 gpr:s1=0 gpr:s2=0x1fff
li $s0, 0
li $s1, 0
li $s2, 0
li $t0, 5
li $t1, -5
li $t2, 7
li $t3, 0x7fffffff
li $t4, 1
# beqc / bnec
beqc $t0, $t2, n1          # 5 != 7: not taken
addiu $s0, $s0, 1
ori $s2, $s2, 0x1
n1: bnec $t0, $t2, t1x     # taken
ori $s1, $s1, 0x1
t1x: beqc $t2, $t0, n2     # operands either order: not taken
addiu $s0, $s0, 1
ori $s2, $s2, 0x2
n2: bltc $t1, $t0, t2x     # -5 < 5 signed: taken
ori $s1, $s1, 0x2
t2x: bltuc $t1, $t0, n3    # 0xfffffffb < 5 unsigned: no
addiu $s0, $s0, 1
ori $s2, $s2, 0x4
n3: bgec $t0, $t1, t3x     # 5 >= -5: taken
ori $s1, $s1, 0x4
t3x: bgeuc $t0, $t1, n4    # 5 >= 0xfffffffb unsigned: no
addiu $s0, $s0, 1
ori $s2, $s2, 0x8
# compare with zero
n4: blezc $t1, t4x          # taken
ori $s1, $s1, 0x8
t4x: blezc $t0, n5          # not taken
addiu $s0, $s0, 1
ori $s2, $s2, 0x10
n5: bgezc $t0, t5x          # taken
ori $s1, $s1, 0x10
t5x: bgezc $t1, n6          # not taken
addiu $s0, $s0, 1
ori $s2, $s2, 0x20
n6: bgtzc $t0, t6x          # taken
ori $s1, $s1, 0x20
t6x: bgtzc $t1, n7          # not taken
addiu $s0, $s0, 1
ori $s2, $s2, 0x40
n7: bltzc $t1, t7x          # taken
ori $s1, $s1, 0x40
t7x: bltzc $t0, n8          # not taken
addiu $s0, $s0, 1
ori $s2, $s2, 0x80
n8: li $t5, 0
beqzc $t5, t8x              # taken (21-bit offset form)
ori $s1, $s1, 0x80
t8x: bnezc $t5, n9          # not taken
addiu $s0, $s0, 1
ori $s2, $s2, 0x100
n9: bnezc $t0, t9x          # taken
ori $s1, $s1, 0x100
# overflow branches: 0x7fffffff + 1 overflows; 5 + 7 does not
t9x: bovc $t3, $t4, t10x    # taken
ori $s1, $s1, 0x200
t10x: bovc $t0, $t2, n10    # not taken
addiu $s0, $s0, 1
ori $s2, $s2, 0x200
n10: bnvc $t0, $t2, t11x    # taken
ori $s1, $s1, 0x400
t11x: bnvc $t3, $t4, n11    # not taken
addiu $s0, $s0, 1
ori $s2, $s2, 0x400
n11: bovc $t5, $zero, n12   # 0 + 0: no overflow, not taken
addiu $s0, $s0, 1
ori $s2, $s2, 0x800
n12: bnvc $t0, $zero, t12x  # BNVC rs, r0 always branches (p.107)
ori $s1, $s1, 0x800
t12x: bc t13x               # unconditional
ori $s1, $s1, 0x1000
t13x: bovc $t3, $zero, n13  # 0x7fffffff + 0: no overflow, not taken
addiu $s0, $s0, 1
ori $s2, $s2, 0x1000
n13: li $v0, 10
syscall
