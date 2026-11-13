# Branch-likely, TAKEN: behaves like the normal branch, the delay slot executes; link regs for *al.
# MD00086 Vol II-A Rev 6.06: BEQL p.73-74, BNEL p.104-106, BLEZL p.95-96, BGTZL p.89-91, BLTZL p.101-102,
# BGEZL p.86-87, BLTZALL p.99-100, BGEZALL p.80-81. Slot does addiu $s0,$s0,1 => 8 expected.
# oracle: expect gpr:s0=8
li $s0, 0
li $t0, 5
li $t1, -5
beql $t0, $t0, l1
addiu $s0, $s0, 1
li $s7, 99
l1: bnel $t0, $t1, l2
addiu $s0, $s0, 1
li $s7, 99
l2: blezl $t1, l3
addiu $s0, $s0, 1
li $s7, 99
l3: bgtzl $t0, l4
addiu $s0, $s0, 1
li $s7, 99
l4: bltzl $t1, l5
addiu $s0, $s0, 1
li $s7, 99
l5: bgezl $t0, l6
addiu $s0, $s0, 1
li $s7, 99
l6: bltzall $t1, l7
addiu $s0, $s0, 1
li $s7, 99
l7: move $s1, $ra
bgezall $t0, l8
addiu $s0, $s0, 1
li $s7, 99
l8: move $s2, $ra
li $v0, 10
syscall
