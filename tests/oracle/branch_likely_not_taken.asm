# Branch-likely, NOT taken: the delay-slot instruction is nullified (not executed).
# MD00086 Vol II-A Rev 6.06: BEQL p.73-74 ("if the branch is not taken, the delay slot is nullified"), BNEL p.104-106,
# BLEZL p.95-96, BGTZL p.89-91, BLTZL p.101-102, BGEZL p.86-87, BLTZALL p.99-100, BGEZALL p.80-81.
# Slots would add 1 to $s0; none executes => $s0 stays 0. $s1/$s2 record the link register of the *al forms.
# oracle: expect gpr:s0=0
li $s0, 0
li $t0, 5
li $t1, -5
beql $t0, $t1, n1
addiu $s0, $s0, 1
n1: bnel $t0, $t0, n2
addiu $s0, $s0, 1
n2: blezl $t0, n3
addiu $s0, $s0, 1
n3: bgtzl $t1, n4
addiu $s0, $s0, 1
n4: bltzl $t0, n5
addiu $s0, $s0, 1
n5: bgezl $t1, n6
addiu $s0, $s0, 1
n6: li $ra, 0
bltzall $t0, n7
addiu $s0, $s0, 1
n7: move $s1, $ra
li $ra, 0
bgezall $t1, n8
addiu $s0, $s0, 1
n8: move $s2, $ra
li $v0, 10
syscall
