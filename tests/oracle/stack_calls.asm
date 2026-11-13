# Stack discipline: push/pop with $sp (initial 0x7fffeffc), nested jal/jr, words land in the stack page.
# MD00086 Vol II-A Rev 6.06: JAL p.195, JR p.206-207, SW p.392, LW p.235.
# oracle: expect gpr:sp=0x7fffeffc gpr:s0=0x0000000d mem:0x7fffeff8=0x00000007 mem:0x7fffeff4=0x0000000d
li $s0, 0
li $a0, 3
jal f
nop
move $s1, $v0
li $t0, 7
addiu $sp, $sp, -4
sw $t0, 0($sp)
li $t1, 13
addiu $sp, $sp, -4
sw $t1, 0($sp)
lw $s0, 0($sp)
addiu $sp, $sp, 8
addiu $sp, $sp, -8
sw $t0, 4($sp)
sw $t1, 0($sp)
addiu $sp, $sp, 8
b end
nop
f: addiu $sp, $sp, -8
sw $ra, 4($sp)
sw $a0, 0($sp)
addiu $a0, $a0, 1
jal g
nop
lw $a0, 0($sp)
lw $ra, 4($sp)
addiu $sp, $sp, 8
addu $v0, $v0, $a0
jr $ra
nop
g: sll $v0, $a0, 1
jr $ra
nop
end: nop
li $v0, 10
syscall
