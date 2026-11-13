# smoke: arithmetic, memory, print-int syscall, exit
.data
w: .word 0x12345678, 7
.text
la $t0,w
lw $t1,0($t0)
sw $t1,8($t0)
li $v0,1
move $a0,$t1
syscall
li $v0,11
li $a0,'x'
syscall
li $v0,10
syscall
