# break/syscall/teq/tne/tge/tlt with non-zero code fields: the exception is taken as usual; the handler logs Cause and the faulting instruction word
# (loaded from EPC, so the encoded code field is observed) and skips it.
# MD00086 Vol II-A Rev 6.06: BREAK p.109 (code 20 bits), SYSCALL p.415, TEQ p.416 (code 10 bits).
.data
res: .space 64
.ktext
mfc0 $k0, $13
sw $k0, 0($s7)
mfc0 $k0, $14
lw $k1, 0($k0)
sw $k1, 4($s7)
addiu $s7, $s7, 8
addiu $k0, $k0, 4
mtc0 $k0, $14
eret
.text
la $s7, res
break 5
break 1023, 1023
break 5, 7
li $v0, 0
syscall 0x1234
syscall 0xfffff
li $t0, 3
teq $t0, $t0, 7
tge $t0, $t0, 1023
tne $t0, $zero, 11
tlt $zero, $t0, 5
tgeu $t0, $t0, 3
tltu $zero, $t0, 4
teq $t0, $zero, 9
sync 4
li $s0, 1
