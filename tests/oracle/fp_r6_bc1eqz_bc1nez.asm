# BC1EQZ/BC1NEZ (MD00086 Vol II-A Rev 6.06 p.54-55): branch with a delay slot on bit 0 of FPR[ft] (only bit 0 is tested; the other bits and
# the upper half are ignored), taken and not taken; the delay-slot instruction always executes; the target is PC+4+sign_extend(offset<<2).
.data
res: .space 52
.text
la $s7, res
li $s0, 0
li $s1, 0
li $t9, 0xfffffffe
mtc1 $t9, $f3
li $t9, 0x00000000
mthc1 $t9, $f3
li $t2, 0
li $t3, 0
bc1eqz $f3, T0
addiu $t2, $t2, 1
addiu $t3, $t3, 1
T0: sw $t2, 0($s7)
sw $t3, 4($s7)
li $t9, 0x00000001
mtc1 $t9, $f3
li $t9, 0x00000000
mthc1 $t9, $f3
li $t2, 0
li $t3, 0
bc1eqz $f3, T1
addiu $t2, $t2, 1
addiu $t3, $t3, 1
T1: sw $t2, 8($s7)
sw $t3, 12($s7)
li $t9, 0x00000001
mtc1 $t9, $f3
li $t9, 0x00000000
mthc1 $t9, $f3
li $t2, 0
li $t3, 0
bc1nez $f3, T2
addiu $t2, $t2, 1
addiu $t3, $t3, 1
T2: sw $t2, 16($s7)
sw $t3, 20($s7)
li $t9, 0xfffffffe
mtc1 $t9, $f3
li $t9, 0x00000000
mthc1 $t9, $f3
li $t2, 0
li $t3, 0
bc1nez $f3, T3
addiu $t2, $t2, 1
addiu $t3, $t3, 1
T3: sw $t2, 24($s7)
sw $t3, 28($s7)
li $t9, 0x00000000
mtc1 $t9, $f3
li $t9, 0xffffffff
mthc1 $t9, $f3
li $t2, 0
li $t3, 0
bc1eqz $f3, T4
addiu $t2, $t2, 1
addiu $t3, $t3, 1
T4: sw $t2, 32($s7)
sw $t3, 36($s7)
li $t9, 0x80000001
mtc1 $t9, $f3
li $t9, 0x00000000
mthc1 $t9, $f3
li $t2, 0
li $t3, 0
bc1nez $f3, T5
addiu $t2, $t2, 1
addiu $t3, $t3, 1
T5: sw $t2, 40($s7)
sw $t3, 44($s7)
li $t4, 0
li $t9, 0
mtc1 $t9, $f5
L0: addiu $t4, $t4, 1
sltiu $t5, $t4, 3
mtc1 $t5, $f5
bc1nez $f5, L0
nop
sw $t4, 48($s7)
li $v0, 10
syscall
