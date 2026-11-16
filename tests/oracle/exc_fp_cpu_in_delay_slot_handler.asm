# An FP exception (enabled Divide-by-zero, ExcCode 15) and Coprocessor Unusable (CU1 = 0, ExcCode 11, CE 1) raised by an instruction in a branch delay slot:
# Cause.BD = 1 and EPC = the address of the branch. The handler logs Cause/EPC/FCSR and resumes after the delay slot (EPC + 8).
# MD00090 Vol III Rev 6.02 sec 6.2 Table 6.11 p.87 (value stored in EPC for an exception in a branch delay slot = the branch address, Cause.BD = 1); MD00082 Vol I-A Rev 6.01 6.7.1; MD00090 6.2.22.
# oracle: expect gpr:s4=2
.data
res: .space 64
.ktext
mfc0 $k0, $13
sw $k0, 0($s7)
mfc0 $k1, $14
sw $k1, 4($s7)
mfc0 $k0, $12
lui $t9, 0x2000
or $k0, $k0, $t9
mtc0 $k0, $12
cfc1 $k0, $31
lui $t9, 0xfff3
ori $t9, $t9, 0xffff
and $k0, $k0, $t9
sw $k0, 8($s7)
addiu $s7, $s7, 12
addiu $s4, $s4, 1
li $k0, 0xfff30fff
cfc1 $t9, $31
and $k0, $k0, $t9
and $t9, $t9, $k0
ctc1 $k0, $31
addiu $k1, $k1, 8
mtc0 $k1, $14
eret
.text
la $s7, res
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $s4, 0
li $t8, 0x400
ctc1 $t8, $31
beq $zero, $zero, A
div.s $f6, $f2, $f4
nop
A: nop
mtc0 $zero, $12
beq $zero, $zero, B
add.s $f6, $f2, $f4
nop
B: nop
