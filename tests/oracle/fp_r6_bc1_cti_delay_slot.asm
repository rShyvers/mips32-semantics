# A CTI in the delay slot of BC1EQZ/BC1NEZ, and BC1EQZ/BC1NEZ in the delay slot of BEQ: "If a control transfer instruction (CTI) is
# executed in the delay slot of a branch or jump, Release 6 implementations are required to signal a Reserved Instruction exception"
# (MD00086 Vol II-A Rev 6.06 BC1EQZ BC1NEZ p.54; MD00082 Vol I-A Rev 6.01 sec 5.3.2.1 p.62): ExcCode 10 with Cause.BD set and EPC = the branch.
# The handler records Cause and EPC of each exception and resumes after the pair.
# oracle: expect gpr:s7=3
.ktext
    mfc0  $k0, $13
    mfc0  $k1, $14
    addiu $s7, $s7, 1
    sll   $s4, $s4, 8
    srl   $t7, $k0, 2
    andi  $t7, $t7, 31
    or    $s4, $s4, $t7
    srl   $t7, $k0, 31
    sll   $s5, $s5, 1
    or    $s5, $s5, $t7
    subu  $t7, $k1, $s3
    sll   $s6, $s6, 4
    or    $s6, $s6, $t7
    addiu $k1, $k1, 12
    mtc0  $k1, $14
    eret
.text
li $s7, 0
li $t9, 0
mtc1 $t9, $f3
li $s4, 0
li $s5, 0
li $s6, 0
la $s3, B0
B0: bc1eqz $f3, X0
beq $zero, $zero, X0
nop
X0: nop
B1: bc1nez $f3, X1
bc1eqz $f3, X1
nop
X1: nop
B2: beq $zero, $zero, X2
bc1nez $f3, X2
nop
X2: nop
li $t0, 1
nop
