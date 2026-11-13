# Integer ALU: add/addu/sub/subu/and/or/xor/nor/slt/sltu/slti/sltiu/andi/ori/xori/lui, shifts incl. variable ones
# (shift amount taken mod 32). MD00086 Vol II-A Rev 6.06: ADDU p.37, SUBU p.390, SLT p.378, SLTU p.381, SLL p.376,
# SRA p.383, SRAV p.384, SRL p.385, SLTI/SLTIU (sign-extended immediate, compared signed/unsigned).
# oracle: expect gpr:s0=0xffffffff gpr:s1=0x00000001 gpr:s2=0x00000000 gpr:s3=0x00000001
li $t0, 0x80000000
li $t1, 1
li $t2, 0xfedcba98
addu $s0, $t0, $zero
subu $s0, $zero, $t1       # -1
slt $s1, $t0, $t1          # INT_MIN < 1 signed => 1
sltu $s2, $t0, $t1         # 0x80000000 < 1 unsigned => 0
slti $s3, $t0, -1          # INT_MIN < -1 => 1
sltiu $s4, $t1, -1         # 1 < 0xffffffff unsigned => 1
sltiu $s5, $t0, 0          # => 0
and $s6, $t2, $t0
or $s7, $t2, $t1
xor $t3, $t2, $t2
nor $t4, $t2, $zero
andi $t5, $t2, 0xffff
ori $t6, $zero, 0x8000
xori $t7, $t2, 0xffff
lui $t8, 0x8001
sll $t9, $t2, 4
srl $a0, $t2, 4
sra $a1, $t2, 4
li $a2, 33
sllv $a3, $t2, $a2         # shift by 33 mod 32 = 1
srlv $v1, $t2, $a2
srav $v0, $t2, $a2
sll $gp, $t2, 31
sra $fp, $t0, 31
add $t1, $t0, $zero
sub $t3, $t2, $t1
li $v0, 10
syscall
