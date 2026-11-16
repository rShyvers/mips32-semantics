# RDHWR in User Mode with Status bit 28 set and HWREna = 0. Release 6: bit 28 is RW, not CU0, so Coprocessor 0 is NOT enabled and every
# rdhwr raises Reserved Instruction (the file name is historical: before Release 6 bit 28 was CU0 and enabled every hardware register).
# MD00086 Vol II-A Rev 6.06 RDHWR p.333 ("Access to the specified hardware register is enabled if Coprocessor 0 is enabled, or if the corresponding
# bit is set in the HWREna register. If access is not allowed or the register is not implemented, a Reserved Instruction Exception is signaled");
# MD00090 Vol III Rev 6.02 sec 9.32 Figure 9.33 p.189 (Release 6 Status: bits 31..29 CU3..CU1, bit 28 RW) and Table 9.47 p.190 (an image page;
# read in the PDF: RW "can be written by software without side-effects"); Table 9.39 p.175 (HWREna); ExcCode 10 = RI, Table 9.53 p.212.
# The handler counts exceptions in s6 and keeps the last ExcCode in s7, then skips the instruction; the destinations s0..s3 keep 0.
# oracle: expect gpr:s0=0 gpr:s1=0 gpr:s2=0 gpr:s3=0 gpr:s6=4 gpr:s7=10
.ktext
addiu $s6, $s6, 1
mfc0 $k0, $13
srl $s7, $k0, 2
andi $s7, $s7, 0x1f
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
eret
.text
li $s6, 0
li $s7, 0
lui $t0, 0x0800
mtc0 $t0, $13
li $t1, 777
mtc0 $t1, $9
mtc0 $zero, $7
la $t0, user
mtc0 $t0, $14
lui $t1, 0x3000
ori $t1, $t1, 0x12
mtc0 $t1, $12
li $t0, 0
li $t1, 0
eret
user:
rdhwr $s0, $0
rdhwr $s1, $1
rdhwr $s2, $2
rdhwr $s3, $3
