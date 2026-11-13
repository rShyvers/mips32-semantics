# RDHWR in User Mode (Status.UM = 1, EXL = ERL = 0, CU0 = 0): only the hardware registers whose HWREna bit is set are readable; the others
# raise Reserved Instruction (not Coprocessor Unusable: RDHWR is not a coprocessor-0 instruction). HWREna = 0b0101 enables CPUNum (0) and CC (2).
# MD00086 Vol II-A Rev 6.06 RDHWR p.333 (Restrictions: "Access to the specified hardware register is enabled if Coprocessor 0 is enabled, or if the
# corresponding bit is set in the HWREna register. If access is not allowed or the register is not implemented, a Reserved Instruction Exception is
# signaled"), p.334 ("Exceptions: Reserved Instruction"); MD00090 Vol III Rev 6.02 sec 9.23 p.175 (HWREna), sec 3.4 p.22 (User Mode), sec 3.5.3
# p.23 (Coprocessor 0 enabled only in Kernel Mode or with CU0 = 1).
# Kernel code freezes Count at 777 (Cause.DC = 1), sets HWREna, EPC = user, Status = CU1|UM|EXL and executes eret. The handler counts exceptions in
# s6, keeps the last ExcCode in s7, and skips the instruction.
# oracle: expect gpr:s0=0 gpr:s1=0x1111 gpr:s2=777 gpr:s3=0x3333 gpr:s5=0x5555 gpr:s6=3 gpr:s7=10
.ktext
mfc0 $k0, $13
srl $s7, $k0, 2
andi $s7, $s7, 0x1f
addiu $s6, $s6, 1
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
eret
.text
li $s6, 0
li $s7, 0
li $s0, 0x9999
li $s1, 0x1111
li $s3, 0x3333
li $s5, 0x5555
lui $t0, 0x0800
mtc0 $t0, $13
li $t1, 777
mtc0 $t1, $9
li $t0, 5
mtc0 $t0, $7
la $t0, user
mtc0 $t0, $14
lui $t1, 0x2000
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
rdhwr $s5, $29
