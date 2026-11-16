# An exception in the delay slot of a conditional branch that is statically never taken (bne r,r / bne $zero,$zero / bgtz $zero /
# bltz $zero) is still an exception in a branch delay slot: Cause.BD = 1 and EPC = the branch address. The handler stores
# (Cause & (BD|ExcCode), EPC) per exception to res, counts in $s7, and resumes at EPC+8 if BD (past branch + slot) else EPC+4.
# The last two cases are controls (dynamically not-taken beq/blez): QEMU and the model agree there (BD = 1).
# QEMU (24Kf and mips32r6-generic, executed) translates a statically never-taken branch as a NOP, so it reports BD = 0 and EPC = the slot address.
# MD00090 Vol III Rev 6.02 sec 9.36 p.209 (Cause.BD: "Indicates whether the last exception taken occurred in a branch delay slot"),
# sec 9.38 p.217 (EPC: "the virtual address of the immediately preceding branch or jump instruction, when the exception causing
# instruction is in a branch delay slot, and the Branch Delay bit in the Cause register is set"); MD00082 Vol I-A Rev 6.01 sec 5.3.2 p.61
# ("Typical delayed branches execute the delay-slot instruction, whether or not the branch was taken"); MD00086 Vol II-A Rev 6.06
# BNE p.103, BGTZ p.88, BLTZ p.97 (the instruction following the branch is "in the branch delay slot").
# oracle: expect gpr:s7=6
# oracle: expect mem:0x10010000=0x80000024 mem:0x10010008=0x80000034 mem:0x10010010=0x80000010 mem:0x10010018=0x80000024
# oracle: expect mem:0x10010004=0x0040001c mem:0x1001000c=0x00400028 mem:0x10010014=0x00400034 mem:0x1001001c=0x00400040
# oracle: expect mem:0x10010020=0x80000024 mem:0x10010024=0x0040004c mem:0x10010028=0x80000034 mem:0x1001002c=0x00400058
# oracle: expect-deviation mem:0x10010000 MD00090 Vol III Rev 6.02 sec 9.36 p.209 / sec 9.38 p.217: exception (break) in the delay slot of the never-taken bne r,r: Cause.BD = 1 (model 0x80000024); QEMU BD = 0
# oracle: expect-deviation mem:0x10010004 MD00090 Vol III Rev 6.02 sec 9.38 p.217: EPC = the bne r,r branch address (model); QEMU EPC = the slot address
# oracle: expect-deviation mem:0x10010008 MD00090 Vol III Rev 6.02 sec 9.36 p.209 / sec 9.38 p.217: trap (teq) in the delay slot of the never-taken bgtz $zero: Cause.BD = 1 (model 0x80000034); QEMU BD = 0
# oracle: expect-deviation mem:0x1001000c MD00090 Vol III Rev 6.02 sec 9.38 p.217: EPC = the bgtz $zero branch address (model); QEMU EPC = the slot address
# oracle: expect-deviation mem:0x10010010 MD00090 Vol III Rev 6.02 sec 9.36 p.209 / sec 9.38 p.217: Address Error (misaligned ll, always an Address Error in Release 6: MD00082 Vol I-A Rev 6.01 App. B.2 p.128) in the delay slot of the never-taken bltz $zero: Cause.BD = 1 (model 0x80000010); QEMU BD = 0
# oracle: expect-deviation mem:0x10010014 MD00090 Vol III Rev 6.02 sec 9.38 p.217: EPC = the bltz $zero branch address (model); QEMU EPC = the slot address
# oracle: expect-deviation mem:0x10010018 MD00090 Vol III Rev 6.02 sec 9.36 p.209 / sec 9.38 p.217: exception (break) in the delay slot of the never-taken bne $zero,$zero: Cause.BD = 1 (model 0x80000024); QEMU BD = 0
# oracle: expect-deviation mem:0x1001001c MD00090 Vol III Rev 6.02 sec 9.38 p.217: EPC = the bne $zero,$zero branch address (model); QEMU EPC = the slot address
.data
res: .space 48
buf: .space 16
.ktext
mfc0 $k0, $13
lui $k1, 0x8000
ori $k1, $k1, 0x7c
and $k0, $k0, $k1
sw $k0, 0($s6)
mfc0 $k1, $14
sw $k1, 4($s6)
addiu $s6, $s6, 8
addiu $s7, $s7, 1
bltz $k0, bd
nop
addiu $k1, $k1, 4
b out
nop
bd: addiu $k1, $k1, 8
out: mtc0 $k1, $14
eret
.text
la $s6, res
la $s5, buf
li $s7, 0
li $t0, 5
li $t1, 7
bne $t0, $t0, L1
break
L1: addiu $s0, $s0, 1
bgtz $zero, L2
teq $zero, $zero
L2: addiu $s0, $s0, 1
bltz $zero, L3
ll $t0, 1($s5)
L3: addiu $s0, $s0, 1
bne $zero, $zero, L4
break
L4: addiu $s0, $s0, 1
beq $t0, $t1, L5
break
L5: addiu $s0, $s0, 1
blez $t0, L6
teq $zero, $zero
L6: addiu $s0, $s0, 1
