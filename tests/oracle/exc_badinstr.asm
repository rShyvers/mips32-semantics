# BadInstr (CP0 8 sel 1) holds the faulting instruction word of a synchronous exception; BadInstrP (CP0 8 sel 2) holds the branch word when the
# faulting instruction is in a delay slot. Cases: Reserved Instruction (a removed pre-Release 6 encoding, movz), Trap (teq), Trap in the delay
# slot of beq, Address Error on a load (lw of a kseg0 address in User Mode, AdEL), Coprocessor Unusable (mfc0 in User Mode).
# MD00090 Vol III Rev 6.02 sec 9.25 p.179 (BadInstr: "capture the most recent instruction which caused one of the following exceptions:
# Coprocessor Unusable, Reserved Instruction ... Trap ... Address Error"), sec 9.26 p.181 (BadInstrP: "contains the prior branch instruction, when
# the faulting instruction is in a branch delay slot"; "When a synchronous exception occurs and the faulting instruction is not in a branch delay
# slot, then the value stored in BadInstrP is UNPREDICTABLE": the handler reads BadInstrP only when Cause.BD = 1, else it logs 0), Table 9.52
# p.209 (BD; CE is UNPREDICTABLE except for CpU: masked out), Table 9.53 p.212-213 (ExcCode); MD00086 Vol II-A Rev 6.06 Table A.1 p.451 (removed
# encodings signal RI), TEQ p.416, MFC0 p.266.
# The handler logs (Cause & 0x8000007c, BadInstr, BadInstrP or 0) per exception at res, then resumes after the instruction (after the delay
# slot when BD = 1: the beq's target is the instruction after its slot).
# oracle: expect gpr:s4=5 mem:0x10010000=0x00000028 mem:0x10010004=0x0109500a mem:0x1001000c=0x00000034 mem:0x10010010=0x00000034 mem:0x10010018=0x80000034 mem:0x1001001c=0x00000034 mem:0x10010020=0x10000001 mem:0x10010024=0x00000010 mem:0x10010028=0x8dcd0000 mem:0x10010030=0x0000002c mem:0x10010034=0x400d6000
.data
res: .space 64
.ktext
addiu $s4, $s4, 1
mfc0 $k0, $13
li $k1, 0x8000007c
and $k0, $k0, $k1
sw $k0, 0($s7)
mfc0 $k1, $8, 1
sw $k1, 4($s7)
bltz $k0, inslot
nop
sw $zero, 8($s7)
mfc0 $k0, $14
addiu $k0, $k0, 4
b out
nop
inslot:
mfc0 $k1, $8, 2
sw $k1, 8($s7)
mfc0 $k0, $14
addiu $k0, $k0, 8
out:
mtc0 $k0, $14
addiu $s7, $s7, 12
li $k1, 0
eret
.text
li $s4, 0
la $s7, res
li $t0, 1
.word 0x0109500a        # movz $t2, $t0, $t1 (removed in Release 6: RI)
teq $zero, $zero
beq $zero, $zero, after
teq $zero, $zero
after:
lui $t6, 0x8000
la $t2, user
mtc0 $t2, $14
lui $t3, 0x2000
ori $t3, $t3, 0x12
mtc0 $t3, $12
eret
user:
lw $t5, 0($t6)
mfc0 $t5, $12
li $t2, 0
li $t3, 0
li $t6, 0
