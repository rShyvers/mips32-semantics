# SDBBP with Config5.SBRI = 1 in User Mode raises Reserved Instruction (ExcCode 10); BadInstr = the sdbbp word.
# MD00086 Vol II-A Rev 6.06 SDBBP p.361 (Release 6 encoding SPECIAL, function 001110; Operation: "if Config5.SBRI=1 then /* SBRI is a MIPS Release 6
# feature */ SignalException(ReservedInstruction) endif"); MD00090 Vol III Rev 6.02 sec 9.50 Table 9.69 p.263 (SBRI = 1: "User (or supervisor, if
# supported) execution of SDBBP will cause a Reserved Instruction exception"), sec 9.25 p.179 (BadInstr), Table 9.53 p.212 (RI = 10).
# Only this case is compared: the profile has no EJTAG and raises RI for SDBBP whatever SBRI holds and in every mode (DECISIONS D7). QEMU
# mips32r6-generic did not come back to the harness (timeout, probed with this program) with SBRI = 0 in User Mode, nor with SBRI = 1 in Kernel
# Mode, where p.361's pseudocode (RI) and p.263's table (SBRI = 1: "SDBBP instruction can only be executed in kernel mode") read differently.
# Emitted as .word: the assembler has no sdbbp (the profile does not decode it).
# The handler counts entries (s4), keeps ExcCode (s5) and BadInstr (s6, s7), skips the instruction.
# oracle: expect gpr:s4=2 gpr:s5=10 gpr:s6=0x0000000e gpr:s7=0x0000048e
.ktext
addiu $s4, $s4, 1
mfc0 $k0, $13
andi $s5, $k0, 0x7c
srl $s5, $s5, 2
move $s6, $s7
mfc0 $s7, $8, 1
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
li $k1, 0
eret
.text
li $s4, 0
mfc0 $t0, $16, 5
ori $t0, $t0, 0x40
mtc0 $t0, $16, 5
la $t2, user
mtc0 $t2, $14
lui $t3, 0x2000
ori $t3, $t3, 0x12
mtc0 $t3, $12
li $t0, 0
eret
user:
.word 0x0000000e           # sdbbp
.word 0x0000048e           # sdbbp 0x12
li $t2, 0
li $t3, 0
