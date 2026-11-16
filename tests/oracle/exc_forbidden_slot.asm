# An exception in the forbidden slot of a not-taken compact branch: where it is reported. MD00082 Vol I-A
# Rev 6.01 sec 5.3.2.2, p.62: "If an exception or interrupt prevents the completion of an instruction in a
# delay slot or forbidden slot, the hardware reports an Exception PC (CP0 EPC) of the branch, with a status
# bit set (StatusBD) to indicate that the exception was for the instruction in the delay slot of the
# branch" (the bit is Cause.BD). The profile follows this text (DECISIONS D6): EPC = the branch, BD = 1;
# MD00090 Vol III Rev 6.02 sec 6.2.3 p.87 tests only InstructionInBranchDelaySlot. The handler records
# Cause in $s4 and EPC in $s3 (first exception), counts in $s7, and resumes at EPC + 8 if BD else EPC + 4
# (both are the instruction after the slot). Two exceptions: a trap (teq) in the slot of a bnezc, and a
# Reserved Instruction (a CTI) in the slot of a beqc; the second's EPC/BD go to $s5/$s2.
# (Observed 2026-11-16: QEMU mips32r6-generic reports the same EPC and BD on both.)
# oracle: expect gpr:s7=2 gpr:s0=3 gpr:s3=0x00400008 gpr:s4=0x80000034 gpr:s5=0x0040001c gpr:s2=0x80000028
.ktext
mfc0 $k0, $13
mfc0 $k1, $14
addiu $s7, $s7, 1
bnez $s4, second
nop
move $s4, $k0
move $s3, $k1
b resume
nop
second: move $s2, $k0
move $s5, $k1
resume: bltz $k0, bd
nop
addiu $k1, $k1, 4
mtc0 $k1, $14
eret
bd: addiu $k1, $k1, 8
mtc0 $k1, $14
eret
.text
li $s0, 0
li $t0, 0
bnezc $t0, a1              # 0x00400008, not taken
teq $zero, $zero           # trap in the forbidden slot
a1: ori $s0, $s0, 1
li $t1, 1
li $t2, 2
beqc $t1, $t2, a2          # 0x0040001c, not taken
bc a2                      # CTI in the forbidden slot: Reserved Instruction
a2: ori $s0, $s0, 2
