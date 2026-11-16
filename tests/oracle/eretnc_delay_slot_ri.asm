# ERETNC in the delay slot of a branch raises Reserved Instruction (Cause.BD = 1, EPC = the branch, BadInstr = the eretnc word, BadInstrP = the
# branch word).
# MD00086 Vol II-A Rev 6.06 ERETNC p.179 (Restrictions: "Release 6 implementations are required to signal a Reserved Instruction exception if ERETNC
# is executed in the delay slot or Release 6 forbidden slot of a branch or jump instruction"); MD00090 Vol III Rev 6.02 sec 9.25 p.179 (BadInstr),
# sec 9.26 p.181 (BadInstrP: "contains the prior branch instruction, when the faulting instruction is in a branch delay slot"), Table 9.52 p.209
# (BD), Table 9.53 p.212 (RI = 10).
# The handler keeps Cause & 0x8000007c (s5), EPC minus the branch address (s6), BadInstr (s2), BadInstrP (s3), counts entries (s4), and resumes at
# the branch's target (EPC + 8).
# oracle: expect gpr:s4=1 gpr:s5=0x80000028 gpr:s6=0 gpr:s2=0x42000058 gpr:s3=0x10000001
.ktext
addiu $s4, $s4, 1
mfc0 $k0, $13
li $k1, 0x8000007c
and $s5, $k0, $k1
mfc0 $s2, $8, 1
mfc0 $s3, $8, 2
mfc0 $k0, $14
subu $s6, $k0, $t0
addiu $k0, $k0, 8
mtc0 $k0, $14
li $k1, 0
eret
.text
li $s4, 0
la $t0, br
br: beq $zero, $zero, after
eretnc
after:
li $t0, 0
