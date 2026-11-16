# Release 6: `ctc1 $t0, $6` (fs = 6 (NFRE)) is a Reserved Instruction (ExcCode 10, a register that does not exist). The handler counts the exception in $s4 and skips the instruction;
# $s0 keeps 7 (the destination is not written) and execution continues with the next instruction ($s1 = 9).
# MD00086 Vol II-A Rev 6.06 CFC1 p.129-130 (Restrictions: 'In Release 6 and later, a Reserved Instruction exception occurs if fs specifies a register that does not exist'; Operation: fs = 1 (UFR),
# fs = 4 (UNFR) 'Release 6 traps', other nonexistent fs 'Release 6 traps'), CTC1 p.149-150 (fs = 1, 4 'Release 6 traps'; fs = 5, 6 (FRE/NFRE): Reserved Instruction without FIRUFRP and Config5UFR);
# MD00082 Vol I-A Rev 6.01 6.5.5 p.96 (Release 6 removes the FCCs and FCCR).
# oracle: expect gpr:s4=1
# oracle: expect-deviation gpr:s4 MD00086 Vol II-A Rev 6.06 CTC1 Restrictions p.149 ("the result is UNPREDICTABLE if fd specifies the UFR, UNFR, FRE and NFRE aliases, with fs anything other than 00000, GPR[0]. Release 6 implementations and later are required to produce a Reserved Instruction exception"; here rt = $t0; the Operation p.150 says only 'if ConfigAR ≤ 2 then UNPREDICTABLE' for fs = 5, 6): the model raises Reserved Instruction; QEMU mips32r6-generic executes it without an exception (the handler never runs, count 0)
# oracle: expect-deviation gpr:k0 same as s4 (the handler's EPC scratch)
.data
res: .space 64
.ktext
addiu $s4, $s4, 1
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
eret
.text
li $s4, 0
li $s0, 7
li $t0, 0xffffffff
ctc1 $t0, $6
li $s1, 9
