# Release 6: ctc1 to a control register that does not exist for writing (FIR, fs = 0) is a Reserved Instruction (ExcCode 10). The handler counts
# the exceptions in $s4 and skips the instruction. The model ignores the write (no exception): a known model bug.
# MD00086 Vol II-A Rev 6.06 CTC1 p.149 ('In Release 6 and later, a Reserved Instruction exception occurs if fs specifies a register that does not exist'),
# p.150 (Operation, other fs: 'if Config2AR >= 2 SignalException(ReservedInstruction) /* Release 6 traps */').
# oracle: known-model-bug gpr:s4 MD00086 Vol II-A Rev 6.06 CTC1 p.149-150: ctc1 to fs = 0 (FIR) raises Reserved Instruction in Release 6; model (lead, Exec FpuControl): the write is ignored, no exception
# oracle: known-model-bug gpr:k0 same (the handler's EPC never read in the model)
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
li $t0, 0xffffffff
ctc1 $t0, $0
li $s0, 7
