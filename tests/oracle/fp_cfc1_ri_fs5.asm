# Release 6: `cfc1 $s0, $5` (fs = 5, FRE) is a Reserved Instruction (ExcCode 10). The handler counts the exception in $s4, keeps
# Cause & 0x7c in $s5 and skips the instruction; $s0 keeps 7 (the destination is not written) and execution continues ($s1 = 9).
# MD00086 Vol II-A Rev 6.06 CFC1: Restrictions p.129 ("In Release 6 and later, a Reserved Instruction exception occurs if fs
# specifies a register that does not exist"); Description p.129 ("extended in Release 6 to allow user code to read and modify the
# Config5FRE bit. Such modification is allowed when this bit is present (as indicated by FIRUFRP)"); Operation p.130, fs = 5:
# "if ConfigAR ≤ 2 then temp ← UNPREDICTABLE else if not Config5UFR then SignalException(ReservedInstruction)", read as
# ConfigAR < 2 (misprint, Manual.Ops.CFC1); this profile has no FRE: FIR.FREP = 0 (MD00082 Vol I-A Rev 6.01 Table 6.5 p.88:
# "If FREP=1, then Config5UFE and Config5FRE are available"), Config5.UFR R0 (MD00090 Vol III Rev 6.02 Table 9.69 p.264).
# ExcCode 10 = RI (MD00090 Vol III Rev 6.02 Table 9.53 p.212).
# QEMU mips32r6-generic also signals Reserved Instruction here. Observed (W7): when the cfc1 is not the first instruction of a QEMU
# translation block, QEMU reports EPC = the start of the block (the model, as Vol III Rev 6.02 sec 9.38 p.217 requires, reports the
# cfc1), so the handler re-runs the block and counts 3; the `b` below makes the cfc1 start a block, and every field is compared.
# oracle: expect gpr:s4=1 gpr:s5=0x28 gpr:s0=7 gpr:s1=9
.ktext
addiu $s4, $s4, 1
mfc0 $k0, $13
andi $s5, $k0, 0x7c
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
eret
.text
li $s4, 0
li $s0, 7
b fre_read
nop
fre_read:
cfc1 $s0, $5
li $s1, 9
