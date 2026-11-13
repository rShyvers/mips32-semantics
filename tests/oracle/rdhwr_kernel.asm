# RDHWR in Kernel Mode (Coprocessor 0 enabled, so every implemented hardware register is readable whatever HWREna holds), HWREna's
# implemented bits, and the Reserved Instruction exception for registers that are not implemented.
# MD00086 Vol II-A Rev 6.06 RDHWR p.332-334 (Table 5.4; Restrictions p.333: "Access to the specified hardware register is enabled if Coprocessor 0
# is enabled, or if the corresponding bit is set in the HWREna register. If access is not allowed or the register is not implemented, a Reserved
# Instruction Exception is signaled"); MD00090 Vol III Rev 6.02 sec 9.23 Table 9.39 p.175 (HWREna: "If RDHWR register 'n' is not implemented, bit 'n'
# of this field returns a zero and is ignored on a write"), Table 9.40 p.176 (CPUNum = EBase.CPUNum; SYNCI_Step "should be zero if there are no
# caches"; CC = Count; CCRes; 4, 5 Release 6; 6-28 reserved; 29 ULR "Required if the UserLocal register is implemented"; 30-31 "If they are not
# implemented, access results in a Reserved Instruction Exception"); sec 9.11 p.143 (UserLocal: "Prior to Release 6, this register only exists if
# the Config3ULRI register field is set").
# SYNCI_Step and CCRes are implementation-dependent (model: no caches, Count once per step; QEMU 24Kf: 32-byte cache lines, Count every second
# cycle): the raw values (t2, t3) are not compared; s1 checks "SYNCI_Step = 0 exactly when Config1 reports no instruction and no data cache",
# s2 checks CCRes >= 1. The handler counts exceptions in s6 and keeps the last ExcCode in s7, then skips the instruction.
# oracle: expect gpr:s0=0 gpr:s1=1 gpr:s2=1 gpr:s3=4242 gpr:s5=0xf gpr:s6=4 gpr:s7=10 gpr:t9=0x7777
# oracle: unpredictable gpr:t2 MD00090 Vol III Rev 6.02 Table 9.40 p.176: SYNCI_Step is the smallest cache line size to synchronize, or zero without caches (implementation-dependent; QEMU 24Kf has 32-byte lines)
# oracle: unpredictable gpr:t3 MD00090 Vol III Rev 6.02 Table 9.40 p.176: CCRes, the number of cycles between Count updates, is implementation-dependent (QEMU 24Kf: 2; model: 1)
# oracle: unpredictable gpr:t5 MD00090 Vol III Rev 6.02 sec 9.46 p.237: Config1 describes the implementation's caches and options (implementation-dependent)
# oracle: expect-deviation gpr:s4 MD00086 Vol II-A Rev 6.06 RDHWR p.333 and MD00090 Vol III Rev 6.02 sec 9.11 p.143: with Config3.ULRI = 0 (QEMU 24Kf reads Config3 = 0) UserLocal is not implemented, so rdhwr 29 must raise Reserved Instruction even in Kernel Mode; QEMU 24Kf returns a value (model: 1 exception, QEMU: 0)
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
# freeze Count (Cause.DC = 1) at a known value
lui $t0, 0x0800
mtc0 $t0, $13
li $t1, 4242
mtc0 $t1, $9
rdhwr $s0, $0
rdhwr $t2, $1
rdhwr $s3, $2
rdhwr $t3, $3
# s1: SYNCI_Step = 0 iff Config1.IL = 0 and Config1.DL = 0
mfc0 $t5, $16, 1
srl $t6, $t5, 19
andi $t6, $t6, 7
srl $t7, $t5, 10
andi $t7, $t7, 7
or $t6, $t6, $t7
sltiu $t6, $t6, 1
sltiu $t7, $t2, 1
xor $s1, $t6, $t7
xori $s1, $s1, 1
# s2: CCRes >= 1
sltu $s2, $zero, $t3
# registers 4 (Release 6 PerfCtr), 5 (Release 6 XNP), 6 (reserved), 30 (implementation-dependent, none): Reserved Instruction, t9 unchanged
li $t9, 0x7777
rdhwr $t9, $4
rdhwr $t9, $5
rdhwr $t9, $6
rdhwr $t9, $30
# register 29 (ULR): UserLocal is not implemented (Config3.ULRI = 0): Reserved Instruction
move $t8, $s6
rdhwr $t9, $29
subu $s4, $s6, $t8
move $s6, $t8
li $t9, 0x7777
li $t8, 0
# HWREna: write all ones, read back the implemented bits (3..0 on both)
li $t0, -1
mtc0 $t0, $7
mfc0 $s5, $7
andi $s5, $s5, 0xf
mtc0 $zero, $7
li $t0, 0
li $t1, 0
li $t6, 0
li $t7, 0
li $k0, 0
