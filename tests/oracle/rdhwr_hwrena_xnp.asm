# HWREna: writing all ones and reading back shows the implemented RDHWR registers; RDHWR 5 (XNP) reads 1 (no LLX/SCX family) in Kernel and,
# with HWREna bit 5 set, in User Mode.
# MD00090 Vol III Rev 6.02 sec 9.23 Table 9.39 p.175 ("If RDHWR register 'n' is not implemented, bit 'n' of this field returns a zero and is ignored
# on a write"; Impl 31..30 likewise), Table 9.40 p.176 ("Software may determine which registers are implemented by writing all ones to the HWREna
# register, then reading the value back"; implemented in the profile: 0 CPUNum, 1 SYNCI_Step, 2 CC, 3 CCRes, 5 XNP "Required (Release 6)", 29 ULR
# "In Release 6, the UserLocal register is required"; not: 4 PerfCnt "Required if any PerfCnt register is implemented", the profile has no
# performance counters; 6-28 reserved; 30-31 implementation-dependent, none), so the model reads back 0x2000002F; sec 9.50 Table 9.69 p.261
# (Config5.XNP: "1 LLX/SCX instruction family not supported"); MD00086 Vol II-A Rev 6.06 RDHWR p.333.
# s0 = HWREna after writing all ones; s1 = rdhwr 5 (Kernel); User Mode with HWREna all ones: s2 = rdhwr 5, s3 = rdhwr 4, s5 = rdhwr 6.
# The handler counts exceptions (s6) and keeps the last ExcCode (s7), skips the instruction.
# oracle: expect gpr:s0=0x2000002f gpr:s1=1 gpr:s2=1 gpr:s3=0x3333 gpr:s5=0x5555 gpr:s6=2 gpr:s7=10
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
li $s3, 0x3333
li $s5, 0x5555
li $t0, -1
mtc0 $t0, $7
mfc0 $s0, $7
rdhwr $s1, $5
la $t2, user
mtc0 $t2, $14
lui $t3, 0x2000
ori $t3, $t3, 0x12
mtc0 $t3, $12
li $t0, 0
eret
user:
rdhwr $s2, $5
rdhwr $s3, $4
rdhwr $s5, $6
li $t2, 0
li $t3, 0
li $k0, 0
