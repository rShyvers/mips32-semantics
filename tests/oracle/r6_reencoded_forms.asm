# Release 6 forms of retained instructions: AUI with rs != 0 (LUI = AUI rs = 0), LL/SC and PREF with 9-bit signed offsets
# (-256..255, incl. negative), PAUSE with LLbit clear (a no-op: execution continues with the next instruction), RDHWR with a
# sel field (sel = 0 reads CC; a sel undefined for the register is a Reserved Instruction), CLO/CLZ in the SPECIAL rt = 0,
# sa = 1 encoding. The handler counts exceptions in $s7 (ExcCode history in $t9) and skips the instruction.
# MD00086 Vol II-A Rev 6.06: AUI p.47 ("GPR[rt] <- GPR[rs] + sign_extend(immediate << 16)"; LUI is AUI with rs = 0), LL p.223,
# SC p.347, PREF p.321 (9-bit offset, bits 15..7), PAUSE p.317 ("if LLBit != 0 then ..."; otherwise the next instruction),
# RDHWR p.332-333 ("In Release 6, when the 3-bit sel is undefined for use with a specific register number, then a Reserved
# Instruction ..."), CLO p.134, CLZ p.135.
# oracle: expect gpr:s0=0x12355678 gpr:s1=0x12335678 gpr:s2=0x80000000 gpr:s3=0x7fff0000 gpr:s4=0x11111111 gpr:t3=1
# oracle: expect gpr:s5=0 gpr:t6=1 gpr:t7=0 mem:0x10010000=0xabc mem:0x100100fc=0x77 gpr:s6=4242 gpr:a0=0x7777
# oracle: expect gpr:s7=1 gpr:t9=10 gpr:k0=0x0040009c gpr:a1=3 gpr:a2=8 gpr:a3=32 gpr:v1=0 gpr:k1=31
# oracle: expect-deviation gpr:a0 MD00086 Vol II-A Rev 6.06 RDHWR p.333 ("In Release 6, when the 3-bit sel is undefined for use with a specific register number, then a Reserved Instruction Exception") : rdhwr $2 (CC) with sel = 1 must be a Reserved Instruction (model); QEMU mips32r6-generic ignores sel and returns Count
# oracle: expect-deviation gpr:s7 MD00086 Vol II-A Rev 6.06 RDHWR p.333 ("In Release 6, when the 3-bit sel is undefined for use with a specific register number, then a Reserved Instruction Exception") : rdhwr $2 (CC) with sel = 1 must be a Reserved Instruction (model); QEMU mips32r6-generic ignores sel and returns Count
# oracle: expect-deviation gpr:t9 MD00086 Vol II-A Rev 6.06 RDHWR p.333 ("In Release 6, when the 3-bit sel is undefined for use with a specific register number, then a Reserved Instruction Exception") : rdhwr $2 (CC) with sel = 1 must be a Reserved Instruction (model); QEMU mips32r6-generic ignores sel and returns Count
# oracle: expect-deviation gpr:k0 MD00086 Vol II-A Rev 6.06 RDHWR p.333 ("In Release 6, when the 3-bit sel is undefined for use with a specific register number, then a Reserved Instruction Exception") : rdhwr $2 (CC) with sel = 1 must be a Reserved Instruction (model); QEMU mips32r6-generic ignores sel and returns Count
.data
w: .word 0x11111111, 0x22222222, 0x33333333, 0x44444444
.space 512
.ktext
mfc0 $k0, $13
srl $k0, $k0, 2
andi $k0, $k0, 0x1f
sll $t9, $t9, 8
or $t9, $t9, $k0
addiu $s7, $s7, 1
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
eret
.text
li $s7, 0
li $t9, 0
la $t0, w
li $t1, 0x12345678
aui $s0, $t1, 0x0001       # 0x12355678
aui $s1, $t1, 0xffff       # + 0xffff0000 = 0x12335678
aui $s2, $zero, 0x8000     # LUI idiom
lui $s3, 0x7fff
addiu $t2, $t0, 256
ll $s4, -256($t2)          # w[0]
li $t3, 0xabc
sc $t3, -256($t2)          # succeeds: t3 = 1, w[0] = 0xabc
ll $s5, 252($t0)           # w + 252 (zero)
li $t6, 0x77
sc $t6, 252($t0)           # succeeds: t6 = 1
pref 0, -256($t2)
pref 23, 255($t0)          # misaligned address: PREF takes no address exception
pause                      # LLbit clear (the sc cleared it): no-op
li $t7, 0
# CC with sel = 0, Count frozen (Cause.DC = 1)
lui $t4, 0x0800
mtc0 $t4, $13
li $t4, 4242
mtc0 $t4, $9
rdhwr $s6, $2, 0
# CLO / CLZ
li $t4, 0xe0000000
clo $a1, $t4               # 3
li $t4, 0x00ffffff
clz $a2, $t4               # 8
clz $a3, $zero             # 32
clo $v1, $zero             # 0
li $t4, 0xfffffffe
clo $k1, $t4               # 31
li $a0, 0x7777
rdhwr $a0, $2, 1           # sel undefined for CC: Reserved Instruction, a0 unchanged (last: QEMU deviates)
