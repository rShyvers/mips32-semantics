# Fixed Mapping MMU, Release 6: TLBWR, TLBWI, TLBP and TLBR raise Reserved Instruction in Kernel Mode, as does TLBINV; in User Mode each of
# them and TLBINVF raises Coprocessor Unusable (CE = 0) first. TLBINVF is not executed in Kernel Mode: on QEMU's TLB it invalidates every entry
# ("The virtual address and ASID are ignored", TLBINVF p.425), the harness's own mappings included (QEMU then hangs); the model raises RI for it
# as for TLBINV (not decoded; MipsRun on a lone Kernel Mode tlbinvf word stops with an unhandled exception, ExcCode 10).
# MD00090 Vol III Rev 6.02 sec A.1.3 p.317 ("The TLBWR, TLBWI, TLBP, and TLBR instructions are no longer required and must cause a Reserved
# Instruction Exception"); MD00086 Vol II-A Rev 6.06 TLBINV p.423 and TLBINVF p.425-426 ("Release 6: On processors that include a Block Address
# Translation (BAT) or Fixed Mapping (FM) MMU (ConfigMT = 2 or 3), the operation of this instruction causes a Reserved Instruction exception");
# TLBWI p.430, TLBWR p.432, TLBP p.427, TLBR p.428 ("If access to Coprocessor 0 is not enabled, a Coprocessor Unusable Exception is signaled");
# MD00090 Vol III Rev 6.02 Table 9.52 p.209 (CE), Table 9.53 p.212 (RI = 10, CpU = 11). The instructions are emitted as .word (the assembler has
# no TLB mnemonics: the profile does not decode them; llvm-mc refuses tlbinv/tlbinvf for mips32r6).
# QEMU mips32r6-generic has a TLB MMU (an implementation choice, MD00082 Vol I-A Rev 6.01 sec 2.4.2 p.32; the profile has the Fixed Mapping MMU,
# DECISIONS D4), so in Kernel Mode it executes them: the Kernel Mode part runs in kseg0 and makes them harmless there (an invalid entry for an
# unused page at the last TLB index, Wired = that index so TLBWR writes it too, an unused ASID for TLBINV; EntryHi, Index, Wired restored).
# The handler counts RI (s5) and CpU (s6), keeps the last CpU's CE (s7), skips the instruction.
# oracle: expect gpr:s5=5 gpr:s6=6 gpr:s7=0
# oracle: unpredictable gpr:s5 MD00090 Vol III Rev 6.02 sec A.1.3 p.317 and MD00082 Vol I-A Rev 6.01 sec 2.4.2 p.32: whether the TLB instructions exist depends on the MMU type, an implementation choice (profile: Fixed Mapping MMU, RI, asserted by expect; QEMU mips32r6-generic: TLB MMU, they execute, 0)
.ktext
mfc0 $k0, $13
andi $k1, $k0, 0x7c
xori $k1, $k1, 0x28
bnez $k1, not_ri
nop
addiu $s5, $s5, 1
not_ri:
andi $k1, $k0, 0x7c
xori $k1, $k1, 0x2c
bnez $k1, not_cpu
nop
addiu $s6, $s6, 1
srl $s7, $k0, 28
andi $s7, $s7, 3
not_cpu:
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
li $k1, 0
eret
kcode:
mfc0 $t9, $10              # EntryHi (QEMU; 0 on the model)
mfc0 $t1, $16, 1
srl $t1, $t1, 25
andi $t1, $t1, 0x3f        # Config1.MMUSize = the last TLB index
li $t2, 0x7f0000ff         # an unused page, ASID 0xff
mtc0 $t2, $10
mtc0 $zero, $2
mtc0 $zero, $3
mtc0 $t1, $0
mtc0 $t1, $6               # Wired = last index: TLBWR writes the last entry too
ehb
.word 0x42000002           # tlbwi
.word 0x42000006           # tlbwr
.word 0x42000008           # tlbp
mtc0 $t1, $0
ehb
.word 0x42000001           # tlbr
mtc0 $t2, $10
ehb
.word 0x42000003           # tlbinv
mtc0 $zero, $6
mtc0 $t9, $10
ehb
li $t9, 0
li $t1, 0
li $t2, 0
la $t6, back
jr $t6
nop
.text
li $s5, 0
li $s6, 0
li $s7, 9
la $t6, kcode
jr $t6
nop
back:
la $t6, user
mtc0 $t6, $14
lui $t3, 0x2000
ori $t3, $t3, 0x12
mtc0 $t3, $12
eret
user:
.word 0x42000002           # tlbwi
.word 0x42000006           # tlbwr
.word 0x42000008           # tlbp
.word 0x42000001           # tlbr
.word 0x42000003           # tlbinv
.word 0x42000004           # tlbinvf
li $t3, 0
li $t6, 0
