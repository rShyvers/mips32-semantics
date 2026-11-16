# Release 6 PC-relative instructions ADDIUPC, AUIPC, ALUIPC, LWPC: PC is the address of the instruction itself, also in a branch
# delay slot (they are not control transfer instructions). The expected values are address differences, independent of the layout.
# MD00086 Vol II-A Rev 6.06: ADDIUPC p.37 ("GPR[rs] <- ( PC + sign_extend( immediate << 2 ) )"; the assembler operand is the byte
# offset), AUIPC p.48, ALUIPC p.43 ("~0x0FFFF & ( PC + sign_extend( immediate << 16 ) )"), LWPC p.246 (a word load at
# PC + sign_extend(offset) << 2); Table 1.1 p.6 (PC: "the address of the instruction word"); MD00082 Vol I-A Rev 6.01 5.3.2.1 p.62
# (the instructions forbidden in a delay slot: CTIs, ERET, ERETNC, DERET, WAIT, PAUSE).
# oracle: expect gpr:s0=0 gpr:s1=0x00100008 gpr:s2=0xee480000 gpr:s3=0xee480000 gpr:s4=8 gpr:s5=0x00010004 gpr:s6=0 gpr:a0=0x00020004 gpr:a1=0x3402000a
nal
nop
addiupc $s0, 0          # the address of this instruction = $ra
subu $s0, $s0, $ra
addiupc $t0, -8
addiupc $t1, 1048572
subu $s1, $t1, $t0      # (A + 4 + 1048572) - (A - 8)
lwpc $s2, 0             # its own word: PCREL | rs = 18 | 01 | 0
lwpc $s3, -4            # the previous word
addiupc $t5, 0          # B
beq $zero, $zero, L1
addiupc $s4, 0          # delay slot: B + 8
L1:
subu $s4, $s4, $t5
addiupc $t6, 0          # C
auipc $t7, 1            # C + 4 + 0x10000
subu $s5, $t7, $t6
aluipc $t8, 1           # (C + 8 + 0x10000) & ~0xffff
andi $s6, $t8, 0xffff   # 0
auipc $t2, 0xffff       # D - 0x10000
auipc $t3, 1            # D + 4 + 0x10000
subu $a0, $t3, $t2      # (D + 4 + 0x10000) - (D - 0x10000) = 0x20004
addiupc $t9, 0
b L2
lwpc $a1, 4             # delay slot: the word after it (li $v0, 10 = ori $v0, $zero, 10)
L2:
li $v0, 10
syscall
