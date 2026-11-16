# Encodings of instructions Release 6 removed raise Reserved Instruction (ExcCode 10) in Release 6; the handler logs
# Cause/EPC per instruction and skips it. (Emitted as .word: the assembler rejects the removed mnemonics.)
# MD00086 Vol II-A Rev 6.06 Table A.1 p.451 ("6Rm and 6R instructions signal a Reserved Instruction exception when
# executed by a Release 6 implementation"); JR p.207 (pre-Release 6 JR encoding removed); NAL p.306 / BAL p.50
# (BLTZAL/BGEZAL with rs != 0 "required to signal a Reserved Instruction exception"); LL p.223, SC p.347, PREF p.321
# (pre-Release 6 opcodes removed); CLZ p.135 (SPECIAL2 form removed).
# oracle: expect gpr:s4=21
.data
res: .space 192
.ktext
mfc0 $k0, $13
sw $k0, 0($s7)
mfc0 $k0, $14
sw $k0, 4($s7)
addiu $s7, $s7, 8
addiu $s4, $s4, 1
addiu $k0, $k0, 4
mtc0 $k0, $14
eret
.text
la $s7, res
li $s4, 0
la $t0, res
li $t1, 3
.word 0x01090018        # mult $t0, $t1
.word 0x00005010        # mfhi $t2
.word 0x00005012        # mflo $t2
.word 0x01000011        # mthi $t0
.word 0x0109500b        # movn $t2, $t0, $t1
.word 0x0109500a        # movz $t2, $t0, $t1
.word 0x71095002        # mul $t2, $t0, $t1 (SPECIAL2)
.word 0x71090000        # madd $t0, $t1
.word 0x710a5020        # clz $t2, $t0 (SPECIAL2)
.word 0x890a0000        # lwl $t2, 0($t0)
.word 0xb90a0000        # swr $t2, 0($t0)
.word 0x050c0001        # teqi $t0, 1
.word 0x050b0001        # tltiu $t0, 1
.word 0x01000008        # jr $t0
.word 0xc10a0000        # ll $t2, 0($t0) (opcode 0x30)
.word 0xe10a0000        # sc $t2, 0($t0) (opcode 0x38)
.word 0xcd000000        # pref 0, 0($t0) (opcode 0x33)
.word 0x01005001        # movf $t2, $t0, $fcc0 (MOVCI)
.word 0x05100002        # bltzal $t0, 8 (rs != 0)
.word 0x05110002        # bgezal $t0, 8 (rs != 0)
.word 0x05020002        # bltzl $t0, 8
li $s0, 7                # then runs off the end of the text
