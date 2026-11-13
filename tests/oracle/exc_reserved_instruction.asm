# A word that decodes to no instruction: Reserved Instruction (ExcCode 10), EPC = that word.
# MD00082 Vol I Rev 6.01 (mipsdoc.py search "Reserved Instruction exception").
# 0x00000028 = SPECIAL funct 0x28 (unassigned in MIPS32r2).
# oracle: expect cause=0x28 epc=0x00400004
nop
.word 0x00000028
nop
