# Reserved Instruction for an unassigned major opcode (0x3F). See exc_reserved_instruction.
# oracle: expect cause=0x28 epc=0x00400000
.word 0xFC000000
nop
