# EXT with lsb = 20, msbd = 19 (lsb + msbd = 39 > 31): "The operation is UNPREDICTABLE if lsb+msbd > 31" (MD00086
# Vol II-A Rev 6.06, EXT p.183). The word matches the EXT diagram with an UNPREDICTABLE field value
# (Manual.UnpredictableEncoding); the model's choice (Oracle.unpredictableEncoding, SPEC-NOTES 11) is Reserved
# Instruction (ExcCode 10, Cause 0x28), EPC = the word.
# oracle: expect cause=0x28 epc=0x00400008
li $t0, 0x12345678
.word 0x7D099D00
li $s0, 99
