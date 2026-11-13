# addi overflow (negative side) with no handler. MD00086 Vol II-A Rev 6.06: ADDI p.35.
# oracle: expect gpr:t1=0x77 cause=0x30
lui $t0, 0x8000           # INT_MIN
li $t1, 0x77
addi $t1, $t0, -1
nop
