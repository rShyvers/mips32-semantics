# add overflow (negative side) with no handler: Integer Overflow, rt unchanged. MD00086 Vol II-A Rev 6.06: ADD p.33.
# (Was the ADDI form; Release 6 removed ADDI.)
# oracle: expect gpr:t1=0x77 cause=0x30
lui $t0, 0x8000           # INT_MIN
li $t1, 0x77
li $t2, -1
add $t1, $t0, $t2
nop
