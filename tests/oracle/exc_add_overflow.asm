# add overflow with no handler: Integer Overflow (ExcCode 12), EPC = the add, rd NOT written.
# MD00086 Vol II-A Rev 6.06: ADD p.33 (Exceptions: Integer Overflow; GPR[rd] is not modified).
# oracle: expect gpr:t2=0x55 cause=0x30 epc=0x00400010
li $t0, 0x7fffffff
li $t1, 1
li $t2, 0x55
add $t2, $t0, $t1
li $t2, 0x66              # not reached
