# teq (taken) with no handler: Trap (ExcCode 13), EPC = the trap. MD00086 Vol II-A Rev 6.06: TEQ p.416.
# oracle: expect cause=0x34 epc=0x00400008
li $t0, 3
li $t1, 3
teq $t0, $t1
nop
