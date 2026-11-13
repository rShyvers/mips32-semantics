# sub overflow with no handler: INT_MIN - 1. MD00086 Vol II-A Rev 6.06: SUB p.388.
# oracle: expect gpr:t2=0x77 cause=0x30
lui $t0, 0x8000
li $t1, 1
li $t2, 0x77
sub $t2, $t0, $t1
nop
