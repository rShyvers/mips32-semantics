# Exception while Status.EXL = 1: EPC and Cause.BD are NOT updated, ExcCode is, Status keeps EXL.
# MD00090 Vol III Rev 6.02 "General Exception Processing" (mipsdoc.py search "EXL EPC BD not updated"):
# if Status.EXL = 0 then EPC <- PC, Cause.BD <- BD.  EPC is pre-loaded with 0x1234.
# oracle: expect epc=0x1234 cause=0x24 status=0x24000002
li $t0, 0x1234
mtc0 $t0, $14             # EPC
mfc0 $t1, $12
ori $t1, $t1, 2           # Status.EXL = 1
mtc0 $t1, $12
break
nop
