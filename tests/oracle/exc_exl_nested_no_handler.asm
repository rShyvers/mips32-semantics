# Exception while Status.EXL = 1: EPC and Cause.BD are NOT updated, ExcCode is, Status keeps EXL.
# MD00090 Vol III Rev 6.02 "General Exception Processing" (mipsdoc.py search "EXL EPC BD not updated"):
# if Status.EXL = 0 then EPC <- PC, Cause.BD <- BD.  EPC is pre-loaded with 0x1234.
# oracle: expect epc=0x1234 cause=0x24 status=0x20000002
# oracle: known-model-bug gpr:t1 MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.191 (FR, bit 26: "Release 6 disallows bi-modal support ...; i.e., FR is read-only"; "if floating-point is implemented then FR = 1 is required") and DECISIONS D2 (64-bit FPU, FR = 1): W5: the model still has Status.FR = 0 (QEMU reads 0x04000000 set)
li $t0, 0x1234
mtc0 $t0, $14             # EPC
mfc0 $t1, $12
ori $t1, $t1, 2           # Status.EXL = 1
mtc0 $t1, $12
break
nop
