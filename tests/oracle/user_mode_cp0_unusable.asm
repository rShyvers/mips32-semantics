# User Mode (Status.UM = 1, EXL = ERL = 0) with Status.CU0 = 0: every coprocessor-0 instruction raises Coprocessor Unusable with Cause.CE = 0.
# Kernel code sets EPC = user, Status = CU1|UM|EXL and executes eret, entering User Mode at `user` (kuseg text). The handler (Kernel Mode, EXL = 1)
# logs Cause and Status per exception and skips the instruction. Covered: mfc0, mtc0, di, ei, eret, wait.
# MD00090 Vol III Rev 6.02 sec 3.4 p.22 (User Mode), sec 3.5.3 p.23 (Coprocessor 0 Enable), sec 6.2.22 p.100 (CpU: "A COP0 or Cache instruction ... in a mode other than Debug Mode or Kernel Mode, and the CU0 bit ... was a zero"; CE = unit number);
# MD00086 Vol II-A Rev 6.06 MFC0 p.266, MTC0 p.291, DI p.164, EI p.176, ERET p.178, WAIT p.443 ("Exceptions: Coprocessor Unusable").
# oracle: expect gpr:s4=6 gpr:s5=6 gpr:t2=0x5555 gpr:t3=0x6666
# oracle: known-model-bug mem:0x10010004 MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.191 (FR, bit 26: "Release 6 disallows bi-modal support ...; i.e., FR is read-only"; "if floating-point is implemented then FR = 1 is required") and DECISIONS D2 (64-bit FPU, FR = 1): W5: the model still has Status.FR = 0 (QEMU reads 0x04000000 set)
# oracle: known-model-bug mem:0x1001000c MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.191 (FR, bit 26: "Release 6 disallows bi-modal support ...; i.e., FR is read-only"; "if floating-point is implemented then FR = 1 is required") and DECISIONS D2 (64-bit FPU, FR = 1): W5: the model still has Status.FR = 0 (QEMU reads 0x04000000 set)
# oracle: known-model-bug mem:0x10010014 MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.191 (FR, bit 26: "Release 6 disallows bi-modal support ...; i.e., FR is read-only"; "if floating-point is implemented then FR = 1 is required") and DECISIONS D2 (64-bit FPU, FR = 1): W5: the model still has Status.FR = 0 (QEMU reads 0x04000000 set)
# oracle: known-model-bug mem:0x1001001c MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.191 (FR, bit 26: "Release 6 disallows bi-modal support ...; i.e., FR is read-only"; "if floating-point is implemented then FR = 1 is required") and DECISIONS D2 (64-bit FPU, FR = 1): W5: the model still has Status.FR = 0 (QEMU reads 0x04000000 set)
# oracle: known-model-bug mem:0x10010024 MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.191 (FR, bit 26: "Release 6 disallows bi-modal support ...; i.e., FR is read-only"; "if floating-point is implemented then FR = 1 is required") and DECISIONS D2 (64-bit FPU, FR = 1): W5: the model still has Status.FR = 0 (QEMU reads 0x04000000 set)
# oracle: known-model-bug mem:0x1001002c MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.191 (FR, bit 26: "Release 6 disallows bi-modal support ...; i.e., FR is read-only"; "if floating-point is implemented then FR = 1 is required") and DECISIONS D2 (64-bit FPU, FR = 1): W5: the model still has Status.FR = 0 (QEMU reads 0x04000000 set)
.data
res: .space 64
.ktext
mfc0 $k0, $13
sw $k0, 0($s7)
mfc0 $k0, $12
sw $k0, 4($s7)
addiu $s7, $s7, 8
addiu $s4, $s4, 1
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
eret
.text
la $s7, res
li $s4, 0
li $s5, 0
li $t2, 0x5555
li $t3, 0x6666
la $t0, user
mtc0 $t0, $14
lui $t1, 0x2000
ori $t1, $t1, 0x12
mtc0 $t1, $12
eret
user:
mfc0 $t2, $12
addiu $s5, $s5, 1
mtc0 $zero, $12
addiu $s5, $s5, 1
di $t3
addiu $s5, $s5, 1
ei
addiu $s5, $s5, 1
eret
addiu $s5, $s5, 1
wait
addiu $s5, $s5, 1
