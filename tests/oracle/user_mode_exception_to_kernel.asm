# An exception taken in User Mode enters Kernel Mode: Status.EXL = 1 with Status.UM still 1 in the handler (the handler can execute mfc0/mtc0 with CU0 = 0).
# The handler clears UM and returns with eret to `back` in kernel code, which reads Status (EXL = 0, UM = 0) with mfc0 - possible only in Kernel Mode.
# Also: an unimplemented COP0 encoding (rs = 3, reserved) and a CACHE word executed in User Mode with CU0 = 0 raise Coprocessor Unusable (CE = 0), not Reserved Instruction.
# MD00090 Vol III Rev 6.02 sec 3.2 p.21 ("The processor enters Kernel Mode ... as the result of an interrupt, exception, or error"); sec 6.2.21 p.99 (COP0 encodings: "If access to the coprocessor is not allowed, a Coprocessor Unusable Exception occurs instead");
# sec 6.2.22 p.100 ("A COP0 or Cache instruction"); Table 6.6 p.83 (CpU takes priority over RI); MD00086 Vol II-A Rev 6.06 ERET p.177, BREAK.
# oracle: expect gpr:s4=3 gpr:s1=0x20000000
# oracle: known-model-bug gpr:s1 MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.191 (FR, bit 26: "Release 6 disallows bi-modal support ...; i.e., FR is read-only"; "if floating-point is implemented then FR = 1 is required") and DECISIONS D2 (64-bit FPU, FR = 1): W5: the model still has Status.FR = 0 (QEMU reads 0x04000000 set)
# oracle: known-model-bug gpr:k1 MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.191 (FR, bit 26: "Release 6 disallows bi-modal support ...; i.e., FR is read-only"; "if floating-point is implemented then FR = 1 is required") and DECISIONS D2 (64-bit FPU, FR = 1): W5: the model still has Status.FR = 0 (QEMU reads 0x04000000 set)
# oracle: known-model-bug mem:0x10010004 MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.191 (FR, bit 26: "Release 6 disallows bi-modal support ...; i.e., FR is read-only"; "if floating-point is implemented then FR = 1 is required") and DECISIONS D2 (64-bit FPU, FR = 1): W5: the model still has Status.FR = 0 (QEMU reads 0x04000000 set)
# oracle: known-model-bug mem:0x1001000c MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.191 (FR, bit 26: "Release 6 disallows bi-modal support ...; i.e., FR is read-only"; "if floating-point is implemented then FR = 1 is required") and DECISIONS D2 (64-bit FPU, FR = 1): W5: the model still has Status.FR = 0 (QEMU reads 0x04000000 set)
# oracle: known-model-bug mem:0x10010014 MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.191 (FR, bit 26: "Release 6 disallows bi-modal support ...; i.e., FR is read-only"; "if floating-point is implemented then FR = 1 is required") and DECISIONS D2 (64-bit FPU, FR = 1): W5: the model still has Status.FR = 0 (QEMU reads 0x04000000 set)
.data
res: .space 64
.ktext
mfc0 $k0, $13
sw $k0, 0($s7)
mfc0 $k1, $12
sw $k1, 4($s7)
addiu $s7, $s7, 8
addiu $s4, $s4, 1
andi $k0, $k0, 0x7c
li $k1, 0x24
beq $k0, $k1, tokernel
nop
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
eret
tokernel:
la $k0, back
mtc0 $k0, $14
mfc0 $k1, $12
li $k0, -17
and $k1, $k1, $k0
mtc0 $k1, $12
eret
.text
la $s7, res
li $s4, 0
la $t0, user
mtc0 $t0, $14
lui $t1, 0x2000
ori $t1, $t1, 0x12
mtc0 $t1, $12
eret
user:
.word 0x40600000
.word 0xbc000000
break
nop
back:
mfc0 $s1, $12
