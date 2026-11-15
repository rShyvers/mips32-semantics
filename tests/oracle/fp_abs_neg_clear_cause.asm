# abs.s / abs.d / neg.s / neg.d of a non-NaN operand after an inexact mul.s (Cause.I = Flags.I = 1): with FIR.Has2008 = 0 ABS/NEG are
# arithmetic, so they write FCSR.Cause (all zero here: no exception condition) and leave the Flags (sticky I). Control: mov.s is
# non-arithmetic and leaves Cause and Flags. Per case: result bits (high word for .d) and FCSR after.
# MD00086 Vol II-A Rev 6.06 ABS.fmt p.32 / NEG.fmt p.307 ("If FIRHas2008=0 or FCSRABS2008=0 then this operation is arithmetic"),
# MOV.fmt p.275 ("The move is non-arithmetic; it causes no IEEE 754 exceptions, and the FCSRCause and FCSRFlags fields are not modified");
# MD00082 Vol I-A Rev 6.01 sec 6.7.1 p.99 ("The Cause bits are written during each floating point arithmetic operation to show any
# exception conditions that arise during the operation. The bit is set to 1 if the corresponding exception condition arises; otherwise it is set to 0").
# QEMU 24Kf treats abs/neg as non-arithmetic for non-NaN operands (Cause.I stays set).
# oracle: expect mem:0x10010004=0x00000004 mem:0x1001000c=0x00000004 mem:0x10010014=0x00000004 mem:0x1001001c=0x00000004
# oracle: expect mem:0x10010024=0x00001004
# oracle: expect mem:0x10010000=0x40490fdb mem:0x10010008=0x400921fb mem:0x10010010=0x40490fdb mem:0x10010018=0x400921fb mem:0x10010020=0xc0490fdb
# oracle: expect-deviation mem:0x10010004 MD00086 Vol II-A Rev 6.06 ABS.fmt p.32 / NEG.fmt p.307 (Has2008=0: arithmetic) and MD00082 Vol I-A Rev 6.01 sec 6.7.1 p.99 ("The Cause bits are written during each floating point arithmetic operation"): FCSR after abs.s of a non-NaN operand is Flags.I only (model 0x00000004); QEMU keeps Cause.I (0x00001004)
# oracle: expect-deviation mem:0x1001000c MD00086 Vol II-A Rev 6.06 ABS.fmt p.32 / NEG.fmt p.307 (Has2008=0: arithmetic) and MD00082 Vol I-A Rev 6.01 sec 6.7.1 p.99 ("The Cause bits are written during each floating point arithmetic operation"): FCSR after abs.d of a non-NaN operand is Flags.I only (model 0x00000004); QEMU keeps Cause.I (0x00001004)
# oracle: expect-deviation mem:0x10010014 MD00086 Vol II-A Rev 6.06 ABS.fmt p.32 / NEG.fmt p.307 (Has2008=0: arithmetic) and MD00082 Vol I-A Rev 6.01 sec 6.7.1 p.99 ("The Cause bits are written during each floating point arithmetic operation"): FCSR after neg.s of a non-NaN operand is Flags.I only (model 0x00000004); QEMU keeps Cause.I (0x00001004)
# oracle: expect-deviation mem:0x1001001c MD00086 Vol II-A Rev 6.06 ABS.fmt p.32 / NEG.fmt p.307 (Has2008=0: arithmetic) and MD00082 Vol I-A Rev 6.01 sec 6.7.1 p.99 ("The Cause bits are written during each floating point arithmetic operation"): FCSR after neg.d of a non-NaN operand is Flags.I only (model 0x00000004); QEMU keeps Cause.I (0x00001004)
.data
res: .space 64
.text
la $s7, res
li $t9, 0x3f800001
mtc1 $t9, $f6
li $t9, 0xc0490fdb
mtc1 $t9, $f2
li $t9, 0xc00921fb
mtc1 $t9, $f5
li $t9, 0x54442d18
mtc1 $t9, $f4
ctc1 $zero, $31
mul.s $f8, $f6, $f6
abs.s $f10, $f2
cfc1 $t1, $31
mfc1 $t0, $f10
sw $t0, 0($s7)
sw $t1, 4($s7)
ctc1 $zero, $31
mul.s $f8, $f6, $f6
abs.d $f10, $f4
cfc1 $t1, $31
mfc1 $t0, $f11
sw $t0, 8($s7)
sw $t1, 12($s7)
ctc1 $zero, $31
mul.s $f8, $f6, $f6
neg.s $f10, $f2
cfc1 $t1, $31
mfc1 $t0, $f10
sw $t0, 16($s7)
sw $t1, 20($s7)
ctc1 $zero, $31
mul.s $f8, $f6, $f6
neg.d $f10, $f4
cfc1 $t1, $31
mfc1 $t0, $f11
sw $t0, 24($s7)
sw $t1, 28($s7)
ctc1 $zero, $31
mul.s $f8, $f6, $f6
mov.s $f10, $f2
cfc1 $t1, $31
mfc1 $t0, $f10
sw $t0, 32($s7)
sw $t1, 36($s7)
li $v0, 10
syscall
