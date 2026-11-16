# abs.s / abs.d / neg.s / neg.d of a non-NaN operand after an inexact mul.s (Cause.I = Flags.I = 1). Release 6 requires FCSR.ABS2008 = 1
# (MD00082 Vol I-A Rev 6.01 FCSR Table 6.8 p.93), and then ABS/NEG are non-arithmetic (MD00086 Vol II-A Rev 6.06 ABS.fmt p.32 / NEG.fmt p.307:
# "If FCSRABS2008=1 then this operation is non-arithmetic"): Cause and Flags stay (0x1004), like mov.s (MOV.fmt p.275, the control case).
# Per case: result bits (high word for .d, via mfhc1) and FCSR after (the read-only NAN2008/ABS2008 bits 19..18 read 1, so 0x000c1004).
# oracle: expect mem:0x10010024=0x000c1004
# oracle: expect mem:0x10010000=0x40490fdb mem:0x10010008=0x400921fb mem:0x10010010=0x40490fdb mem:0x10010018=0x400921fb mem:0x10010020=0xc0490fdb
.data
res: .space 64
.text
la $s7, res
li $t9, 0x3f800001
mtc1 $t9, $f6
li $t9, 0xc0490fdb
mtc1 $t9, $f2
li $t9, 0x54442d18
mtc1 $t9, $f4
li $t9, 0xc00921fb
mthc1 $t9, $f4
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
mfhc1 $t0, $f10
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
mfhc1 $t0, $f10
sw $t0, 24($s7)
sw $t1, 28($s7)
ctc1 $zero, $31
mul.s $f8, $f6, $f6
mov.s $f10, $f2
cfc1 $t1, $31
mfc1 $t0, $f10
sw $t0, 32($s7)
sw $t1, 36($s7)
mthc1 $zero, $f4
mthc1 $zero, $f10
li $v0, 10
syscall
