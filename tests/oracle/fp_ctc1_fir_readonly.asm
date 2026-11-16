# cfc1 FIR twice (stable); cvt.d.w exact; PRId (mtc0 $15) write is ignored. (Release 6: ctc1 to FIR is a Reserved Instruction,
# tests/oracle/fp_ctc1_fir_ri.)
# MD00082 Vol I-A Rev 6.01 FIR description p.88 (read-only); MD00090 Vol III Rev 6.02 PRId p.221 (read-only).
# oracle: expect gpr:s1=0 gpr:s3=0
# oracle: unpredictable gpr:s0 MD00082 Vol I-A Rev 6.01 FIR: ProcessorID/Revision are implementation-defined; bit 29 (FREP) is an optional feature QEMU mips32r6-generic has (FIR 0x20f30000) and this profile (FIR 0x00f30000) does not
# oracle: unpredictable gpr:t7 same as s0
# oracle: unpredictable gpr:s2 MD00090 Vol III Rev 6.02 PRId: implementation-defined constant
# oracle: unpredictable gpr:t6 same as s2
.data
res: .space 80
.text
la $s7, res
cfc1 $s0, $0
li $t0, 0xffffffff
cfc1 $t7, $0
subu $s1, $t7, $s0
mfc0 $s2, $15
mtc0 $t0, $15
mfc0 $t6, $15
subu $s3, $t6, $s2
li $t9, 0x7fffffff
mtc1 $t9, $f2
cvt.d.w $f4, $f2
mfc1 $t1, $f4
mfhc1 $t2, $f4
sw $t1, 0($s7)
sw $t2, 4($s7)
li $t9, 0x80000000
mtc1 $t9, $f2
cvt.d.w $f4, $f2
mfc1 $t1, $f4
mfhc1 $t2, $f4
sw $t1, 8($s7)
sw $t2, 12($s7)
move $t0, $zero
move $t2, $zero
mtc1 $zero, $f0
mtc1 $zero, $f2
mtc1 $zero, $f4
mtc1 $zero, $f6
mtc1 $zero, $f8
mtc1 $zero, $f10
mtc1 $zero, $f12
mtc1 $zero, $f14
mtc1 $zero, $f16
mtc1 $zero, $f18
mtc1 $zero, $f20
mtc1 $zero, $f22
mtc1 $zero, $f24
mtc1 $zero, $f26
mtc1 $zero, $f28
mtc1 $zero, $f30
mthc1 $zero, $f0
mthc1 $zero, $f2
mthc1 $zero, $f4
mthc1 $zero, $f6
mthc1 $zero, $f8
mthc1 $zero, $f10
mthc1 $zero, $f12
mthc1 $zero, $f14
mthc1 $zero, $f16
mthc1 $zero, $f18
mthc1 $zero, $f20
mthc1 $zero, $f22
mthc1 $zero, $f24
mthc1 $zero, $f26
mthc1 $zero, $f28
mthc1 $zero, $f30
li $v0, 10
syscall
