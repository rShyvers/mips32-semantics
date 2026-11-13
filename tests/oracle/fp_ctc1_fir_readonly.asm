# ctc1 to FIR ($0) is ignored (FIR is read-only); cfc1 FIR before/after; cvt.d.w exact; PRId (mtc0 $15) write is ignored.
# MD00082 Vol I-A Rev 6.01 FIR description p.88 (read-only); MD00090 Vol III Rev 6.02 PRId p.221 (read-only).
# oracle: expect gpr:s1=0 gpr:s3=0
# oracle: unpredictable gpr:s0 MD00082 Vol I-A Rev 6.01 FIR: ProcessorID/Revision and the F64 capability bit are implementation-defined (QEMU 24Kf: F64=1, the model: a 32-bit FPU)
# oracle: unpredictable gpr:t7 same as s0
# oracle: unpredictable gpr:s2 MD00090 Vol III Rev 6.02 PRId: implementation-defined constant
# oracle: unpredictable gpr:t6 same as s2
.data
res: .space 80
.text
la $s7, res
cfc1 $s0, $0
li $t0, 0xffffffff
ctc1 $t0, $0
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
mfc1 $t2, $f5
sw $t1, 0($s7)
sw $t2, 4($s7)
li $t9, 0x80000000
mtc1 $t9, $f2
cvt.d.w $f4, $f2
mfc1 $t1, $f4
mfc1 $t2, $f5
sw $t1, 8($s7)
sw $t2, 12($s7)
li $v0, 10
syscall
