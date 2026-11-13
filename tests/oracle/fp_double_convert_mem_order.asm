# Register-pair / memory word order of ldc1/sdc1/mtc1/mfc1 in big-endian: 1.0 = 0x3ff00000 00000000 is stored
# high word first; $f0 holds the LOW word, $f1 the HIGH word for a double in $f0 (FR=0).
# MD00086 Vol II-A Rev 6.06: LDC1 p.215, SDC1 p.362, MTC1 p.292, MFC1 p.267; Vol I Rev 6.01 FPR organisation
# (mipsdoc.py search "FPRs 32-bit FR=0 even odd register pair double").
# oracle: expect fpr:f0=0x00000000 fpr:f1=0x3ff00000 gpr:s0=0x3ff00000 gpr:s1=0
.data
.align 3
one: .word 0x3ff00000, 0x00000000
out: .space 8
.text
la $t0, one
ldc1 $f0, 0($t0)
mfc1 $s0, $f1
mfc1 $s1, $f0
la $t1, out
sdc1 $f0, 0($t1)
lw $s2, 0($t1)
lw $s3, 4($t1)
li $v0, 10
syscall
