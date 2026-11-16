# Memory word order of ldc1/sdc1 in little-endian: 1.0 = 0x3ff00000_00000000 is stored low word first (the word at the lower
# address is bits 31..0). mfc1 reads the low word of the 64-bit FPR, mfhc1 the high word (the same with Status.FR = 0, where the
# high word is the odd register of the pair, and FR = 1).
# MD00086 Vol II-A Rev 6.06: LDC1 p.215, SDC1 p.362, MFC1 p.267, MFHC1 p.271, MTHC1 p.295.
# oracle: expect gpr:s0=0x3ff00000 gpr:s1=0 gpr:s2=0 gpr:s3=0x3ff00000
.data
.align 3
one: .double 1.0
out: .space 8
.text
la $t0, one
ldc1 $f0, 0($t0)
mfhc1 $s0, $f0
mfc1 $s1, $f0
la $t1, out
sdc1 $f0, 0($t1)
lw $s2, 0($t1)
lw $s3, 4($t1)
mthc1 $zero, $f0           # the final FPR dump of an FR = 1 FPU holds only low words
li $v0, 10
syscall
