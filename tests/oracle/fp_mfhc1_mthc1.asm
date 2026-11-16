# mfhc1/mthc1 on even registers: mthc1 writes the high word of the 64-bit FPR[fs] and leaves the low word, mfhc1 reads it back
# (the same with Status.FR = 0, where the high word is the odd register of the pair, and FR = 1). The high words are cleared before exit
# (the final FPR dump holds only the low word of each 64-bit FPR on an FR = 1 FPU).
# MD00086 Vol II-A Rev 6.06: MFHC1 p.271 ('GPR[rt] <- FPR[fs]63..32'), MTHC1 p.295.
# oracle: expect gpr:s0=0xaabbccdd gpr:s1=0x11223344 gpr:s3=0x01020304 gpr:s4=0x11223344
.data
res: .space 64
.text
la $s7, res
li $t0, 0x11223344
li $t1, 0xaabbccdd
mtc1 $t0, $f2
mthc1 $t1, $f2
mfhc1 $s0, $f2
mfc1 $s1, $f2
li $t2, 0x01020304
mtc1 $t0, $f4
mthc1 $t2, $f4
mfhc1 $s3, $f4
mfc1 $s4, $f4
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
