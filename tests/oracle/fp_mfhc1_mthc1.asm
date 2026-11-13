# mfhc1/mthc1 with Status.FR = 0 on an even register: the 64-bit view of FPR[fs] is the even/odd pair, so mfhc1 reads the odd register of
# the pair and mthc1 writes it. (An odd fs is UNPREDICTABLE with FR=0 and is not used.)
# MD00086 Vol II-A Rev 6.06: MFHC1 p.271 ('GPR[rt] <- FPR[fs]63..32 ... UNPREDICTABLE if Status.FR = 0 and fs is odd'), MTHC1 p.295.
# oracle: expect gpr:s0=0xaabbccdd gpr:s1=0x11223344 fpr:f5=0x01020304 fpr:f4=0x11223344
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
mfc1 $s2, $f3
li $t2, 0x01020304
mtc1 $t0, $f4
mthc1 $t2, $f4
mfhc1 $s3, $f4
li $v0, 10
syscall
