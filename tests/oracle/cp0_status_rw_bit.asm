# Release 6 Status bit 28 (RW) is a plain read/write bit in Kernel Mode: it reads back what was written, with no other effect.
# MD00090 Vol III Rev 6.02 sec 9.32 Figure 9.33 p.189 (Release 6 Status format: bits 31..29 CU3..CU1, bit 28 RW) and Table 9.47 p.190 (an image
# page; read in the PDF: RW "Read/write field. This bit can be written by software without side-effects"); MD00086 Vol II-A Rev 6.06 MFC0 p.266,
# MTC0 p.290. s0 = Status & 0x10000000 after setting it, s1 after clearing it, s2 after setting it again (kept at the end: the oracle also
# compares the final Status, bit 28 included). Only bit 28 is extracted from each read (Status.FR, bit 26, reads 1 in Release 6 and is not part of the check).
# oracle: expect gpr:s0=0x10000000 gpr:s1=0 gpr:s2=0x10000000
.text
lui $t1, 0x1000
mfc0 $t0, $12
or $t0, $t0, $t1
mtc0 $t0, $12
mfc0 $s0, $12
and $s0, $s0, $t1
nor $t2, $t1, $zero
and $t0, $t0, $t2
mtc0 $t0, $12
mfc0 $s1, $12
and $s1, $s1, $t1
or $t0, $t0, $t1
mtc0 $t0, $12
mfc0 $s2, $12
and $s2, $s2, $t1
li $t0, 0
li $t1, 0
li $t2, 0
li $v0, 10
syscall
