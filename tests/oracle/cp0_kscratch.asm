# KScratch1..KScratch6 (CP0 register 31, selects 2..7) are read/write 32-bit scratch registers in Kernel Mode, independent of each other.
# MD00090 Vol III Rev 6.02 sec 9.70 p.311 ("Release 6 - Required"; Table 9.84: Data 31:0 R/W), sec 9.49 Table 9.68 p.255 (Config4.KScrExist: "For
# Release 6, bits 2-7 are always 1 because KScratch1-6 must be implemented"); MD00086 Vol II-A Rev 6.06 MFC0 p.266, MTC0 p.290.
# Each select is written with a distinct pattern, then all six are read back (s0..s5); s6 = Config4.KScrExist (bits 23..16) = 0xfc.
# oracle: expect gpr:s0=0x11111111 gpr:s1=0x22222222 gpr:s2=0x80000003 gpr:s3=0xfffffffc gpr:s4=0x00000000 gpr:s5=0x5a5aa5a5 gpr:s6=0xfc
.text
li $t0, 0x11111111
mtc0 $t0, $31, 2
li $t0, 0x22222222
mtc0 $t0, $31, 3
li $t0, 0x80000003
mtc0 $t0, $31, 4
li $t0, 0xfffffffc
mtc0 $t0, $31, 5
li $t0, 0x77777777
mtc0 $t0, $31, 6
mtc0 $zero, $31, 6
li $t0, 0x5a5aa5a5
mtc0 $t0, $31, 7
mfc0 $s0, $31, 2
mfc0 $s1, $31, 3
mfc0 $s2, $31, 4
mfc0 $s3, $31, 5
mfc0 $s4, $31, 6
mfc0 $s5, $31, 7
mfc0 $s6, $16, 4
srl $s6, $s6, 16
andi $s6, $s6, 0xff
li $t0, 0
li $v0, 10
syscall
