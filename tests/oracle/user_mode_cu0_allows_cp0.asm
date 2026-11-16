# Release 6: Status bit 28 is RW, not CU0, so setting it does NOT make coprocessor 0 usable in User Mode.
# (The file name is historical: before Release 6 bit 28 was CU0 and this test checked that it enabled CP0.)
# MD00090 Vol III Rev 6.02 sec 9.32 Figure 9.33 p.189 (Release 6 Status: bits 31..29 CU3..CU1, bit 28 RW) and Table 9.47 p.190 (an image page;
# read in the PDF: RW is "Read/write field. This bit can be written by software without side-effects"). Sec 3.5.3 p.23 still lists "The CU0
# bit in the Status register is 1" as an enabling condition: pre-Release 6 wording that the Release 6 Status format overrides (no CU0 field).
# With Status = 0x30000012 (bits 29, 28, UM = 1, EXL = 1), eret enters User Mode; each mfc0/mtc0 there raises Coprocessor Unusable
# (MD00086 Vol II-A Rev 6.06 MFC0 p.266, MTC0 p.290-291: "Exceptions: Coprocessor Unusable"; ExcCode 11 = CpU, MD00090 Vol III Rev 6.02
# Table 9.53 p.212; CE = 0, the unit referenced, Table 9.52 p.209), the destination registers keep 0 and EPC is not written by the user mtc0.
# The handler counts exceptions in s4, keeps Cause & 0x3000007c (CE, ExcCode) in s5, skips the instruction.
# oracle: expect gpr:s0=0 gpr:s2=0 gpr:s4=3 gpr:s5=0x2c
.ktext
addiu $s4, $s4, 1
mfc0 $k0, $13
li $k1, 0x3000007c
and $s5, $k0, $k1
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
li $k1, 0
eret
.text
li $s4, 0
la $t0, user
mtc0 $t0, $14
lui $t1, 0x3000
ori $t1, $t1, 0x12
mtc0 $t1, $12
eret
user:
mfc0 $s0, $12
li $t2, 0x00400abc
mtc0 $t2, $14
mfc0 $s2, $14
