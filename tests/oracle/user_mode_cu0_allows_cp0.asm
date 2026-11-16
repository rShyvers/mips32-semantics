# User Mode with Status.CU0 = 1: coprocessor 0 is usable ("Access to Coprocessor 0 registers are enabled under any of the following conditions: ... The CU0 bit in the Status register is 1").
# mfc0 reads Status (UM = 1, CU0 = 1, EXL = 0) and Cause; mtc0 writes EPC and reads it back; no exception is taken (the handler would count it in s4).
# MD00090 Vol III Rev 6.02 sec 3.5.3 p.23; Table 9.47 p.190 (CU0 R/W); MD00086 Vol II-A Rev 6.06 MFC0 p.266, MTC0 p.290-291.
# Release 6: this premise no longer holds (bit 28 is RW, not CU0): QEMU takes Coprocessor Unusable for each mfc0/mtc0; the model still treats bit 28
# as CU0 (W2).
# oracle: known-model-bug gpr:s0 MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.190 (an image page; read in the PDF): in Release 6 the CU field is CU3..CU1 (bits 31..29) and bit 28 is "RW: Read/write field. This bit can be written by software without side-effects"; Coprocessor 0 is not enabled in User Mode by bit 28; W2: the model still enables Coprocessor 0 in User Mode through bit 28 (pre-Release 6 CU0)
# oracle: known-model-bug gpr:s2 MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.190 (an image page; read in the PDF): in Release 6 the CU field is CU3..CU1 (bits 31..29) and bit 28 is "RW: Read/write field. This bit can be written by software without side-effects"; Coprocessor 0 is not enabled in User Mode by bit 28; W2: the model still enables Coprocessor 0 in User Mode through bit 28 (pre-Release 6 CU0)
# oracle: known-model-bug gpr:s4 MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.190 (an image page; read in the PDF): in Release 6 the CU field is CU3..CU1 (bits 31..29) and bit 28 is "RW: Read/write field. This bit can be written by software without side-effects"; Coprocessor 0 is not enabled in User Mode by bit 28; W2: the model still enables Coprocessor 0 in User Mode through bit 28 (pre-Release 6 CU0)
# oracle: known-model-bug gpr:k0 MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.190 (an image page; read in the PDF): in Release 6 the CU field is CU3..CU1 (bits 31..29) and bit 28 is "RW: Read/write field. This bit can be written by software without side-effects"; Coprocessor 0 is not enabled in User Mode by bit 28; W2: the model still enables Coprocessor 0 in User Mode through bit 28 (pre-Release 6 CU0)
.ktext
addiu $s4, $s4, 1
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
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
