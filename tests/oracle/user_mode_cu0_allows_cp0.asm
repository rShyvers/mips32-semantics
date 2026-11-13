# User Mode with Status.CU0 = 1: coprocessor 0 is usable ("Access to Coprocessor 0 registers are enabled under any of the following conditions: ... The CU0 bit in the Status register is 1").
# mfc0 reads Status (UM = 1, CU0 = 1, EXL = 0) and Cause; mtc0 writes EPC and reads it back; no exception is taken (the handler would count it in s4).
# MD00090 Vol III Rev 6.02 sec 3.5.3 p.23; Table 9.47 p.190 (CU0 R/W); MD00086 Vol II-A Rev 6.06 MFC0 p.266, MTC0 p.290-291.
# oracle: expect gpr:s4=0 gpr:s0=0x30000010 gpr:s2=0x00400abc
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
