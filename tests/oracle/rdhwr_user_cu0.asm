# RDHWR in User Mode with Status.CU0 = 1: Coprocessor 0 is enabled, so every implemented hardware register is readable although HWREna = 0.
# MD00086 Vol II-A Rev 6.06 RDHWR p.333 ("Access to the specified hardware register is enabled if Coprocessor 0 is enabled, or if the corresponding
# bit is set in the HWREna register"); MD00090 Vol III Rev 6.02 sec 3.5.3 p.23 (Coprocessor 0 is enabled when "The CU0 bit in the Status register
# is 1"), Table 9.39 p.175 (HWREna reset/zero). SYNCI_Step and CCRes are implementation-dependent (rdhwr_kernel), so their raw values are not
# compared: the check is that no exception happens (s6 = 0).
# oracle: expect gpr:s0=0 gpr:s2=777 gpr:s6=0
# oracle: unpredictable gpr:s1 MD00090 Vol III Rev 6.02 Table 9.40 p.176: SYNCI_Step is implementation-dependent (QEMU 24Kf: 32; model: 0)
# oracle: unpredictable gpr:s3 MD00090 Vol III Rev 6.02 Table 9.40 p.176: CCRes is implementation-dependent (QEMU 24Kf: 2; model: 1)
.ktext
addiu $s6, $s6, 1
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
eret
.text
li $s6, 0
lui $t0, 0x0800
mtc0 $t0, $13
li $t1, 777
mtc0 $t1, $9
mtc0 $zero, $7
la $t0, user
mtc0 $t0, $14
lui $t1, 0x3000
ori $t1, $t1, 0x12
mtc0 $t1, $12
li $t0, 0
li $t1, 0
eret
user:
rdhwr $s0, $0
rdhwr $s1, $1
rdhwr $s2, $2
rdhwr $s3, $3
