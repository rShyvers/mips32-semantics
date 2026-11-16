# abs.s/neg.s of a NaN operand (0xffa00000 / 0x7fa00000). Release 6 requires FCSR.ABS2008 = 1 (MD00082 Vol I-A Rev 6.01 FCSR
# Table 6.8 p.93): "If FCSRABS2008=1 then this operation is non-arithmetic" (MD00086 Vol II-A Rev 6.06 ABS.fmt p.32, NEG.fmt p.307),
# so the sign bit is cleared / flipped, no Invalid is signaled and FCSR is unchanged: Cause/Flags stay 0, so each FCSR read is the read-only
# NAN2008/ABS2008 bits only (0x000c0000). Note the operands 0xffa00000 / 0x7fa00000 are SIGNALING NaNs in the Release 6 encoding (fraction MSB 0):
# an arithmetic operation would raise Invalid on them, ABS/NEG do not. abs.s 0xffa00000 -> $s1 = 0x7fa00000; neg.s 0x7fa00000 -> $s3 = 0xffa00000.
# oracle: expect gpr:s1=0x7fa00000
# oracle: expect gpr:s3=0xffa00000
# oracle: expect gpr:s0=0x000c0000 gpr:s2=0x000c0000
li $t9, 0xffa00000
mtc1 $t9, $f0
ctc1 $zero, $31
abs.s $f2, $f0
cfc1 $s0, $31
mfc1 $s1, $f2
li $t9, 0x7fa00000
mtc1 $t9, $f0
ctc1 $zero, $31
neg.s $f4, $f0
cfc1 $s2, $31
mfc1 $s3, $f4
ctc1 $zero, $31
li $v0, 10
syscall
