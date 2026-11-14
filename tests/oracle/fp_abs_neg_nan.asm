# abs.s/neg.s of a quiet NaN. With FIR.Has2008 = 0 these are ARITHMETIC operations and "any NaN operand signals invalid
# operation" (MD00086 Vol II-A Rev 6.06: ABS.fmt p.32, NEG.fmt p.307); NEG also says "The value is negated by changing
# the sign bit value" (p.307). The model takes reading A' (SPEC-NOTES 9.21, Manual Oracle.absNegNaN): Invalid is raised
# (FCSR.Cause.V 0x10000 and Flags.V 0x40) and, untrapped, the result is the operand with the sign bit cleared (abs) or
# flipped (neg).
# The operands 0xffa00000 / 0x7fa00000 are QUIET NaNs: with FIR.Has2008 = 0 the fraction MSB (bit 22) is 0 for a QNaN
# (MD00082 Vol I-A Rev 6.01 Table 6.2, p.80).
# abs.s 0xffa00000 -> $s1 = 0x7fa00000, FCSR $s0 = 0x00010040; neg.s 0x7fa00000 -> $s3 = 0xffa00000, FCSR $s2 = 0x00010040.
# QEMU changes the sign bit (same result values) but does not signal Invalid (FCSR stays 0): declared deviation on the
# FCSR values, the manual wins.
# oracle: expect gpr:s0=0x00010040
# oracle: expect gpr:s1=0x7fa00000
# oracle: expect gpr:s2=0x00010040
# oracle: expect gpr:s3=0xffa00000
# oracle: expect-deviation gpr:s0 MD00086 Rev 6.06 ABS.fmt p.32: with Has2008=0 abs is arithmetic and "any NaN operand signals invalid operation" (a QNaN here, Vol I-A Table 6.2 p.80); QEMU leaves FCSR at 0
# oracle: expect-deviation gpr:s2 MD00086 Rev 6.06 NEG.fmt p.307: with Has2008=0 neg is arithmetic and "any NaN operand signals invalid operation" (a QNaN here, Vol I-A Table 6.2 p.80); QEMU leaves FCSR at 0
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
