# The multiply-add family executes "as if separate floating-point multiply and add [and negate] instructions were
# executed" (MD00086 Vol II-A Rev 6.06, MADD.fmt p.256, NMADD.fmt p.308): each operation writes FCSR.Cause and is
# checked for a trap on its own; the Flags of the completed operations accumulate.
# (1) madd.s with no enables: the product max*2 overflows to +inf (Overflow, Inexact), then +inf + -inf is Invalid
#     (default QNaN 0x7fbfffff). Cause after the instruction is the add's: V (0x10000); Flags V|O|I (0x54).
#     $s0 = 0x7fbfffff, $s1 = 0x00010054.
# (2) nmadd.s with fr = QNaN A (0x7f800001) and fs = QNaN B (0x7f800002), ft = 1.0: the printed Operation is
#     -(vfr + (vfs x vft)) (p.308, read from the PDF): the product is B, the add's first QNaN operand is fr = A
#     (SPEC-NOTES 9.13), and the negate (arithmetic NEG.fmt, reading A' of SPEC-NOTES 9.21) flips the sign and signals
#     Invalid: $s2 = 0xff800001, $s3 = 0x00010040.
# (3) madd.s with the same operands: (vfs x vft) + vfr, product first: $s4 = 0x7f800002, FCSR $s5 = 0 (QNaN operands
#     signal nothing).
# oracle: expect gpr:s0=0x7fbfffff
# oracle: expect gpr:s1=0x00010054
# oracle: expect gpr:s2=0xff800001
# oracle: expect gpr:s3=0x00010040
# oracle: expect gpr:s4=0x7f800002
# oracle: expect gpr:s5=0x00000000
# QEMU differs (declared): it ORs the Cause bits of the steps (V|O|I), returns the default QNaN for any NaN operand of
# the multiply-add family instead of an operand QNaN, and does not signal Invalid in the negate step.
# oracle: expect-deviation gpr:s1 MD00086 Rev 6.06 MADD.fmt p.256: results and flags "as if separate floating-point multiply and add instructions were executed", so Cause is the last (add) operation's (V); QEMU ORs the multiply's O|I into Cause
# oracle: expect-deviation gpr:s2 MD00082 Rev 6.01 6.3.1.5 p.82: "When possible, this QNaN result is one of the operand QNaN values" (fr = 0x7f800001, then NEG.fmt p.307 changes the sign); QEMU returns the default QNaN
# oracle: expect-deviation fpr:f8 MD00082 Rev 6.01 6.3.1.5 p.82: an operand QNaN is returned when possible (as gpr:s2); QEMU returns the default QNaN
# oracle: expect-deviation gpr:s3 MD00086 Rev 6.06 NMADD.fmt p.308 "as if separate ... negate instructions were executed" and NEG.fmt p.307 "any NaN operand signals invalid operation" (Has2008=0); QEMU leaves FCSR at 0
# oracle: expect-deviation gpr:s4 MD00082 Rev 6.01 6.3.1.5 p.82: an operand QNaN is returned when possible (the product of vfs = 0x7f800002, MADD.fmt p.256 order); QEMU returns the default QNaN
# oracle: expect-deviation fpr:f10 MD00082 Rev 6.01 6.3.1.5 p.82: an operand QNaN is returned when possible (as gpr:s4); QEMU returns the default QNaN
li $t9, 0x7f7fffff
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
li $t9, 0xff800000
mtc1 $t9, $f6
ctc1 $zero, $31
madd.s $f8, $f6, $f2, $f4
mfc1 $s0, $f8
cfc1 $s1, $31
li $t9, 0x7f800001
mtc1 $t9, $f6
li $t9, 0x7f800002
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
ctc1 $zero, $31
nmadd.s $f8, $f6, $f2, $f4
mfc1 $s2, $f8
cfc1 $s3, $31
ctc1 $zero, $31
madd.s $f10, $f6, $f2, $f4
mfc1 $s4, $f10
cfc1 $s5, $31
ctc1 $zero, $31
li $v0, 10
syscall
