# abs.s/neg.s of a NaN: with FIR.Has2008 = 0 these are ARITHMETIC operations and "any NaN operand signals invalid
# operation" (MD00086 Vol II-A Rev 6.06: ABS.fmt p.32, NEG.fmt p.307), so Invalid is raised (FCSR.Cause.V and the flag are
# set) for a quiet NaN too. The model (Semantics/FpOps.lean f32Abs/f32Neg, SPEC-NOTES 9.21) returns a QUIET NaN operand
# unchanged (sign bit NOT cleared/flipped: "one of the operand QNaN values", MD00082 Vol I-A Rev 6.01 6.3.1.5 p.82) and
# gives the default QNaN 0x7fbfffff only for a signaling NaN operand.
# The operand 0x7fa00000 is a QUIET NaN, not a signaling one: with FIR.Has2008 = 0 the fraction MSB b1 (bit 22) is 0 for a
# QNaN and 1 for an SNaN (MD00082 Vol I-A Rev 6.01 Table 6.2, p.80); here b1 = 0 (the fraction is 0x200000).
# Here: abs.s of the QNaN 0x7fa00000: Invalid raised => FCSR = Cause.V(0x10000) | Flags.V(0x40) = 0x00010040; the
# result in $f2 is 0x7fa00000 (unchanged). QEMU does not signal Invalid for abs/neg (FCSR stays 0): declared deviation, the
# manual wins.# oracle: expect gpr:s0=0x00010040
# oracle: expect-deviation gpr:s0 MD00086 Rev 6.06 ABS.fmt p.32 / NEG.fmt p.307: with Has2008=0 abs/neg are arithmetic and signal Invalid on any NaN operand (here a QNaN, Vol I Table 6.2 p.80); QEMU leaves FCSR at 0
li $t9, 0x7fa00000
mtc1 $t9, $f0
ctc1 $zero, $31
abs.s $f2, $f0
cfc1 $s0, $31
ctc1 $zero, $31
li $v0, 10
syscall
