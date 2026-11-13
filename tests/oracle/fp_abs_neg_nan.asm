# abs.s/neg.s of a NaN: with FIR.Has2008 = 0 these are ARITHMETIC operations (a signaling NaN operand raises
# Invalid, FCSR.Cause.V and the flag are set; the result is the default NaN); QNaN operands copy the NaN with the
# sign cleared/flipped. MD00086 Vol II-A Rev 6.06: ABS.fmt p.32, NEG.fmt p.307.
# Here: sNaN (0x7fa00000) -> abs.s: Invalid raised => FCSR = Cause.V(0x10000) | Flags.V(0x40) = 0x00010040,
# result 0x7fbfffff.  QEMU does not signal Invalid for abs/neg (FCSR stays 0): declared deviation, the manual wins.
# oracle: expect gpr:s0=0x00010040
# oracle: expect-deviation gpr:s0 MD00086 Rev 6.06 ABS.fmt p.32 / NEG.fmt p.307: with Has2008=0 abs/neg are arithmetic and signal Invalid on an sNaN; QEMU leaves FCSR at 0
li $t9, 0x7fa00000
mtc1 $t9, $f0
ctc1 $zero, $31
abs.s $f2, $f0
cfc1 $s0, $31
ctc1 $zero, $31
li $v0, 10
syscall
