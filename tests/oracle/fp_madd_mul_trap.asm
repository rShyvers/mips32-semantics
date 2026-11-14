# madd.s with FCSR.Enables.O set (0x200): the multiply step (max*2) overflows, so the instruction traps at the
# multiply with the multiply's Cause only ("as if separate floating-point multiply and add instructions were
# executed", MD00086 Vol II-A Rev 6.06, MADD.fmt p.256; "a trap occurs before the instruction that causes the trap ...
# can complete and write its results", MD00082 Vol I-A Rev 6.01 §6.7.1 p.99). The add (+inf + -inf, Invalid) never
# runs, so Cause.V stays 0 and $f8 is not written. Floating Point exception, ExcCode 15 (Cause 0x3c).
# FCSR at the trap: Cause O (0x4000) | Enables O (0x200) = 0x4200. QEMU computes the whole multiply-add first and traps
# with Cause V|O|I (0x15200): declared deviation.
# oracle: expect cause=0x3c epc=0x00400038
# oracle: expect fcsr=0x00004200
# oracle: expect-deviation fcsr MD00086 Rev 6.06 MADD.fmt p.256: "as if separate floating-point multiply and add instructions were executed": the multiply traps (Overflow enabled) before the add runs, Cause = O only (MD00082 Rev 6.01 6.7.1 p.99); QEMU reports the add's Invalid too
li $t9, 0x7f7fffff
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f4
li $t9, 0xff800000
mtc1 $t9, $f6
li $t9, 0x12345678
mtc1 $t9, $f8
li $t8, 0x200
ctc1 $t8, $31
madd.s $f8, $f6, $f2, $f4
li $s0, 99
