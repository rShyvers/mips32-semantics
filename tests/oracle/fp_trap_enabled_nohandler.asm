# Enabled Divide-by-zero: div.s 1/0 with FCSR.Enables.Z set takes the FP exception (ExcCode 15) at once; the destination keeps its
# old value, there is no handler so the run ends unhandled.
# MD00082 Vol I-A Rev 6.01 sec 6.7.1 p.98-99 (an enabled exception -> Floating Point exception, ExcCode 15, destination not written, Flags not updated, Cause set);
# MD00090 Vol III Rev 6.02 Cause ExcCode 15 = FPE.
# oracle: expect cause=0x3c
.data
res: .space 64
.text
la $s7, res
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x12345678
mtc1 $t9, $f6
li $t8, 0x400
ctc1 $t8, $31
div.s $f6, $f2, $f4
li $s0, 99
