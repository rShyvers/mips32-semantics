# Cause.DC (bit 27, Disable Count) is R/W in Release 2: a written 1 reads back as 1.
# MD00090 Vol III Rev 6.02 sec 9.36 Cause register (DC: R/W, Required (Release 2)); MTC0 p.290-291 (MD00086 6.06).
# (formerly a known model gap; the model now implements Cause.DC.)
# oracle: expect gpr:s0=0x08000000
lui $t0, 0x0800
mtc0 $t0, $13
mfc0 $s0, $13
mtc0 $zero, $13
li $v0, 10
syscall
