# ERET between LL and SC makes the SC fail: rt <- 0, memory unchanged.
# MD00086 Vol II-A Rev 6.06: SC p.347 ("If either of the following events occurs between the execution of LL
# and SC, the SC fails: ... An ERET instruction is executed"), ERET p.177-178.
# oracle: expect gpr:s1=0 mem:0x10010000=0x00000005
.ktext
mfc0 $k1, $14
addiu $k1, $k1, 4
mtc0 $k1, $14
eret
.data
w: .word 5
.text
la $t0, w
ll $s0, 0($t0)
break                    # handler skips it and erets
li $s1, 0x99
sc $s1, 0($t0)
nop
