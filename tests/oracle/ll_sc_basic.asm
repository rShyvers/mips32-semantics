# ll/sc: success writes 1 to rt and stores; a following sc without a new ll is UNPREDICTABLE per the manual
# only if no LL preceded -- here the second sc follows a successful sc (LLbit cleared by sc): see ll_sc_second_fails.
# MD00086 Vol II-A Rev 6.06: LL p.223-224, SC p.347-350.
# oracle: expect gpr:s1=1 mem:0x10010000=0x00000099 gpr:s0=0x00000005
.data
w: .word 5
.text
la $t0, w
ll $s0, 0($t0)
li $s1, 0x99
sc $s1, 0($t0)
li $v0, 10
syscall
