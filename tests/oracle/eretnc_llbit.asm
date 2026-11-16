# ERETNC does not clear the LLbit, ERET does: ll; break (the handler returns with eretnc); sc succeeds (rt = 1, memory written);
# then ll; break (the handler returns with eret); sc fails (rt = 0, memory unchanged).
# MD00086 Vol II-A Rev 6.06 ERETNC p.179-180 ("ERETNC is identical to ERET except that an ERETNC will not clear the LLbit that is set by
# execution of an LL instruction, and thus when placed between an LL and SC sequence, will never cause the SC to fail"); SC p.347 ("If either of
# the following events occurs between the execution of LL and SC, the SC fails: ... An ERET instruction is executed. (Release 5 includes ERETNC,
# which will not cause the SC to fail.)"); ERET p.177-178.
# SC p.348 also lets the SC fail ("success is not predictable") when "The instructions executed starting with the LL and ending with the SC do not
# lie in a 2048-byte contiguous region of virtual memory" and on a load or store to another block: so the LL/SC sequences run in kseg0 right
# after the handler (all within 0x80000180..+0x80), reached by jr from .text, and the handler does no load or store.
# The handler skips the break and returns with eretnc while s7 = 1, with eret while s7 = 0; it counts entries in s4.
# oracle: expect gpr:s1=1 gpr:s3=0 gpr:s4=2 mem:0x10010000=0x00000099
.data
w: .word 5
.ktext
mfc0 $k1, $14
addiu $k1, $k1, 4
mtc0 $k1, $14
addiu $s4, $s4, 1
beqz $s7, use_eret
nop
eretnc
use_eret:
eret
kcode:
ll $s0, 0($t0)
break
li $s1, 0x99
sc $s1, 0($t0)
li $s7, 0
ll $s2, 0($t0)
break
li $s3, 0x77
sc $s3, 0($t0)
la $t9, done
jr $t9
nop
.text
li $s4, 0
la $t0, w
li $s7, 1
la $t9, kcode
jr $t9
nop
done:
li $t9, 0
