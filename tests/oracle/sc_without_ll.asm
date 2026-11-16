# SC with no preceding LL: "The following conditions must be true or the result of the SC is not
# predictable—the SC may fail or succeed (if Config5LLB=1, then either success or failure is mandated,
# else the result is UNPREDICTABLE): Execution of SC must have been preceded by execution of an LL
# instruction" (MD00086 Vol II-A Rev 6.06, SC p.348). Release 6 has Config5LLB = 1 ("In Release 6,
# Config5LLB is read-only 1", MD00090 Vol III Rev 6.02 Table 9.69 p.264), so the SC either fails or
# succeeds (no exception, no other effect): which one is not compared; only "no exception" is checked.
# oracle: unpredictable gpr:s1 MD00086 Vol II-A Rev 6.06 SC p.348: SC not preceded by LL "may fail or succeed" (Config5LLB=1: one of the two is mandated, which one is not; MD00090 Vol III Rev 6.02 Table 9.69 p.264) (rt)
# oracle: unpredictable mem:0x10010000 MD00086 Vol II-A Rev 6.06 SC p.348: SC not preceded by LL "may fail or succeed" (Config5LLB=1: one of the two is mandated, which one is not; MD00090 Vol III Rev 6.02 Table 9.69 p.264) (memory)
.data
w: .word 5
.text
la $t0, w
li $s1, 0x99
sc $s1, 0($t0)
li $s0, 1
li $v0, 10
syscall
