# SC with no preceding LL: UNPREDICTABLE (it may fail or succeed). Only "no exception" is checked.
# MD00086 Vol II-A Rev 6.06: SC p.348 ("Execution of SC must have been preceded by execution of an LL instruction").
# oracle: unpredictable gpr:s1 MD00086 SC p.348: SC without LL is UNPREDICTABLE (rt)
# oracle: unpredictable mem:0x10010000 MD00086 SC p.348: SC without LL is UNPREDICTABLE (memory)
.data
w: .word 5
.text
la $t0, w
li $s1, 0x99
sc $s1, 0($t0)
li $s0, 1
li $v0, 10
syscall
