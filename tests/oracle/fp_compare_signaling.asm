# The signaling-predicate family c.lt/c.le/c.eq... as in the model tables: a<b only (ordinary values), both orders,
# then bc1t with delay slot. MD00086 Vol II-A Rev 6.06: C.cond.fmt p.110-113 (lt = cond 1100, le = 1110, eq = 0010).
# oracle: expect gpr:s0=1 gpr:s1=0 gpr:s2=1 gpr:s3=1 gpr:s4=0 gpr:s5=1
li $t9, 0x3f800000
mtc1 $t9, $f0
li $t9, 0x40000000
mtc1 $t9, $f1
li $s0, 0
li $s1, 0
li $s2, 0
li $s3, 0
li $s4, 0
li $s5, 0
c.lt.s $f0, $f1
bc1t t1
nop
b d1
nop
t1: li $s0, 1
d1: c.lt.s $f1, $f0
bc1t t2
nop
b d2
nop
t2: li $s1, 1
d2: c.le.s $f0, $f0
bc1t t3
li $s2, 1                  # delay slot executes either way
li $s2, 5                  # skipped (taken)
t3: c.eq.s $f0, $f1
bc1f t4
li $s3, 1
li $s3, 7                  # skipped (taken)
t4: c.le.s $f1, $f0
bc1t t5
li $s4, 0
b d5
li $s5, 1
t5: li $s4, 1
d5: nop
li $v0, 10
syscall
