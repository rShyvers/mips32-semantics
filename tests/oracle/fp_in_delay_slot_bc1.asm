# bc1t/bc1f delay slot executes; branch-likely FP branches are not in the model's assembler.
# MD00086 Vol II-A Rev 6.06: BC1T p.60-61, BC1F p.56-57.
# oracle: expect gpr:s0=2 gpr:s1=3
li $t9, 0x3f800000
mtc1 $t9, $f0
li $s0, 0
li $s1, 0
c.eq.s $f0, $f0
bc1t x1
addiu $s0, $s0, 1
addiu $s1, $s1, 100        # skipped
x1: c.eq.s $f0, $f0
bc1f x2                    # not taken
addiu $s0, $s0, 1
addiu $s1, $s1, 3
x2: nop
li $v0, 10
syscall
