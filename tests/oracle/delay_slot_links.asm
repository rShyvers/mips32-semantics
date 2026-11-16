# jal/jalr/bal/nal link registers and jr; the link is PC+8 (after the delay slot).
# MD00086 Vol II-A Rev 6.06: JAL p.195, JALR p.196-197, JR p.206-207, BAL p.50, NAL p.306 ("NAL is considered
# to be a not-taken branch, with a delay slot"; GPR[31] <- PC+8).
# Layout: text at 0x00400000; instructions are numbered so the expected links are checkable.
la $t9, f1
jalr $t9                # link in $ra = address of the instruction after the delay slot
nop
move $s0, $ra           # (reached after f1 returns; ra here is f1's return = clobbered by jal below)
jal f2
nop
move $s1, $ra
la $t8, f3
jalr $s7, $t8           # explicit link register
nop
bal f4                  # taken: links ra
nop
move $s2, $ra
li $t0, 1
nal                     # not taken: ra := PC + 8
nop
move $s3, $ra
li $v0, 10
syscall
f1: jr $ra
nop
f2: jr $ra
nop
f3: jr $s7
nop
f4: jr $ra
nop
