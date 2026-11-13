# bc1fl/bc1tl, taken and not taken, cc 0 and non-zero: the delay slot executes only when the branch is taken (likely form).
# cc0 = 1, cc3 = 0, cc5 = 1. Each case adds 1 to $sN in the delay slot and 100 in the skipped fall-through instruction.
# MD00086 Vol II-A Rev 6.06: BC1FL p.58, BC1TL p.62 (branch likely: 'the delay slot instruction is annulled when not taken').
# oracle: expect gpr:s0=1 gpr:s1=100 gpr:s2=1 gpr:s3=100 gpr:s4=1 gpr:s5=100 gpr:s6=1 gpr:s7=100
.data
res: .space 64
.text
li $t9, 0x3f800000
mtc1 $t9, $f0
li $t9, 0x40000000
mtc1 $t9, $f4
c.lt.s $fcc0, $f0, $f4
c.eq.s $fcc3, $f0, $f4
c.lt.s $fcc5, $f0, $f4
li $s0, 0
li $s1, 0
li $s2, 0
li $s3, 0
li $s4, 0
li $s5, 0
li $s6, 0
li $s7, 0
bc1tl $fcc0, L1
addiu $s0, $s0, 1
addiu $s0, $s0, 100
L1: nop
bc1fl $fcc0, L2
addiu $s1, $s1, 1
addiu $s1, $s1, 100
L2: nop
bc1fl $fcc3, L3
addiu $s2, $s2, 1
addiu $s2, $s2, 100
L3: nop
bc1tl $fcc3, L4
addiu $s3, $s3, 1
addiu $s3, $s3, 100
L4: nop
bc1tl $fcc5, L5
addiu $s4, $s4, 1
addiu $s4, $s4, 100
L5: nop
bc1fl $fcc5, L6
addiu $s5, $s5, 1
addiu $s5, $s5, 100
L6: nop
bc1tl L7
addiu $s6, $s6, 1
addiu $s6, $s6, 100
L7: nop
bc1fl L8
addiu $s7, $s7, 1
addiu $s7, $s7, 100
L8: nop
li $v0, 10
syscall
