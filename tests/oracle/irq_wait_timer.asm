# WAIT stops the processor until an interrupt: with the timer set (Compare = Count + 3000), IM7 = IE = 1, `wait` enters standby; the
# timer interrupt restarts it and is taken "between the WAIT instruction and the following instruction (EPC for the interrupt points at
# the instruction following the WAIT instruction)"; after eret execution continues there. The instruction after `wait` runs once.
# MD00086 Vol II-A Rev 6.06 WAIT p.442-443; MD00090 Vol III Rev 6.02 sec 9.30 p.187, Table 6.2 p.73, sec 6.2.26 p.102.
# oracle: bare
# oracle: expect gpr:s0=0 gpr:s2=0 gpr:s4=1 gpr:s5=1
# oracle: max-steps 200000
.ktext
mfc0 $k0, $13
andi $s0, $k0, 0x7c
mfc0 $s2, $14
subu $s2, $s2, $t0
mfc0 $k1, $9
lui $k0, 0x4000
addu $k1, $k1, $k0
mtc0 $k1, $11
addiu $s4, $s4, 1
li $k0, 0
li $k1, 0
eret
.text
la $t0, after
mfc0 $t1, $9
addiu $t1, $t1, 3000
mtc0 $t1, $11
li $t1, 0x20008001
mtc0 $t1, $12
ehb
wait
after: addiu $s5, $s5, 1
lui $t1, 0x2000
mtc0 $t1, $12
li $t0, 0
li $t1, 0
