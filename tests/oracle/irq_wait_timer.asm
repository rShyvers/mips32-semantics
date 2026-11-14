# WAIT stops the processor until an interrupt: with the timer set (Compare = Count + 3000), IM7 = IE = 1, `wait` enters standby; the
# timer interrupt restarts it and is taken "between the WAIT instruction and the following instruction (EPC for the interrupt points at
# the instruction following the WAIT instruction)"; after eret execution continues there. The instruction after `wait` runs once.
# MD00086 Vol II-A Rev 6.06 WAIT p.442-443; MD00090 Vol III Rev 6.02 sec 9.30 p.187, Table 6.2 p.73, sec 6.2.26 p.102.
# Robust to host load (wave 9; the race irq_timer had, which a `wait` cannot poll for):
# - Compare is armed with IE = 0 and Count is read again: if Count is already at or past Compare (signed Count - Compare >= 0), the
#   match "When the value of the Count register equals the value of the Compare register" (sec 9.30 p.187) was missed and would
#   happen only after Count wraps, so Compare is re-armed. Once the check passes the match is still ahead, and the timer request
#   (Cause.TI) it raises stays pending until Compare is written.
# - If the request arrives after IE = 1 but before the `wait` (QEMU descheduled there), the interrupt is taken before the `wait`
#   (EPC is not `after`). The handler then records nothing, re-arms Compare with the same check (EXL = 1, no interrupt), and returns;
#   the `wait` that follows is woken by the next match.
# In the model Count advances one per instruction: the check passes the first time and the interrupt is taken from the `wait`, so
# neither fallback runs and the observed registers are as before.
# oracle: bare
# oracle: expect gpr:s0=0 gpr:s2=0 gpr:s4=1 gpr:s5=1
# oracle: max-steps 200000
.ktext
mfc0 $k0, $14
subu $k0, $k0, $t0
bnez $k0, early
nop
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
# interrupt taken before the WAIT: re-arm Compare in the future, return to reach the WAIT
early:
mfc0 $k1, $9
addiu $k1, $k1, 3000
mtc0 $k1, $11
mfc0 $k0, $9
subu $k0, $k0, $k1
bgez $k0, early
nop
li $k0, 0
li $k1, 0
eret
.text
la $t0, after
# Compare = Count + 3000 with IE = 0; re-arm while Count is already at or past Compare
arm:
mfc0 $t1, $9
addiu $t1, $t1, 3000
mtc0 $t1, $11
mfc0 $t2, $9
subu $t2, $t2, $t1
bgez $t2, arm
nop
li $t1, 0x20008001
mtc0 $t1, $12
ehb
wait
after: addiu $s5, $s5, 1
lui $t1, 0x2000
mtc0 $t1, $12
li $t0, 0
li $t1, 0
li $t2, 0
