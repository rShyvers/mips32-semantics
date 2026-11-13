# Count (CP0 9,0) and Compare (CP0 11,0) are Read/Write; Cause.DC = 1 stops Count; Count = Compare sets Cause.TI (bit 30) and, merged
# into hardware interrupt 5, Cause.IP7 (bit 15); a write to Compare clears TI. Interrupts stay disabled (Status.IE = 0), so nothing is taken.
# MD00090 Vol III Rev 6.02 sec 9.27 p.183 (Count R/W, "incrementing at a constant rate"), sec 9.30 p.187 (Compare: "When the value of the Count
# register equals the value of the Compare register, an interrupt request is made"; "Writing a value to the Compare register, as a side effect,
# clears the timer interrupt"), Table 9.52 p.209 (TI), p.210 (DC "Disable Count register"), p.211 (IP7..IP2); sec 6.1.1.1 Table 6.2 p.73 (HW5 =
# "Hardware Interrupt, Timer Interrupt, or Performance Counter Interrupt" -> CauseIP7); sec 9.33 Table 9.48 p.199 (IntCtl.IPTI; QEMU 24Kf reads 7).
# Count's rate is implementation-dependent (model: one per step; QEMU: virtual time), so only frozen values (DC = 1), flags and "it moved" are
# compared; Compare is set 100000 counts ahead so that the match cannot happen before the polling loop runs. Every register that held a
# running Count value is cleared before exit. On QEMU the TI and IP7 bits appear one after the other (IP7 through the interrupt line), so the
# program waits for each with a bounded loop.
# oracle: expect gpr:s0=1 gpr:s1=1 gpr:s2=0 gpr:s3=0 gpr:s4=1 gpr:s5=1234 gpr:s6=0x5000
# oracle: unpredictable cause MD00090 Vol III Rev 6.02 Table 9.52 p.211: IP7..IP2 report external hardware interrupts (the Malta board raises HW0 from its interrupt controller after some milliseconds; the model has no interrupt inputs); TI/IP7 are compared through s0..s2
# oracle: max-steps 400000
.text
# freeze Count (Cause.DC = 1)
lui $t0, 0x0800
mtc0 $t0, $13
# with DC = 1 a written Count reads back unchanged, and does not move
li $t1, 1234
mtc0 $t1, $9
mfc0 $s5, $9
mfc0 $t2, $9
nop
nop
nop
mfc0 $t3, $9
subu $s3, $t3, $t2
# Compare is Read/Write
li $t1, 0x5000
mtc0 $t1, $11
mfc0 $s6, $11
# let Count run; Compare = Count + 100000; poll Cause.TI
mtc0 $zero, $13
mfc0 $t1, $9
li $t0, 100000
addu $t1, $t1, $t0
mtc0 $t1, $11
li $t4, 50000000
poll:
mfc0 $t5, $13
srl $t6, $t5, 30
andi $t6, $t6, 1
bnez $t6, got
nop
addiu $t4, $t4, -1
bnez $t4, poll
nop
got:
move $s0, $t6
# the timer request merged into IP7
li $t4, 50000000
poll7:
mfc0 $t5, $13
srl $t6, $t5, 15
andi $t6, $t6, 1
bnez $t6, got7
nop
addiu $t4, $t4, -1
bnez $t4, poll7
nop
got7:
move $s1, $t6
# write Compare far ahead (2^30 counts): TI and IP7 cleared
mfc0 $t1, $9
lui $t0, 0x4000
addu $t1, $t1, $t0
mtc0 $t1, $11
mfc0 $t5, $13
srl $s2, $t5, 30
andi $s2, $s2, 1
srl $t7, $t5, 15
andi $t7, $t7, 1
or $s2, $s2, $t7
# with DC = 0 Count moves: poll until two reads differ
mfc0 $t2, $9
li $t4, 50000000
run:
mfc0 $t3, $9
bne $t3, $t2, moved
nop
addiu $t4, $t4, -1
bnez $t4, run
nop
moved:
sltu $s4, $zero, $t4
# freeze Count for a deterministic end state, clear every register that held a Count-dependent value
lui $t0, 0x0800
mtc0 $t0, $13
li $t0, 0
li $t1, 0
li $t2, 0
li $t3, 0
li $t4, 0
li $t5, 0
li $t6, 0
li $t7, 0
li $v0, 10
syscall
