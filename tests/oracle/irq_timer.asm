# Timer interrupt delivery: Count = Compare raises the timer request (Cause.TI), merged into IP7 (IntCtl.IPTI = 7); with Status.IM7 = 1
# and IE = 1 the Interrupt exception is taken (ExcCode 0) and the handler sees TI = IP7 = 1; writing Compare clears TI. The program first
# reads IntCtl (expected 0xE0000000: IPTI = 7, IPPCI = IPFDC = VS = 0) and SRSCtl (expected 0: HSS = 0, only the normal GPRs).
# MD00090 Vol III Rev 6.02 sec 9.30 p.187 (Compare match: "an interrupt request is made"; "Writing a value to the Compare register, as
# a side effect, clears the timer interrupt"), Table 6.2 p.73 (HW5: Timer -> CauseIP7 and StatusIM7), sec 9.33 Table 9.48 p.199-201
# (IntCtl), sec 9.34 Table 9.49 p.203-204 (SRSCtl), sec 6.2.26 p.102.
# Count's rate differs (model: one per step; QEMU: virtual time), so the program waits in a bounded loop for the handler's flag and
# only flags are compared; the interrupted instruction is not. IM2 stays 0 (Malta HW0).
# oracle: bare
# oracle: expect gpr:s0=0 gpr:s1=1 gpr:s2=1 gpr:s3=1 gpr:s4=1 gpr:s5=0 gpr:s6=0xe0000000 gpr:s7=0
# oracle: max-steps 200000
.ktext
mfc0 $k0, $13
andi $s0, $k0, 0x7c
srl $s1, $k0, 30
andi $s1, $s1, 1
srl $s2, $k0, 15
andi $s2, $s2, 1
# Compare far ahead: clears TI
mfc0 $k1, $9
lui $k0, 0x4000
addu $k1, $k1, $k0
mtc0 $k1, $11
mfc0 $k0, $13
srl $s5, $k0, 30
andi $s5, $s5, 1
li $s3, 1
addiu $s4, $s4, 1
li $k0, 0
li $k1, 0
eret
.text
mfc0 $s6, $12, 1
mfc0 $s7, $12, 2
# Compare = Count + 2000, then enable IM7 and IE
mfc0 $t1, $9
addiu $t1, $t1, 2000
mtc0 $t1, $11
li $t1, 0x20008001
mtc0 $t1, $12
li $t4, 50000000
poll:
bnez $s3, done
nop
addiu $t4, $t4, -1
bnez $t4, poll
nop
done:
lui $t1, 0x2000
mtc0 $t1, $12
li $t1, 0
li $t4, 0
