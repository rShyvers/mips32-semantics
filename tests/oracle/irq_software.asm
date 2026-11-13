# Software interrupts SW0/SW1 (Cause.IP0/IP1 written with mtc0) in interrupt compatibility mode: taken when the request is
# unmasked (Status.IM) and Status.IE = 1, EXL = ERL = 0; not taken while masked, with IE = 0 or with EXL = 1; taken as soon as the
# blocking bit is cleared (mtc0 Status, ei). Interrupt exception: ExcCode 0, EPC = the instruction that was not executed, EXL = 1,
# vector 0x80000180 (Cause.IV = 0). Each request is followed by `ehb` ("makes the change to the interrupt state visible no later than
# the instruction following the EHB"), so the interrupt is taken at the `ehb` or at the instruction after it; both the model
# (hazards cleared at once, pin) and QEMU take it at the `ehb`.
# MD00090 Vol III Rev 6.02 sec 6.1 p.72 (conditions), sec 6.1.1.1 Table 6.2 p.73 (SW0 = CauseIP0 and StatusIM0), sec 6.1.2.1 Table 6.5
# p.82 (EHB), sec 6.2.26 p.102 (ExcCode Int, vector 0x180 if IV = 0), Table 9.52 p.212 (IP1..IP0 R/W); MD00086 Vol II-A Rev 6.06 EI p.176.
# IM2 stays 0: the Malta board raises HW0 (IP2) on its own. The handler counts entries (s4), records ExcCode (s0), the pending
# software requests (s1), EPC relative to the expected address in t0 (s2) and Status (s3), then clears the requests and returns.
# oracle: bare
# oracle: expect gpr:s4=4 gpr:s5=4 gpr:s0=0 gpr:s2=0 gpr:s3=0x20000203
.ktext
mfc0 $k0, $13
andi $s0, $k0, 0x7c
andi $s1, $k0, 0x300
mfc0 $s2, $14
subu $s2, $s2, $t0
mfc0 $s3, $12
addiu $s4, $s4, 1
mtc0 $zero, $13
li $k0, 0
eret
.text
# 1. SW0 with IM0 = IE = 1: taken at once
li $t1, 0x20000101
mtc0 $t1, $12
la $t0, h1
li $t2, 0x100
mtc0 $t2, $13
h1: ehb
addiu $s5, $s5, 1
# 2. SW1 requested while IM1 = 0: pending, not taken; then IM1 = 1 (mtc0 Status): taken
mtc0 $zero, $14
li $t2, 0x200
mtc0 $t2, $13
ehb
nop
li $t1, 0x20000201
la $t0, h2
mtc0 $t1, $12
h2: ehb
addiu $s5, $s5, 1
# 3. IE = 0 (di): request pending, not taken; ei: taken
di
li $t2, 0x200
mtc0 $t2, $13
ehb
nop
la $t0, h3
ei
h3: ehb
addiu $s5, $s5, 1
# 4. EXL = 1: not taken; clearing EXL: taken
li $t1, 0x20000203
mtc0 $t1, $12
li $t2, 0x200
mtc0 $t2, $13
ehb
nop
li $t1, 0x20000201
la $t0, h4
mtc0 $t1, $12
h4: ehb
addiu $s5, $s5, 1
# end: interrupts off, requests clear
lui $t1, 0x2000
mtc0 $t1, $12
mtc0 $zero, $13
li $t0, 0
li $t1, 0
li $t2, 0
