# Cause.IV = 1: the Interrupt exception uses the special interrupt vector, offset 0x200 (0x80000200 with EBase at its reset value and
# BEV = 0), not the general exception vector 0x80000180; a non-interrupt exception (break) still goes to 0x80000180. IntCtl.VS = 0
# (no vectored interrupts), so the offset is 0x200 for every request.
# MD00090 Vol III Rev 6.02 sec 6.2.26 p.102 ("Interrupt vector (offset 0x200) if the IV bit in the Cause register is one"), sec 6.1.1.1
# p.73 (compatibility mode dispatches through 0x200 if CauseIV = 1), Table 6.10 p.86 (Interrupt, BEV 0, EXL 0, IV 1: 0x8000.0200), sec 6.2.3
# Operation p.88 ("if (StatusBEV = 1) or (IntCtlVS = 0) then vectorOffset <- 0x200"), Table 9.48 p.201 (IntCtl.VS).
# The .ktext image starts at 0x80000180: the general handler (break: s6 += 1, skip it) is padded with nops to 0x80000200, where the
# interrupt handler records ExcCode (s0), EPC relative to the expected address (s2) and counts entries (s4).
# oracle: bare
# oracle: expect gpr:s4=1 gpr:s6=1 gpr:s0=0 gpr:s2=0 gpr:s5=1
.ktext
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
addiu $s6, $s6, 1
li $k0, 0
eret
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
# 0x80000200: interrupt vector (Cause.IV = 1)
mfc0 $k0, $13
andi $s0, $k0, 0x7c
mfc0 $s2, $14
subu $s2, $s2, $t0
addiu $s4, $s4, 1
mtc0 $zero, $13
li $k0, 0
eret
.text
break
li $t1, 0x20000101
mtc0 $t1, $12
la $t0, h1
lui $t2, 0x0080
ori $t2, $t2, 0x100
mtc0 $t2, $13
h1: ehb
addiu $s5, $s5, 1
lui $t1, 0x2000
mtc0 $t1, $12
li $t0, 0
li $t1, 0
li $t2, 0
