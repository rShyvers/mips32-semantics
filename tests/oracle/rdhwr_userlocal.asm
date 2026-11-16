# UserLocal (CP0 4 sel 2) is R/W in Kernel Mode, and RDHWR 29 (ULR) reads it: in Kernel Mode always, in User Mode only while HWREna bit 29 = 1,
# else Reserved Instruction (destination unchanged).
# MD00090 Vol III Rev 6.02 sec 9.11 p.143 ("Release 6: Required"; UserInformation R/W; Programming Notes: "To do so, bit 29 of the HWREna register
# must be set to a 1 to enable unprivileged access to the register"), Table 9.39 p.175 (HWREna Mask), Table 9.40 p.176 (29 ULR); MD00086 Vol II-A
# Rev 6.06 RDHWR p.333 ("Access to the specified hardware register is enabled if Coprocessor 0 is enabled, or if the corresponding bit is set in the
# HWREna register. If access is not allowed or the register is not implemented, a Reserved Instruction Exception is signaled"), MFC0 p.266, MTC0 p.290.
# Kernel: s0 = mfc0 UserLocal, s1 = rdhwr 29. User (HWREna = bit 29): s2 = rdhwr 29; break (the handler clears HWREna); s3 = rdhwr 29 -> RI.
# The handler counts RI exceptions (s6), clears HWREna on a Breakpoint, skips the instruction.
# oracle: expect gpr:s0=0xcafebabe gpr:s1=0xcafebabe gpr:s2=0xcafebabe gpr:s3=0x3333 gpr:s6=1
.ktext
mfc0 $k0, $13
andi $k0, $k0, 0x7c
xori $k1, $k0, 0x28
bnez $k1, not_ri
nop
addiu $s6, $s6, 1
not_ri:
xori $k1, $k0, 0x24
bnez $k1, not_bp
nop
mtc0 $zero, $7
not_bp:
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
li $k1, 0
eret
.text
li $s6, 0
li $s3, 0x3333
li $t0, 0xcafebabe
mtc0 $t0, $4, 2
mfc0 $s0, $4, 2
rdhwr $s1, $29
lui $t0, 0x2000
mtc0 $t0, $7
la $t2, user
mtc0 $t2, $14
lui $t3, 0x2000
ori $t3, $t3, 0x12
mtc0 $t3, $12
li $t0, 0
eret
user:
rdhwr $s2, $29
break
rdhwr $s3, $29
li $t2, 0
li $t3, 0
