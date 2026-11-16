# A branch in the delay slot of a branch. Release 6 requires a Reserved Instruction exception: "In
# Release 6, if a CTI is placed in a branch delay slot or a compact branch forbidden slot,
# implementations are required to signal a Reserved Instruction exception" (MD00082 Vol I-A Rev 6.01
# sec 5.3.2.1 p.62; MD00086 Vol II-A Rev 6.06 BEQ Restrictions p.72: "Release 6: If a control
# transfer instruction (CTI) is executed in the delay slot of a branch or jump, Release 6
# implementations are required to signal a Reserved Instruction exception"; only pre-Release 6 is it
# UNPREDICTABLE). The exception is for the instruction in the delay slot: EPC = the first branch with
# Cause.BD = 1 (MD00082 Vol I-A Rev 6.01 sec 5.3.2.2 p.62; MD00090 Vol III Rev 6.02 sec 9.38 p.217),
# ExcCode 10. Every field is compared with QEMU mips32r6-generic (no `unpredictable` directive: the
# behaviour is mandated), and the pinned values are also checked with `expect`.
# oracle: expect gpr:s7=1 gpr:s4=0x80000028 gpr:s3=0x00400000 gpr:s0=1 gpr:s1=2
.ktext
    mfc0  $k0, $13
    mfc0  $k1, $14
    addiu $s7, $s7, 1
    move  $s4, $k0
    move  $s3, $k1
    addiu $k1, $k1, 8
    mtc0  $k1, $14
    eret
.text
    beq   $zero, $zero, t1
    beq   $zero, $zero, t2
    nop
t1: li    $s0, 1
t2: li    $s1, 2
    nop
