# A branch in the delay slot of a branch. Pre-Release 6 this is UNPREDICTABLE: "Processor operation
# is UNPREDICTABLE if a control transfer instruction (CTI) is placed in the delay slot of a branch
# or jump" (MD00086 Vol II-A Rev 6.06, BEQ p.72; MD00082 Vol I-A Rev 6.01 sec 5.3.2.1 p.62), and
# "UNPREDICTABLE operations may cause arbitrary exceptions" but "must not halt or hang the
# processor" (MD00086 sec 1.2.1 p.3-4). The model pins Reserved Instruction taken in the delay slot
# (Cause.ExcCode = 10, Cause.BD = 1, EPC = the first branch), which is also what Release 6 requires
# (MD00082 sec 5.3.2.1 p.62). QEMU's behaviour is not authoritative here: every observable that
# depends on the CTI pair is not compared; the model's pinned values are checked with `expect`.
# (Observed 2026-11-13: QEMU 24Kf also raises Reserved Instruction here and agrees on every field.)
# oracle: unpredictable gpr MD00086 Vol II-A Rev 6.06 BEQ p.72: CTI in a delay slot is UNPREDICTABLE (model pins Reserved Instruction)
# oracle: unpredictable cause same
# oracle: unpredictable epc same
# oracle: unpredictable status same
# oracle: unpredictable pc same
# oracle: unpredictable term same
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
