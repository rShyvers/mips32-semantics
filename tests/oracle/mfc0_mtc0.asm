# mfc0/mtc0 on the CP0 registers the model implements: Status (IM bits only; IE/EXL/ERL/BEV stay clear: ERL would
# make kuseg unmapped on QEMU, BEV moves the vector), Cause (IV, IP1..0 writable), EPC, ErrorEPC, BadVAddr (read-only).
# MD00086 Vol II-A Rev 6.06: MFC0 p.266, MTC0 p.290-291; MD00090 Vol III Rev 6.02 sec 9.35 BadVAddr, 9.36 Cause,
# 9.37 EPC, 9.38 ErrorEPC. Cause.ExcCode/BD are not writable; BadVAddr ignores writes.
# oracle: expect gpr:s0=0x2400ff00 gpr:s1=0x00800300 gpr:s2=0x00400000 gpr:s3=0x00000123 gpr:s4=0
lui $t0, 0x2000
ori $t0, $t0, 0xff00
mtc0 $t0, $12
mfc0 $s0, $12
li $t1, 0x0080037c
mtc0 $t1, $13              # IV (23), IP1..0 (9..8) take effect; ExcCode (6..2) is read-only
mfc0 $s1, $13
li $t2, 0x00400000
mtc0 $t2, $14
mfc0 $s2, $14
li $t3, 0x123
mtc0 $t3, $30
mfc0 $s3, $30
mtc0 $t3, $8               # BadVAddr is read-only
mfc0 $s4, $8
lui $t0, 0x2000
mtc0 $t0, $12
mtc0 $zero, $13
li $v0, 10
syscall
