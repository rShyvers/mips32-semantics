# cfc1/ctc1: FCSR ($31) and the FCCR/FEXR/FENR views ($25 $26 $28); rounding-mode field and condition code.
# MD00086 Vol II-A Rev 6.06: CFC1 p.129-130, CTC1 p.149-151; Vol I Rev 6.01 sec "Floating Point Control and Status
# Register (FCSR)" (mipsdoc.py section v1 "FCSR").  Written values avoid Cause/Enable bits (no FP exception).
# FCSR = RM(1:0)=3 | FCC0(23)=1 => 0x00800003 ; FCCR($25) = fcc[7:0] = 0x01; FENR($28) = RM | FS<<2 = 3.
# oracle: expect gpr:s0=0x00800003 gpr:s1=0x00000001 gpr:s2=0x00000003
li $t0, 0x00800003
ctc1 $t0, $31
cfc1 $s0, $31
cfc1 $s1, $25
cfc1 $s2, $28
ctc1 $zero, $31
cfc1 $s3, $31
li $t0, 0x01000000         # FS (flush-to-zero) bit only
ctc1 $t0, $31
cfc1 $s4, $31
ctc1 $zero, $31
li $v0, 10
syscall
