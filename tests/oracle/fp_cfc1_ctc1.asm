# cfc1/ctc1: FCSR ($31) and the FENR/FEXR views ($28 $26); rounding-mode and FS fields.
# MD00086 Vol II-A Rev 6.06: CFC1 p.129-130, CTC1 p.149-150; MD00082 Vol I-A Rev 6.01 6.5.4 FCSR (Table 6.8 p.92-94), 6.5.6/6.5.7.
# Release 6 removes the FP condition codes (FCSR.FCC is R0, Table 6.8 p.92) and the FCCR ($25, "reserved in Release 6", 6.5.5 p.96):
# neither is used. Written values avoid Cause/Enable bits (no FP exception). FCSR reads are masked to drop the read-only bits 19..18
# (NAN2008/ABS2008, checked in fp_fcsr_nan2008_abs2008).
# FCSR = RM(1:0)=3 => 0x00000003; FENR($28) = RM | FS<<2 = 3; with FS (bit 24): FCSR 0x01000000, FENR 4.
# oracle: expect gpr:s0=0x00000003 gpr:s2=0x00000003 gpr:s3=0 gpr:s4=0x01000000 gpr:s5=4 gpr:s6=0
lui $at, 0xfff3
ori $at, $at, 0xffff
li $t0, 0x00000003
ctc1 $t0, $31
cfc1 $s0, $31
and $s0, $s0, $at
cfc1 $s2, $28
ctc1 $zero, $31
cfc1 $s3, $31
and $s3, $s3, $at
li $t0, 0x01000000         # FS (flush-to-zero) bit only
ctc1 $t0, $31
cfc1 $s4, $31
and $s4, $s4, $at
cfc1 $s5, $28
cfc1 $s6, $26
ctc1 $zero, $31
li $v0, 10
syscall
