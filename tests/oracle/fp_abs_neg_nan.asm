# abs.s/neg.s of a NaN operand (0xffa00000 / 0x7fa00000). Release 6 requires FCSR.ABS2008 = 1 (MD00082 Vol I-A Rev 6.01 FCSR
# Table 6.8 p.93): "If FCSRABS2008=1 then this operation is non-arithmetic" (MD00086 Vol II-A Rev 6.06 ABS.fmt p.32, NEG.fmt p.307),
# so the sign bit is cleared / flipped and no Invalid is signaled. The model still has the legacy (ABS2008 = 0, arithmetic) FPU
# until W5: it raises Invalid (FCSR 0x00010040, reading A' of SPEC-NOTES 9.21) -- a known model bug on the FCSR values.
# The result values agree: abs.s 0xffa00000 -> $s1 = 0x7fa00000; neg.s 0x7fa00000 -> $s3 = 0xffa00000.
# FCSR reads are masked to drop the read-only NAN2008/ABS2008 bits 19..18 (checked in fp_fcsr_nan2008_abs2008).
# oracle: expect gpr:s1=0x7fa00000
# oracle: expect gpr:s3=0xffa00000
# oracle: known-model-bug gpr:s0 MD00086 Vol II-A Rev 6.06 ABS.fmt p.32 / NEG.fmt p.307: "If FCSRABS2008=1 then this operation is non-arithmetic" and FCSR.ABS2008 is required 1 in Release 6 (MD00082 Vol I-A Rev 6.01 FCSR Table 6.8 p.93); W5: the model is still the ABS2008 = 0 (arithmetic) FPU
# oracle: known-model-bug gpr:s2 MD00086 Vol II-A Rev 6.06 ABS.fmt p.32 / NEG.fmt p.307: "If FCSRABS2008=1 then this operation is non-arithmetic" and FCSR.ABS2008 is required 1 in Release 6 (MD00082 Vol I-A Rev 6.01 FCSR Table 6.8 p.93); W5: the model is still the ABS2008 = 0 (arithmetic) FPU
li $t9, 0xffa00000
mtc1 $t9, $f0
ctc1 $zero, $31
abs.s $f2, $f0
cfc1 $s0, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $s0, $s0, $at
mfc1 $s1, $f2
li $t9, 0x7fa00000
mtc1 $t9, $f0
ctc1 $zero, $31
neg.s $f4, $f0
cfc1 $s2, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $s2, $s2, $at
mfc1 $s3, $f4
ctc1 $zero, $31
li $v0, 10
syscall
