# Release 6 removes the FP condition codes: cfc1 of FCCR ($25) reads 0 and a write of 0xff (temp31..8 = 0) through ctc1 $25 is ignored; FCSR ($31) keeps its value (only the
# read-only NAN2008/ABS2008 bits, 0x000c0000, after ctc1 $zero,$31). The model reads FCSR/FCCR/FEXR/FENR identically afterwards.
# MD00086 Vol II-A Rev 6.06 CFC1 p.129-130 (Restrictions: 'In Release 6 and later, a Reserved Instruction exception occurs if fs specifies a register that does not exist'; Operation: fs = 1 (UFR),
# fs = 4 (UNFR) 'Release 6 traps', other nonexistent fs 'Release 6 traps'), CTC1 p.149-150 (fs = 1, 4 'Release 6 traps'; fs = 5, 6 (FRE/NFRE): Reserved Instruction without FIRUFRP and Config5UFR);
# MD00082 Vol I-A Rev 6.01 6.5.5 p.96 (Release 6 removes the FCCs and FCCR).
# MD00082 Vol I-A Rev 6.01 FCSR Table 6.8 p.92 (FCC 'pre-Release 6 feature': R0).
# oracle: expect gpr:s0=0 gpr:s1=0x000c0000 gpr:s2=0 gpr:s3=0x000c0000 gpr:s4=0 gpr:s5=0
.data
res: .space 64
.text
la $s7, res
ctc1 $zero, $31
cfc1 $s0, $25
li $t0, 0xff
ctc1 $t0, $25
cfc1 $s1, $31
cfc1 $s2, $25
ctc1 $zero, $25
cfc1 $s3, $31
cfc1 $s4, $26
cfc1 $s5, $28
li $v0, 10
syscall
