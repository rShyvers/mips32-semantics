# With CU1 = 0 every FP-unit instruction raises Coprocessor Unusable: the handler logs Cause (ExcCode 11, CE 1) per instruction and skips it.
# Covers arithmetic, loads/stores, moves to/from coprocessor, FCSR access, ldc1, mfhc1, and four pre-Release 6 COP1 encodings
# Release 6 removed (C.EQ.S, MOVF.S, MOVN.S, BC1T, emitted as .word): in the COP1 opcode space Coprocessor Unusable takes priority
# (MD00086 Vol II-A Rev 6.06 Table A.1 p.451: 'If the encoding has been used for a new instruction or coprocessor, the unusable
# exception takes priority').
# MD00090 Vol III Rev 6.02 sec 6.2.22 (Coprocessor Unusable: ExcCode 11, Cause.CE = coprocessor number when Status.CU1 = 0); MD00086 Vol II-A Rev 6.06 each FP instruction's 'Exceptions: Coprocessor Unusable'.
# oracle: expect gpr:s4=16
.data
.align 3
dat: .word 1, 2, 3, 4
res: .space 64
.ktext
mfc0 $k0, $13
sw $k0, 0($s7)
addiu $s7, $s7, 4
addiu $s4, $s4, 1
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
eret
.text
la $s7, res
li $s4, 0
la $t0, dat
li $t1, 8
mtc0 $zero, $12
add.s $f2, $f4, $f6
addiu $s5, $s5, 1
lwc1 $f2, 0($t0)
addiu $s5, $s5, 1
swc1 $f2, 0($t0)
addiu $s5, $s5, 1
mfc1 $t2, $f2
addiu $s5, $s5, 1
mtc1 $t2, $f2
addiu $s5, $s5, 1
cfc1 $t2, $31
addiu $s5, $s5, 1
ctc1 $t2, $31
addiu $s5, $s5, 1
.word 0x46041032        # pre-Release 6 c.eq.s $f2, $f4
addiu $s5, $s5, 1
.word 0x46002091        # pre-Release 6 movf.s $f2, $f4, $fcc0
addiu $s5, $s5, 1
ldc1 $f2, 0($t0)
addiu $s5, $s5, 1
mfhc1 $t2, $f2
addiu $s5, $s5, 1
sqrt.d $f2, $f4
addiu $s5, $s5, 1
cvt.d.s $f2, $f4
addiu $s5, $s5, 1
.word 0x46092093        # pre-Release 6 movn.s $f2, $f4, $t1
addiu $s5, $s5, 1
mov.s $f2, $f4
addiu $s5, $s5, 1
.word 0x45010001        # pre-Release 6 bc1t (not a branch in Release 6)
addiu $s6, $s6, 1
L1: nop
