# Underflow with the Underflow trap enabled and an EXACT tiny result: mul.s 0.5 * 2^-126 = 2^-127 and mul.d 0.5 * 2^-1022 = 2^-1023
# (tiny, representable as a denormal, no loss of accuracy). With Enables.U set, underflow is signaled on tininess alone, so the
# instruction traps (Floating Point exception, ExcCode 15, Cause.U, destination not written). Controls: the same exact tiny
# product with Enables.U clear (no flag at all: underflow needs tininess AND loss of accuracy), and an inexact tiny product with
# Enables.U set (traps on both). The handler records ExcCode history ($s6), the trap count ($s4) and FCSR at the trap ($s5),
# clears FCSR.Cause and skips the instruction. Per case: destination bits (a sentinel when not written), FCSR after, $s5.
# MD00082 Vol I-A Rev 6.01 sec 6.7.2.3 p.101 ("When an underflow trap is enabled (through the FCSR Enable field bit), underflow is
# signaled when tininess is detected regardless of loss of accuracy"; "When an underflow trap is not enabled, underflow is signaled
# only when both tininess and loss of accuracy have been detected"); sec 6.7.1 p.99 (a trap whenever a Cause bit and its Enable are set).
# Doubles are loaded with mtc1/mthc1 and read with mfhc1 (the same with Status.FR = 0 and FR = 1); FCSR reads are masked to drop the
# read-only NAN2008/ABS2008 bits 19..18 (checked in fp_fcsr_nan2008_abs2008).
# QEMU mips32r6-generic signals Underflow only for an inexact tiny result, also with the trap enabled: the exact cases do not trap there.
# oracle: expect gpr:s4=3
# oracle: expect gpr:s6=0x000f0f0f
# oracle: expect mem:0x10010000=0x12345678 mem:0x10010004=0x00000100 mem:0x10010008=0x00002100
# oracle: expect mem:0x10010018=0x00400000 mem:0x1001001c=0x00000000 mem:0x10010020=0x00000000
# oracle: expect mem:0x1001000c=0x12345678 mem:0x10010010=0x00000100 mem:0x10010014=0x00002100
# oracle: expect mem:0x10010024=0x12345678 mem:0x10010028=0x00000100 mem:0x1001002c=0x00003100
# oracle: expect-deviation gpr:s4 MD00082 Vol I-A Rev 6.01 sec 6.7.2.3 p.101: "When an underflow trap is enabled ..., underflow is signaled when tininess is detected regardless of loss of accuracy": the two exact tiny products trap (3 traps in the model); QEMU traps only on the inexact control (1)
# oracle: expect-deviation gpr:s6 MD00082 Vol I-A Rev 6.01 sec 6.7.2.3 p.101: "When an underflow trap is enabled ..., underflow is signaled when tininess is detected regardless of loss of accuracy": ExcCode history 15,15,15 (model 0x000f0f0f); QEMU 0x0000000f
# oracle: expect-deviation mem:0x10010000 MD00082 Vol I-A Rev 6.01 sec 6.7.2.3 p.101: "When an underflow trap is enabled ..., underflow is signaled when tininess is detected regardless of loss of accuracy": mul.s exact tiny with Enables.U traps, fd not written (model sentinel 0x12345678); QEMU writes 2^-127 = 0x00400000
# oracle: expect-deviation mem:0x10010008 MD00082 Vol I-A Rev 6.01 sec 6.7.2.3 p.101: "When an underflow trap is enabled ..., underflow is signaled when tininess is detected regardless of loss of accuracy": FCSR at the trap for mul.s is Enables.U|Cause.U (model 0x00002100); QEMU does not trap (0)
# oracle: expect-deviation mem:0x1001000c MD00082 Vol I-A Rev 6.01 sec 6.7.2.3 p.101: "When an underflow trap is enabled ..., underflow is signaled when tininess is detected regardless of loss of accuracy": mul.d exact tiny with Enables.U traps, fd not written (model sentinel 0x12345678); QEMU writes 2^-1023 (high word 0x00080000)
# oracle: expect-deviation mem:0x10010014 MD00082 Vol I-A Rev 6.01 sec 6.7.2.3 p.101: "When an underflow trap is enabled ..., underflow is signaled when tininess is detected regardless of loss of accuracy": FCSR at the trap for mul.d is Enables.U|Cause.U (model 0x00002100); QEMU does not trap (0)
.data
res: .space 96
.ktext
mfc0 $k0, $13
srl $k0, $k0, 2
andi $k0, $k0, 31
sll $s6, $s6, 8
or $s6, $s6, $k0
addiu $s4, $s4, 1
cfc1 $s5, $31
lui $k1, 0xfff3
ori $k1, $k1, 0xffff
and $s5, $s5, $k1
li $k1, 0xfffc0fff
and $k1, $s5, $k1
ctc1 $k1, $31
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
eret
.text
la $s7, res
li $s4, 0
li $s6, 0
# case 0: mul.s 0.5 * 2^-126, exact tiny, Enables.U
li $s5, 0
li $t9, 0x12345678
mtc1 $t9, $f10
li $t9, 0x3f000000
mtc1 $t9, $f6
li $t9, 0x00800000
mtc1 $t9, $f8
li $t8, 0x00000100
ctc1 $t8, $31
mul.s $f10, $f6, $f8
mfc1 $t0, $f10
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
ctc1 $zero, $31
sw $t0, 0($s7)
sw $t1, 4($s7)
sw $s5, 8($s7)
# case 1: mul.d 0.5 * 2^-1022, exact tiny, Enables.U (result high word at 12, FCSR 16, $s5 20)
li $s5, 0
li $t9, 0x12345678
mtc1 $t9, $f10
mthc1 $t9, $f10
mtc1 $zero, $f6
li $t9, 0x3fe00000
mthc1 $t9, $f6
mtc1 $zero, $f8
li $t9, 0x00100000
mthc1 $t9, $f8
li $t8, 0x00000100
ctc1 $t8, $31
mul.d $f10, $f6, $f8
mfhc1 $t0, $f10
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
ctc1 $zero, $31
sw $t0, 12($s7)
sw $t1, 16($s7)
sw $s5, 20($s7)
# case 2 (control): mul.s 0.5 * 2^-126 with Enables.U clear: exact tiny, no flag, no trap
li $s5, 0
li $t9, 0x12345678
mtc1 $t9, $f10
li $t9, 0x3f000000
mtc1 $t9, $f6
li $t9, 0x00800000
mtc1 $t9, $f8
ctc1 $zero, $31
mul.s $f10, $f6, $f8
mfc1 $t0, $f10
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
ctc1 $zero, $31
sw $t0, 24($s7)
sw $t1, 28($s7)
sw $s5, 32($s7)
# case 3 (control): mul.s 0.75 * (2^-126 + ulp), inexact tiny, Enables.U: traps on both
li $s5, 0
li $t9, 0x12345678
mtc1 $t9, $f10
li $t9, 0x3f400000
mtc1 $t9, $f6
li $t9, 0x00800001
mtc1 $t9, $f8
li $t8, 0x00000100
ctc1 $t8, $31
mul.s $f10, $f6, $f8
mfc1 $t0, $f10
cfc1 $t1, $31
lui $at, 0xfff3
ori $at, $at, 0xffff
and $t1, $t1, $at
ctc1 $zero, $31
sw $t0, 36($s7)
sw $t1, 40($s7)
sw $s5, 44($s7)
mthc1 $zero, $f6               # the final FPR dump of an FR = 1 FPU holds only low words (results are in memory)
mthc1 $zero, $f8
mthc1 $zero, $f10
