# SIGRIE raises Reserved Instruction (ExcCode 10) in Kernel and in User Mode; BadInstr holds the sigrie word; EPC = the sigrie.
# MD00086 Vol II-A Rev 6.06 SIGRIE p.375 ("Operation: SignalException(ReservedInstruction)"; encoding REGIMM, rs = 0, rt = 10111, 16-bit code);
# MD00090 Vol III Rev 6.02 sec 9.25 p.179 (BadInstr captures "the most recent instruction which caused one of the following exceptions: ...
# Reserved Instruction"), Table 9.53 p.212 (ExcCode 10 = RI).
# The handler counts entries (s4), keeps ExcCode (s5), BadInstr (s6 first, s7 second), EPC minus the expected address in t0 (s3 |= ...), skips it.
# oracle: expect gpr:s4=2 gpr:s5=10 gpr:s6=0x04171234 gpr:s7=0x0417ffff gpr:s3=0
.ktext
addiu $s4, $s4, 1
mfc0 $k0, $13
andi $s5, $k0, 0x7c
srl $s5, $s5, 2
move $s6, $s7
mfc0 $s7, $8, 1
mfc0 $k0, $14
subu $k1, $k0, $t0
or $s3, $s3, $k1
addiu $k0, $k0, 4
mtc0 $k0, $14
li $k1, 0
eret
.text
li $s3, 0
li $s4, 0
la $t0, k1
k1: sigrie 0x1234
la $t0, user
mtc0 $t0, $14
lui $t1, 0x2000
ori $t1, $t1, 0x12
mtc0 $t1, $12
la $t0, u1
eret
user:
u1: sigrie 0xffff
li $t0, 0
li $t1, 0
