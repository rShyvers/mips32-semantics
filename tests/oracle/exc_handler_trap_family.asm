# All twelve trap instructions, each taken and not taken, with a handler that counts.
# MD00086 Vol II-A Rev 6.06: TEQ p.416, TEQI p.417, TGE p.418, TGEI p.419, TGEIU p.420, TGEU p.421, TLT p.434,
# TLTI p.435, TLTIU p.436, TLTU p.437, TNE p.438, TNEI p.439. a=-1 (0xffffffff), b=1.
# Taken: teq(a,a) tne(a,b) tge(b,a) tlt(a,b) tgeu(a,b) tltu(b,a) teqi(a,-1) tnei(a,1) tgei(b,-1) tlti(a,1) tgeiu(a,1) tltiu(b,-1)
# = 12 traps; not taken: the 12 complementary cases. => $s7 = 12 exactly.
# oracle: expect gpr:s7=12
.ktext
# handler: record Cause/EPC/BadVAddr, count in $s7, ExcCode history in $s6 (shifted 8 bits per exception),
# skip the faulting instruction (EPC += 4; if Cause.BD: the branch target is branch+8 in these tests), eret.
mfc0 $k0, $13
mfc0 $k1, $14
addiu $s7, $s7, 1
sll $s6, $s6, 8
srl $t9, $k0, 2
andi $t9, $t9, 31
or $s6, $s6, $t9
mfc0 $s5, $8
move $s4, $k0
move $s3, $k1
bltz $k0, bdslot
nop
addiu $k1, $k1, 4
b out
nop
bdslot: addiu $k1, $k1, 8
out: mtc0 $k1, $14
eret
.text
li $t0, -1
li $t1, 1
teq $t0, $t0
tne $t0, $t1
tge $t1, $t0
tlt $t0, $t1
tgeu $t0, $t1
tltu $t1, $t0
teqi $t0, -1
tnei $t0, 1
tgei $t1, -1
tlti $t0, 1
tgeiu $t0, 1
tltiu $t1, -1
teq $t0, $t1
tne $t0, $t0
tge $t0, $t1
tlt $t1, $t0
tgeu $t1, $t0
tltu $t0, $t1
teqi $t0, 1
tnei $t0, -1
tgei $t0, 1
tlti $t1, -1
tgeiu $t1, -1
tltiu $t0, 1
nop
