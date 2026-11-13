# Exception in a delay slot with a handler: handler sees Cause.BD = 1 and EPC = the branch; it resumes at
# EPC+8 (the branch target is branch+8 here). MD00090 Vol III Rev 6.02 sec 9.36 (Cause.BD), 9.37 (EPC);
# MD00086 Vol II-A Rev 6.06 ADD p.33, ERET p.177-178.
# oracle: expect gpr:s7=1 gpr:s4=0x80000030
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
li $t0, 0x7fffffff
li $t1, 1
beq $zero, $zero, tgt
add $t2, $t0, $t1
nop
tgt: li $s0, 77
nop
