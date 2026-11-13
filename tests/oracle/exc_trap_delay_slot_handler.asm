# A trap (teq) in the delay slot of jal, with a handler: the handler sees BD = 1 and EPC = the jal; $ra was already
# written by the jal (link = jal+8). It resumes at EPC+8 (= the jal target here: jal to the next-but-one instruction).
# MD00086 Vol II-A Rev 6.06: TEQ p.416, JAL p.195 ("the link is written regardless"); MD00090 Vol III sec 9.36/9.37.
# oracle: expect gpr:s7=1 gpr:s4=0x80000034
.ktext
mfc0 $k0, $13
mfc0 $k1, $14
addiu $s7, $s7, 1
move $s4, $k0
bltz $k0, bd
nop
addiu $k1, $k1, 4
b out
nop
bd: addiu $k1, $k1, 8
out: mtc0 $k1, $14
eret
.text
jal tgt
teq $zero, $zero
nop
tgt: move $s0, $ra
nop
