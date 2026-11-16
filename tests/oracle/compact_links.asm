# Release 6 compact branch-and-link and compact jumps. MD00086 Vol II-A Rev 6.06: B{LE,GE,GT,LT,EQ,NE}ZALC
# p.77-79 ("Places the return address link in GPR 31. The return link is the address of the instruction
# immediately following the branch ... The return address link is unconditionally updated"), BALC p.52,
# JIC p.205, JIALC p.203 ("temp <- GPR[rt] + sign_extend(offset)", offset not shifted; "The register
# specifier may be set to the link register $31"). Each link is saved to an $s register; a taken
# branch skips an `ori $s7` (bit set = wrongly executed).
# oracle: expect gpr:s7=0 gpr:s6=0x3f
li $s6, 0
li $s7, 0
li $t0, -3
li $t1, 0
li $t2, 4
blezalc $t0, a1            # taken
ori $s7, $s7, 1
a1: move $s0, $ra
bgezalc $t0, a2            # not taken: link still written
ori $s6, $s6, 1
a2: move $s1, $ra
bgtzalc $t2, a3            # taken
ori $s7, $s7, 2
a3: bltzalc $t2, a4        # not taken
ori $s6, $s6, 2
a4: move $s2, $ra
beqzalc $t2, a5            # not taken ($t2 = 4)
ori $s6, $s6, 4
a5: bnezalc $t2, a6        # taken
ori $s7, $s7, 4
a6: move $s3, $ra
la $t3, a7
balc a7                    # always; link = next instruction
ori $s7, $s7, 8
a7: move $s4, $ra
subu $s4, $s4, $t3         # the link is the balc's address + 4, so $s4 = a7 - a7 = 0
la $t4, a8
jic $t4, 0                 # PC <- $t4 + 0
ori $s7, $s7, 0x10
a8: la $t5, a9 + 3
jialc $t5, -3              # offset not shifted: $t5 - 3 = a9
ori $s7, $s7, 0x20
a9: move $s5, $ra
la $ra, a10
jialc $ra, 0               # rt = 31: jumps to the old $ra, then links
ori $s7, $s7, 0x40
a10: beqzalc $t1, a11      # taken ($t1 = 0)
ori $s7, $s7, 0x80
a11: bltzalc $t0, a12      # taken
ori $s7, $s7, 0x100
a12: bgtzalc $t0, a13      # not taken
ori $s6, $s6, 8
a13: blezalc $t2, a14      # not taken
ori $s6, $s6, 0x10
a14: bnezalc $t1, a15      # not taken
ori $s6, $s6, 0x20
a15: li $v0, 10
syscall
