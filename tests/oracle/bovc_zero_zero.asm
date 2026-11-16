# BOVC and BNVC with rs = rt = 0 (POP10/POP30 with both register fields 0). MD00086 Vol II-A Rev 6.06,
# Table A.26 p.464: on POP10/POP30 "0rs 0rt" is BOVC/BNVC (the "=" column), and BOVC p.107: "The special
# case of rs=0 and rt=0 is allowed. BOVC never branches, while BNVC always branches." Neither links.
# Observed 2026-11-16 (QEMU mips32r6-generic): the branch behaviour agrees (s0, s1), but both write
# $ra = their address + 4, as BEQZALC/BNEZALC would (those need rt != 0, p.77); here the final $ra is
# that of the `bnvc` (0x00400014). The manual wins (CLAUDE.md); declared below.
# oracle: expect-deviation gpr:ra MD00086 Vol II-A Rev 6.06 BOVC/BNVC p.107 ("The special case of rs=0 and rt=0 is allowed. BOVC never branches, while BNVC always branches") and Table A.26 p.464 (rs = rt = 0 on POP10/POP30 is BOVC/BNVC, not BEQZALC/BNEZALC): QEMU links $31
# oracle: expect gpr:ra=0 gpr:s0=1 gpr:s1=0
li $s0, 0
li $s1, 0
bovc $zero, $zero, a1      # never branches, no link
addiu $s0, $s0, 1
a1: bnvc $zero, $zero, a2  # always branches, no link
ori $s1, $s1, 1
a2: li $v0, 10
syscall
