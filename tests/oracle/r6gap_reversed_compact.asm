# The reversed-operand compact-branch idioms BGTC/BLEC/BGTUC/BLEUC rt, rs, offset (aliases of BLTC/BGEC/BLTUC/BGEUC with the
# registers swapped): each is run taken and not taken; s0 collects one bit per outcome that went the expected way.
# MD00086 Vol II-A Rev 6.06 B<cond>C p.83 ("Assembly idioms with reversed operands for signed/unsigned compare-and-branch:
# BGTC rt, rs, offset ... BLEUC rt, rs, offset"; "BLEC: Compact branch if GPR rt is less than or equal to GPR rs (alias for BGEC)",
# "BGTC: Compact branch if GPR rt is greater than GPR rs (alias for BLTC)", BLEUC/BGTUC likewise unsigned), Operation p.84.
# t0 = -1 (0xffffffff), t1 = 1: signed t1 > t0, unsigned t0 > t1.
# oracle: expect gpr:s0=0xff
.text
li $s0, 0
li $t0, -1
li $t1, 1
bgtc $t1, $t0, a1        # 1 > -1: taken
nop
j fail
nop
a1: ori $s0, $s0, 1
bgtc $t0, $t1, fail      # -1 > 1: not taken
ori $s0, $s0, 2
blec $t0, $t1, a3        # -1 <= 1: taken
nop
j fail
nop
a3: ori $s0, $s0, 4
blec $t1, $t0, fail      # 1 <= -1: not taken
ori $s0, $s0, 8
bgtuc $t0, $t1, a5       # 0xffffffff > 1 unsigned: taken
nop
j fail
nop
a5: ori $s0, $s0, 16
bgtuc $t1, $t0, fail     # 1 > 0xffffffff unsigned: not taken
ori $s0, $s0, 32
bleuc $t1, $t0, a7       # 1 <= 0xffffffff unsigned: taken
nop
j fail
nop
a7: ori $s0, $s0, 64
bleuc $t0, $t1, fail     # 0xffffffff <= 1 unsigned: not taken
ori $s0, $s0, 128
j done
nop
fail: li $s1, 1
done: li $t2, 0
