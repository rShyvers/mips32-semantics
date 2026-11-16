# A control transfer in the forbidden slot of a compact branch. MD00086 Vol II-A Rev 6.06, B<cond>C,
# Restrictions, p.84: "If a control transfer instruction (CTI) is placed in the forbidden slot of a compact
# branch, Release 6 implementations are required to signal a Reserved Instruction exception, but only when
# the branch is not taken"; MD00082 Vol I-A Rev 6.01 sec 5.3.2.4.4, p.63 (forbidden slot only if not taken)
# and 5.3.2.4.3 (BC has no forbidden slot). The handler counts in $s7, records ExcCode history in $s6 and
# resumes at EPC + 8 when Cause.BD = 1 (the slot after the branch), else EPC + 4.
#   1. bnezc not taken, then `bc`: Reserved Instruction (ExcCode 10).
#   2. bgezc taken over an adjacent bltzc: no exception (the bltzc is never in a slot).
#   3. the same bltzc reached by a jump (not after a branch): it executes, no exception.
#   4. bc (no forbidden slot) to a label directly followed by a CTI: no exception.
# Where the exception is reported (EPC, Cause.BD) is compared in exc_forbidden_slot.asm; here only
# the count, the ExcCode and the control flow.
# oracle: expect gpr:s7=1 gpr:s6=10 gpr:s0=0x0f
.ktext
mfc0 $k0, $13
mfc0 $k1, $14
addiu $s7, $s7, 1
sll $s6, $s6, 8
srl $t9, $k0, 2
andi $t9, $t9, 31
or $s6, $s6, $t9
bltz $k0, bd
nop
addiu $k1, $k1, 4
mtc0 $k1, $14
eret
bd: addiu $k1, $k1, 8
mtc0 $k1, $14
eret
.text
li $s0, 0
li $t0, 0
li $t1, 1
bnezc $t0, x1              # not taken: the next instruction is in the forbidden slot
bc x1                      # CTI in the forbidden slot: Reserved Instruction
ori $s0, $s0, 1            # the handler resumes here
x1: bgezc $t1, x2          # taken: the adjacent bltzc is not in a forbidden slot
y1: bltzc $t1, y2          # reached by a jump below: executes normally (not taken)
ori $s0, $s0, 4            # its forbidden slot: an ordinary instruction
bc x5                      # not in a slot (after the ori): executes
x2: ori $s0, $s0, 2
j y1
nop
y2: ori $s7, $s7, 0x100    # never reached
x5: bc x6                  # BC: no forbidden slot
x6: bc x7                  # executed after a taken BC, not in a slot
x7: ori $s0, $s0, 8
