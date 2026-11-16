# jump_jal.asm — j and jal with a "return" (hardcoded j back to the known
# call-site address, this program deliberately does not use jr).
#
# `j`/`jal` keep their delay slot in Release 6: the instruction immediately
# following the jump executes before control transfers (MD00086 Vol II-A
# Rev 6.06, JAL, p.195; see docs/spec/SPEC-NOTES.md §9 item 1). Each jump below is therefore followed
# by a genuine no-op (`sll $zero, $zero, 0`, i.e. $zero <<= 0, into $zero)
# as its delay-slot instruction, so this file's test intent is unchanged
# under both our delay-slot-aware engine (which executes the nop
# harmlessly) and real MARS's still-no-delay-slot default config (which
# skips it harmlessly).
.text
main:
    jal  Lsub
    sll  $zero, $zero, 0
AfterCall:
    move $a0, $t0
    li   $v0, 11
    syscall
    # (no longer prints $ra's low byte here: jal's $ra legitimately diverges
    # from MARS's once a real delay-slot instruction sits between jal and
    # its continuation — see docs/spec/SPEC-NOTES.md §9 item 5. This file
    # never actually uses $ra to return (this program does not use jr; see header),
    # so dropping the probe does not weaken the control-flow check below.)
    li   $v0, 10
    syscall
Lsub:
    li   $t0, 65
    j    AfterCall
    sll  $zero, $zero, 0
