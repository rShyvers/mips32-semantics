# Release 6 WAIT with an interrupt request that is pending and not masked out by Status.IM, while interrupts are disabled (Status.IE = 0):
# the processor does not stop (or resumes at once) and, the interrupt not being enabled, continues with the instruction after the WAIT; no
# interrupt is taken. Request: software interrupt SW0 (Cause.IP0 = 1, written by mtc0) with Status.IM0 = 1, IE = 0, EXL = ERL = 0.
# MD00086 Vol II-A Rev 6.06 WAIT p.442-443 (Release 6 Operation: "I: if IsCoprocessorEnabled(0) then while ( !interrupt_pending_and_not_masked_out()
# && !implementation_dependent_wake_event() ) <enter or remain in low power mode or stand-by mode> ... I+1: if ( interrupt_pending() &&
# interrupts_enabled() ) then EPC <- PC + 4 <process interrupt> else // unblock on non-enabled interrupt or imp dep wake event. PC <- PC + 4
# <continue execution at instruction after wait>"; interrupt_pending_and_not_masked_out = CauseIP & StatusIM without EIC; interrupts_enabled =
# StatusIE && !StatusEXL && !StatusERL; Description p.442: "In Release 6, ... a processor that has disabled operation as a result of executing a
# WAIT will resume operation on arrival of an interrupt even if interrupts are not enabled"); MD00090 Vol III Rev 6.02 sec 6.1.1.1 Table 6.2 p.73
# (SW0 = CauseIP0 and StatusIM0), Table 9.52 p.212 (IP1..IP0 R/W). IM2 stays 0: the Malta board raises HW0 on its own.
# s0 = 1 after the wait; the handler would count interrupts in s4 (none). The step budget bounds the model (a standby that never ends hits it).
# oracle: max-steps 200
# oracle: expect gpr:s0=1 gpr:s4=0
.ktext
addiu $s4, $s4, 1
mtc0 $zero, $13
eret
.text
li $s4, 0
li $s0, 0
li $t1, 0x20000100
mtc0 $t1, $12
li $t2, 0x100
mtc0 $t2, $13
ehb
wait
li $s0, 1
mtc0 $zero, $13
lui $t1, 0x2000
mtc0 $t1, $12
li $t1, 0
li $t2, 0
