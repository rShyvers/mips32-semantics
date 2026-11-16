# Exceptions WITH a handler in .ktext (0x80000180): ov, break, trap, address errors, syscall(unserviced), RI;
# the handler records Cause/EPC/BadVAddr (mfc0), skips the instruction (EPC += 4) and erets.
# MD00086 Vol II-A Rev 6.06: ERET p.177-178, MFC0 p.266, MTC0 p.290-291; MD00090 Vol III Rev 6.02 sec 9.36 Cause, 9.37 EPC.
# ExcCode history in $s6, one byte per exception: 12(ov) 9(bp) 13(tr) 4(AdEL) 8(sys) 10(RI) => 0x0c090d04080a (low 32 bits 0x0d04080a), the
# count $s7 = 6; the AdEL is a misaligned LL (always Address Error in Release 6: MD00082 Vol I-A Rev 6.01 App. B.2 p.128,
# "misalignment support is NOT provided for the load-linked/store conditional instructions"; ordinary misaligned loads/stores
# may be done in hardware, exc_lw_misaligned); the program runs off its end afterwards (the default exit syscall would itself reach the handler).
# oracle: expect gpr:s7=6 gpr:s6=0x0d04080a
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
add $t1, $t0, $t0        # Integer Overflow
break                    # Breakpoint
teq $zero, $zero         # Trap
li $t2, 0x10010000
ll $t3, 1($t2)           # AdEL
li $v0, 0
syscall                  # Syscall exception (v0 = 0 is not an environment call)
.word 0x00000028         # Reserved Instruction
move $s0, $s3            # last EPC seen
move $s1, $s4            # last Cause seen
nop
