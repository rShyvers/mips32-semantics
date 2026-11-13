# A syscall whose $v0 selects no hosted service is the architectural System Call exception, taken
# by the program's own .ktext handler: "A system call exception occurs, immediately and
# unconditionally transferring control to the exception handler. The code field ... may be
# retrieved by the exception handler by loading the contents of the memory word containing the
# instruction" (MD00086 Vol II-A Rev 6.06, SYSCALL p.415). The handler records Cause and EPC,
# loads the syscall word through EPC (the code field 0x123 is bits 25..6), skips it and erets.
# MD00090 Vol III Rev 6.02 sec 9.36 (Cause), 9.37 (EPC); ERET p.177-178 (Vol II-A).
# oracle: expect gpr:s4=0x20 gpr:s3=0x00400004 gpr:s5=0x000048cc gpr:s0=1 gpr:s7=1
.ktext
    mfc0  $k0, $13
    mfc0  $k1, $14
    addiu $s7, $s7, 1
    move  $s4, $k0
    move  $s3, $k1
    lw    $s5, 0($k1)
    addiu $k1, $k1, 4
    mtc0  $k1, $14
    eret
.text
    li    $v0, 99
    syscall 0x123
    li    $s0, 1
    nop
