# Bare machine: without the hosted environment, syscall service 11 (print char) is just a System
# Call exception (MD00086 Vol II-A Rev 6.06, SYSCALL p.415); the program's own .ktext handler
# implements the service by appending $a0's low byte to a buffer, then resumes after the syscall
# (EPC + 4; ERET p.177-178). The model runs with MipsRun --bare (no hosted services); QEMU has no
# default handler because the test brings its own.
# oracle: bare
# oracle: expect mem:0x10010000=0x48690000 gpr:s7=0x10010002
.data
buf: .word 0, 0
.ktext
    li    $k0, 11
    bne   $v0, $k0, done
    nop
    sb    $a0, 0($s7)
    addiu $s7, $s7, 1
done:
    mfc0  $k1, $14
    addiu $k1, $k1, 4
    mtc0  $k1, $14
    eret
.text
    la    $s7, buf
    li    $v0, 11
    li    $a0, 72
    syscall
    li    $a0, 105
    syscall
    nop
