# `.ktext` / `.kdata`: an exception handler assembled at the exception vector
# (0x80000180). `teq` traps into it; the handler prints the kernel-data
# string and exits. Not a MARS differential test: MARS 4.5 rejects the
# three-operand `teq rs, rt, code` form used below.
# Expected output: "trap"
        .kdata
msg:    .asciiz "trap"
        .ktext
handler:
        mfc0 $k0, $13              # Cause (standard `$N` coprocessor operand)
        lui  $a0, 0x9000           # address of msg (0x90000000)
        li   $v0, 4
        syscall
        li   $v0, 10
        syscall
        .text
        .globl main
main:   li   $t0, 1
        teq  $zero, $zero, 0       # code operand: only 0 is representable
        li   $a0, '!'              # not reached
        li   $v0, 11
        syscall
        li   $v0, 10
        syscall
