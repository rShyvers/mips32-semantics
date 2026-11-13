# Environment-call convention (model = MARS/SPIM services; the QEMU harness emulates them): print int (1),
# string (4), char (11), exit (10). Includes INT_MIN, negative, zero. Not an architectural feature (Step.lean
# "Environment calls"); MD00086 SYSCALL p.415 only defines the exception.
.data
msg: .asciiz "hello\n"
.text
li $v0, 1
li $a0, 0
syscall
li $v0, 11
li $a0, 32
syscall
li $v0, 1
li $a0, -2147483648
syscall
li $v0, 11
li $a0, 10
syscall
li $v0, 1
li $a0, 12345
syscall
li $v0, 4
la $a0, msg
syscall
li $v0, 1
li $a0, -7
syscall
li $v0, 11
li $a0, 0x141              # only the low byte (0x41 'A') is printed
syscall
li $v0, 10
syscall
