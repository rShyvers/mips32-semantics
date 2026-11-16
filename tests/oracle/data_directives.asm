# Data layout of .byte/.half/.word/.asciiz/.space/.align/.float/.double (little-endian: byte k of a datum at address a+k holds
# bits 8k+7..8k; the .double -2.0 = 0xc0000000_00000000 has its low word first) as seen through memory.
# The final-memory comparison checks every nonzero word of the data pages.
# oracle: expect mem:0x10010000=0x04030201 mem:0x10010004=0x07080605 mem:0x10010008=0x12345678 mem:0x1001000c=0x00006968
# oracle: expect mem:0x10010018=0x00000000 mem:0x1001001c=0xc0000000 gpr:s0=0 gpr:s1=0xc0000000
# oracle: known-model-bug fpr:f3 MD00090 Vol III Rev 6.02 sec 9.32 Table 9.47 p.191 (Status.FR read-only in Release 6, FR = 1 required with a 64-bit FPU) and DECISIONS D2: W5: the model's ldc1 still fills the even/odd pair (f3 = high word); QEMU (FR = 1) leaves FPR 3 alone
.data
b: .byte 1, 2, 3, 4, 5, 6
.half 0x0708
.align 2
w: .word 0x12345678
s: .asciiz "hi"
.align 2
f: .float 1.5
.align 3
d: .double -2.0
sp: .space 8
e: .word 0xdeadbeef
.text
la $t0, f
lwc1 $f0, 0($t0)
la $t0, d
ldc1 $f2, 0($t0)
lw $s0, 0($t0)
lw $s1, 4($t0)
li $v0, 10
syscall
