# Data layout of .byte/.half/.word/.asciiz/.space/.align/.float/.double (big-endian) as seen through memory.
# The final-memory comparison checks every nonzero word of the data pages.
# oracle: expect mem:0x10010000=0x01020304 mem:0x10010004=0x05060708 mem:0x10010008=0x12345678 mem:0x1001000c=0x68690000
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
