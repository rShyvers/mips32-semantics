# li/la pseudo-instructions across the immediate range (value semantics only; encodings are checked by --encodings).
# oracle: expect gpr:s0=0 gpr:s1=65535 gpr:s2=0xffffffff gpr:s3=0xffff8000 gpr:s4=0x10000 gpr:s5=0x12345678 gpr:s6=0x80000000
.data
a: .word 1
b: .word 2
.text
li $s0, 0
li $s1, 65535
li $s2, -1
li $s3, -32768
li $s4, 65536
li $s5, 0x12345678
li $s6, 0x80000000
la $t0, b
la $t1, a
subu $s7, $t0, $t1
li $v0, 10
syscall
