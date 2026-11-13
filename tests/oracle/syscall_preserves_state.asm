# A serviced syscall changes nothing but the output: HI/LO, $k0/$k1, other registers, Cause/EPC (model: untouched).
# oracle: expect gpr:k0=0x1111 gpr:k1=0x2222 hi=0x33 lo=0x44
li $k0, 0x1111
li $k1, 0x2222
li $t0, 0x33
mthi $t0
li $t0, 0x44
mtlo $t0
li $s0, 77
li $v0, 1
li $a0, 5
syscall
li $v0, 11
li $a0, 66
syscall
li $v0, 10
syscall
