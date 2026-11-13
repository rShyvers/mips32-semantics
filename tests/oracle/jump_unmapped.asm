# jr to an address that holds no code (0x00800000): the model halts no_instruction; QEMU takes a TLB refill on the fetch.
li $t0, 0x00800000
jr $t0
li $s0, 9
