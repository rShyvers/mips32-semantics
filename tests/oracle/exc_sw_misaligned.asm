# sw to an address with low bits 10: Address Error on store (ExcCode 5), BadVAddr = address, memory unchanged.
# MD00086 Vol II-A Rev 6.06: SW p.392.
# oracle: expect cause=0x14 badvaddr=0x10010002
.data
w: .word 0, 0
.text
la $t0, w
li $t1, 0x1234
sw $t1, 2($t0)
nop
