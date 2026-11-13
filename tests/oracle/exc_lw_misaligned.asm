# lw from an address with low bits 01: Address Error on load (ExcCode 4), BadVAddr = effective address,
# destination register unchanged. MD00086 Vol II-A Rev 6.06: LW p.235 (Exceptions: Address Error);
# MD00090 Vol III Rev 6.02 BadVAddr register.
# oracle: expect cause=0x10 badvaddr=0x10010001 gpr:t1=0x1234
.data
w: .word 0, 0
.text
la $t0, w
li $t1, 0x1234
lw $t1, 1($t0)
nop
