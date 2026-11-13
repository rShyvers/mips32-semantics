# ll from a misaligned address: Address Error on load. MD00086 Vol II-A Rev 6.06: LL p.223-224.
# oracle: expect cause=0x10 badvaddr=0x10010002
.data
w: .word 0, 0
.text
la $t0, w
ll $t1, 2($t0)
nop
