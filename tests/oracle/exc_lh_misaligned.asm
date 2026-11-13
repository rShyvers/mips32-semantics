# lh from an odd address: Address Error on load. MD00086 Vol II-A Rev 6.06: LH p.219.
# oracle: expect cause=0x10 badvaddr=0x10010003
.data
w: .word 0, 0
.text
la $t0, w
lh $t1, 3($t0)
nop
