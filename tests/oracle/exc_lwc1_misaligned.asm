# lwc1 from a misaligned address: Address Error on load. MD00086 Vol II-A Rev 6.06: LWC1 p.236.
# oracle: expect cause=0x10 badvaddr=0x10010002
.data
w: .word 0, 0
.text
la $t0, w
lwc1 $f0, 2($t0)
nop
