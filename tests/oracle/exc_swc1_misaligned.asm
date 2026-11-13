# swc1 to a misaligned address: Address Error on store. MD00086 Vol II-A Rev 6.06: SWC1 p.393.
# oracle: expect cause=0x14 badvaddr=0x10010001
.data
w: .word 0, 0
.text
la $t0, w
swc1 $f0, 1($t0)
nop
