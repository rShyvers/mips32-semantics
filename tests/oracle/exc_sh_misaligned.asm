# sh to an odd address: Address Error on store. MD00086 Vol II-A Rev 6.06: SH p.373.
# oracle: expect cause=0x14 badvaddr=0x10010001
.data
w: .word 0, 0
.text
la $t0, w
li $t1, 0x4321
sh $t1, 1($t0)
nop
