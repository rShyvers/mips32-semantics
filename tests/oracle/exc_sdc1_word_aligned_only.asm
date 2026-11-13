# sdc1 to a 4-byte-aligned but not 8-byte-aligned address: Address Error on store.
# MD00086 Vol II-A Rev 6.06: SDC1 p.362 ("An Address Error exception occurs if EffectiveAddress2..0 != 0").
# (formerly a known model gap; the model now agrees with the manual and QEMU.)
# oracle: expect cause=0x14 badvaddr=0x10010004
.data
.align 3
w: .word 0, 0, 0, 0
.text
la $t0, w
sdc1 $f0, 4($t0)
nop
