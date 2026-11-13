# break in the delay slot of jr: EPC = the jr, BD = 1. MD00086 Vol II-A Rev 6.06: BREAK p.109, JR p.206-207.
# oracle: expect cause=0x80000024 epc=0x00400008
la $t0, tgt               # lui/ori: 0x00400000, 0x00400004
jr $t0                    # 0x00400008
break
nop
tgt: nop
