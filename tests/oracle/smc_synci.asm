# Self-modifying code with the manual's SYNCI sequence: store a new instruction word over a later
# nop, make it effective (SYNCI, SYNC, JR.HB) and execute it. Writing the instruction stream is
# defined behaviour: SYNCI "is used after a new instruction stream is written to make the new
# instructions effective relative to an instruction fetch" (MD00086 Vol II-A Rev 6.06, SYNCI
# p.412; the sequence synci / sync / jr.hb is the programming note on p.413-414). The patched
# word is addiu $t2, $zero, 7 (0x240a0007); before the patch the slot is a nop, so $t2 = 7 only
# if the fetch sees the store.
# oracle: expect gpr:t2=7
.text
    la    $t0, patch
    li    $t1, 0x240a0007
    sw    $t1, 0($t0)
    synci 0($t0)
    sync
    jr.hb $t0
    nop
    nop
patch:
    nop
    li    $v0, 10
    syscall
