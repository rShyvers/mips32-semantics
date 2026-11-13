# Fixed Mapping MMU: with Status.ERL = 1 kuseg is unmapped (identity), so kuseg 0x0038_0000 is physical
# 0x0038_0000, the location kseg0 0x8038_0000 and kseg1 0xA038_0000 name.
# MD00090 Vol III Rev 6.02 sec 4.7 p.31 ("the kuseg Segment becomes an unmapped, uncached Segment, similar to
# the kseg1 Segment, if the ERL bit is set in the Status register"); Table 4.2 p.30 (kuseg in Kernel Mode:
# "Unmapped if StatusERL=1"); Appendix A.1.1 p.313 / Table A.1 p.313 (kuseg: identity when ERL = 1).
# The ERL = 1 window runs from kseg0 (.ktext): executing from kuseg with ERL = 1 is UNDEFINED (A.1.2 p.316).
# QEMU's kuseg is TLB-mapped while ERL = 0, so only the ERL = 1 identity map and kseg0/kseg1 are compared.
# oracle: expect gpr:s1=0x5a5a1234 gpr:s2=0x5a5a1234 gpr:s3=0x5a5a1234 gpr:s5=0
.ktext
erlwin:
    mfc0  $t0, $12
    ori   $t1, $t0, 4            # Status.ERL = 1 (Kernel Mode, kuseg unmapped)
    mtc0  $t1, $12
    ehb
    lui   $t2, 0x0038            # kuseg 0x0038_0000 = physical 0x0038_0000 while ERL = 1
    sw    $s0, 0($t2)
    lw    $s1, 0($t2)
    mtc0  $t0, $12               # Status.ERL = 0 again
    ehb
    jr    $ra
    nop
.text
    li    $s0, 0x5a5a1234
    la    $t9, erlwin
    jalr  $t9
    nop
    lui   $t3, 0x8038
    lw    $s2, 0($t3)            # kseg0 view of the same physical word
    lui   $t3, 0xa038
    lw    $s3, 0($t3)            # kseg1 view
    sw    $zero, 0($t3)          # leave the location clean
    lw    $s5, 0($t3)
