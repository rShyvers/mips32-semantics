# Fixed Mapping MMU, User Mode: a reference to kseg0, kseg1, kseg2 or kseg3 is an Address Error with
# BadVAddr = the virtual address (AdEL for a load or an instruction fetch, AdES for a store), checked
# before translation; useg works. The handler records Cause, BadVAddr and EPC, skips the faulting load or
# store (EPC + 4) and, for the instruction fetch (EPC = BadVAddr), resumes at `fetchback`.
# MD00090 Vol III Rev 6.02 Table 4.2 p.30 (kseg0/kseg1/kseg3/sseg from User Mode: "Address Error");
# sec 6.2.9 p.92-93 ("A reference is made to a kernel address space from User Mode"; AdEL: "load or an
# instruction fetch", AdES: "store"; BadVAddr = "failing address"); Appendix A.1.1 p.313 ("address error
# checking is still done before the translation process. Therefore, an attempt to reference kseg0 from
# User Mode still results in an address error exception"); MD00086 Vol II-A Rev 6.06 LWL p.240-241.
# oracle: expect gpr:s4=6 gpr:s5=77
.data
res: .space 96
.ktext
    mfc0  $k0, $13
    sw    $k0, 0($s7)
    mfc0  $k1, $8
    sw    $k1, 4($s7)
    mfc0  $k0, $14
    sw    $k0, 8($s7)
    addiu $s7, $s7, 12
    addiu $s4, $s4, 1
    bne   $k0, $k1, skip
    nop
    la    $k0, fetchback
    mtc0  $k0, $14
    eret
skip:
    addiu $k0, $k0, 4
    mtc0  $k0, $14
    eret
kfetch:
    nop                          # kseg0 code a User-Mode jump targets
    nop
.text
    la    $s7, res
    li    $s4, 0
    la    $t0, user
    mtc0  $t0, $14
    lui   $t1, 0x2000
    ori   $t1, $t1, 0x12         # CU1, UM = 1, EXL = 1
    mtc0  $t1, $12
    eret                         # to `user` in User Mode
user:
    lui   $t2, 0x8000
    lw    $t3, 0x100($t2)        # kseg0 load: AdEL, BadVAddr 0x8000_0100
    lui   $t2, 0xa000
    sw    $t3, 0x104($t2)        # kseg1 store: AdES, BadVAddr 0xA000_0104
    lui   $t2, 0xc000
    lb    $t3, 3($t2)            # kseg2: AdEL, BadVAddr 0xC000_0003
    lui   $t2, 0xe000
    sh    $t3, 6($t2)            # kseg3: AdES, BadVAddr 0xE000_0006
    lui   $t2, 0x8000
    lwl   $t3, 1($t2)            # unaligned load of kseg0: AdEL, BadVAddr 0x8000_0001
    la    $t5, res               # useg: legal
    li    $t6, 77
    sw    $t6, 92($t5)
    lw    $s5, 92($t5)
    la    $t2, kfetch
    jr    $t2                    # fetch from kseg0: AdEL, EPC = BadVAddr = kfetch
    nop
fetchback:
    addiu $s6, $zero, 1
