# Fixed Mapping MMU, Kernel Mode: kseg0 and kseg1 are two virtual windows onto the same low 512 MB of
# physical memory, so a store through one is visible through the other.
# MD00090 Vol III Rev 6.02 sec 4.6 p.30 ("The kseg0 and kseg1 Unmapped Segments provide a window into the
# least significant 2^29 bytes of physical memory"), Table 4.3 p.31 (kseg0 0x8000_0000.. and kseg1
# 0xA000_0000.. both generate physical 0x0000_0000..0x1FFF_FFFF); Appendix A.1.1 p.313 (Fixed Mapping:
# "Kseg0 and Kseg1 addresses ... both map to the low 512MB of physical memory").
# Physical 0x0038_0000 is used: unused by the QEMU harness (scripts/README.md) and by the model's image.
# oracle: expect gpr:s0=0x12345678 gpr:s1=0x12345678 gpr:s2=0xab gpr:s3=0xffffbeef gpr:s4=0xcafe0042
.text
    lui   $t0, 0xa038            # kseg1 0xA038_0000 = physical 0x0038_0000 (uncached)
    lui   $t1, 0x8038            # kseg0 0x8038_0000 = the same physical address
    li    $t2, 0x12345678
    sw    $t2, 0($t0)            # store through kseg1
    lw    $s0, 0($t1)            # load through kseg0
    lw    $s1, 0($t0)            # and back through kseg1
    li    $t3, 0xab
    sb    $t3, 5($t1)            # byte store through kseg0
    lbu   $s2, 5($t0)            # byte load through kseg1
    li    $t4, 0xbeef
    sh    $t4, 8($t0)            # halfword through kseg1
    lh    $s3, 8($t1)            # read through kseg0, sign-extended
    li    $t5, 0xcafe0042
    sw    $t5, 12($t1)           # word through kseg0
    lw    $s4, 12($t0)           # read through kseg1
    sw    $zero, 0($t1)          # leave the location clean
    sw    $zero, 4($t1)
    sw    $zero, 8($t1)
    sw    $zero, 12($t1)
    li    $v0, 10
    syscall
