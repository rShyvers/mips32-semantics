# ldxc1 at base + 4 (data segment is 8-byte aligned): Address Error, EPC/BadVAddr/Cause compared; unhandled.
# (Doubleword indexed accesses at a word-aligned but not doubleword-aligned address: see the manual page, the model treats ldc1/sdc1 as word-aligned only.)
# MD00086 Vol II-A Rev 6.06: LWXC1 p.254, SWXC1 p.406, LDXC1 p.218, SDXC1 p.364 (Restrictions: 'An Address Error exception occurs if EffectiveAddress1..0 != 0 (not word-aligned)' / 'EffectiveAddress2..0 != 0 (not doubleword-aligned)').
# oracle: expect-deviation term LDXC1: the manual requires Address Error for a misaligned effective address (LDXC1 p.218); QEMU 24Kf performs the access without an exception
# oracle: expect-deviation gpr:s0 LDXC1: the manual requires Address Error for a misaligned effective address (LDXC1 p.218); QEMU 24Kf performs the access without an exception
# oracle: expect-deviation epc LDXC1: the manual requires Address Error for a misaligned effective address (LDXC1 p.218); QEMU 24Kf performs the access without an exception
# oracle: expect-deviation badvaddr LDXC1: the manual requires Address Error for a misaligned effective address (LDXC1 p.218); QEMU 24Kf performs the access without an exception
# oracle: expect-deviation pc LDXC1: the manual requires Address Error for a misaligned effective address (LDXC1 p.218); QEMU 24Kf performs the access without an exception
# oracle: expect-deviation cause LDXC1: the manual requires Address Error for a misaligned effective address (LDXC1 p.218); QEMU 24Kf performs the access without an exception
# oracle: expect-deviation fpr:f2 LDXC1: the manual requires Address Error for a misaligned effective address (LDXC1 p.218); QEMU 24Kf performs the access without an exception
# oracle: expect-deviation fpr:f3 LDXC1: the manual requires Address Error for a misaligned effective address (LDXC1 p.218); QEMU 24Kf performs the access without an exception
.data
.align 3
d: .word 1, 2, 3, 4
res: .space 64
.text
la $t0, d
li $t1, 4
ldxc1 $f2, $t1($t0)
li $s0, 7
