# Config.K0 (bits 2..0) is Read/Write: write each of the legal attribute values and read it back; the other Config bits are not written.
# MD00090 Vol III Rev 6.02 Table 9.64 p.235 (K0 "R/W", "Required"); Table 9.12 p.133: 2 Uncached and 3 Cacheable are "Required" (the others "Optional").
# Only the two required encodings are written (an unsupported attribute is not specified before Release 6); K0 is restored to 2 before exit.
# oracle: unpredictable gpr:s0 MD00090 Vol III Rev 6.02 Config: reset state of K0 is "Undefined" (the model resets it to 2)
# oracle: expect gpr:s1=3 gpr:s2=2 gpr:s3=1
# oracle: unpredictable gpr:t1 MD00090 Vol III Rev 6.02 Config: only BE/AT/AR and the written K0 are fixed (checked in s1..s3); the rest of the register is implementation-defined (QEMU sets Impl bit 7)
.text
mfc0 $s0, $16
andi $s0, $s0, 7
li $t0, 3
mtc0 $t0, $16
mfc0 $s1, $16
andi $s1, $s1, 7
li $t0, 2
mtc0 $t0, $16
mfc0 $s2, $16
andi $s2, $s2, 7
mfc0 $t1, $16
srl $s3, $t1, 15
andi $s3, $s3, 1
li $v0, 10
syscall
