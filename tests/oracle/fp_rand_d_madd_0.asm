# Randomised (seeded 600) madd/msub/nmadd/nmsub on .d over edge-value pools and random normals, in all four rounding modes: result bits + FCSR. No NaN operands (payload choice is unspecified).
# MD00082 Vol I-A Rev 6.01 sec 6.7.2 p.99-102, Table 6.14 p.100 (IEEE default results, flags, rounding modes); MD00086 Vol II-A Rev 6.06 ADD/SUB/MUL/DIV/SQRT.fmt, CVT/ROUND/TRUNC/CEIL/FLOOR.
# The model leaves FCSR.Cause of the last operation of the multiply-add (7R, SPEC-NOTES 9.13); QEMU ORs the Causes of all
# steps: every FCSR value below differs from QEMU in Cause bits only (declared).
# oracle: expect-deviation mem:0x10010004 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x10010010 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x1001001c MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x10010028 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x10010034 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x10010040 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x1001004c MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x10010058 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x10010154 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x10010160 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x1001016c MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x10010178 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x100102d4 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x100102e0 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x100102ec MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x100102f8 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x10010334 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x10010340 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x1001034c MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x10010358 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x100103c4 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x100103d0 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x100103dc MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
# oracle: expect-deviation mem:0x100103e8 MD00086 Rev 6.06 MADD.fmt p.256 (MSUB p.287, NMADD p.308, NMSUB p.310): results and flags "as if separate floating-point" operations "were executed", so FCSR.Cause after the instruction is the last operation's (SPEC-NOTES 9.13); QEMU ORs the Cause bits of all steps
.data
res: .space 1600
.text
la $s7, res
li $t9, 0xa1e17d9e
mtc1 $t9, $f2
li $t9, 0x3fe70815
mtc1 $t9, $f3
li $t9, 0x63f9b60d
mtc1 $t9, $f4
li $t9, 0x3ee672b7
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f8
li $t9, 0x80000000
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 0($s7)
sw $t1, 4($s7)
mfc1 $t2, $f7
sw $t2, 8($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 12($s7)
sw $t1, 16($s7)
mfc1 $t2, $f7
sw $t2, 20($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 24($s7)
sw $t1, 28($s7)
mfc1 $t2, $f7
sw $t2, 32($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 36($s7)
sw $t1, 40($s7)
mfc1 $t2, $f7
sw $t2, 44($s7)
li $t9, 0xaf526451
mtc1 $t9, $f2
li $t9, 0x016c29e9
mtc1 $t9, $f3
li $t9, 0x1f00281f
mtc1 $t9, $f4
li $t9, 0xabb2ae03
mtc1 $t9, $f5
li $t9, 0x9999999a
mtc1 $t9, $f8
li $t9, 0x3fb99999
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 48($s7)
sw $t1, 52($s7)
mfc1 $t2, $f7
sw $t2, 56($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 60($s7)
sw $t1, 64($s7)
mfc1 $t2, $f7
sw $t2, 68($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 72($s7)
sw $t1, 76($s7)
mfc1 $t2, $f7
sw $t2, 80($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 84($s7)
sw $t1, 88($s7)
mfc1 $t2, $f7
sw $t2, 92($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x00200000
mtc1 $t9, $f3
li $t9, 0x824a0a05
mtc1 $t9, $f4
li $t9, 0x68420f82
mtc1 $t9, $f5
li $t9, 0x804be93f
mtc1 $t9, $f8
li $t9, 0x403b0020
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 96($s7)
sw $t1, 100($s7)
mfc1 $t2, $f7
sw $t2, 104($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 108($s7)
sw $t1, 112($s7)
mfc1 $t2, $f7
sw $t2, 116($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 120($s7)
sw $t1, 124($s7)
mfc1 $t2, $f7
sw $t2, 128($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 132($s7)
sw $t1, 136($s7)
mfc1 $t2, $f7
sw $t2, 140($s7)
li $t9, 0xffffffff
mtc1 $t9, $f2
li $t9, 0x7fefffff
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x00000000
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f8
li $t9, 0x00000000
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 144($s7)
sw $t1, 148($s7)
mfc1 $t2, $f7
sw $t2, 152($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 156($s7)
sw $t1, 160($s7)
mfc1 $t2, $f7
sw $t2, 164($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 168($s7)
sw $t1, 172($s7)
mfc1 $t2, $f7
sw $t2, 176($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 180($s7)
sw $t1, 184($s7)
mfc1 $t2, $f7
sw $t2, 188($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0xbff00000
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x7ff00000
mtc1 $t9, $f5
li $t9, 0x9999999a
mtc1 $t9, $f8
li $t9, 0x3fb99999
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 192($s7)
sw $t1, 196($s7)
mfc1 $t2, $f7
sw $t2, 200($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 204($s7)
sw $t1, 208($s7)
mfc1 $t2, $f7
sw $t2, 212($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 216($s7)
sw $t1, 220($s7)
mfc1 $t2, $f7
sw $t2, 224($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 228($s7)
sw $t1, 232($s7)
mfc1 $t2, $f7
sw $t2, 236($s7)
li $t9, 0xffffffff
mtc1 $t9, $f2
li $t9, 0x000fffff
mtc1 $t9, $f3
li $t9, 0x9497ef9e
mtc1 $t9, $f4
li $t9, 0xed38de23
mtc1 $t9, $f5
li $t9, 0xffffffff
mtc1 $t9, $f8
li $t9, 0x7fefffff
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 240($s7)
sw $t1, 244($s7)
mfc1 $t2, $f7
sw $t2, 248($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 252($s7)
sw $t1, 256($s7)
mfc1 $t2, $f7
sw $t2, 260($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 264($s7)
sw $t1, 268($s7)
mfc1 $t2, $f7
sw $t2, 272($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 276($s7)
sw $t1, 280($s7)
mfc1 $t2, $f7
sw $t2, 284($s7)
li $t9, 0x701d0851
mtc1 $t9, $f2
li $t9, 0x408c8149
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0xbff00000
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f8
li $t9, 0x00100000
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 288($s7)
sw $t1, 292($s7)
mfc1 $t2, $f7
sw $t2, 296($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 300($s7)
sw $t1, 304($s7)
mfc1 $t2, $f7
sw $t2, 308($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 312($s7)
sw $t1, 316($s7)
mfc1 $t2, $f7
sw $t2, 320($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 324($s7)
sw $t1, 328($s7)
mfc1 $t2, $f7
sw $t2, 332($s7)
li $t9, 0x947c7916
mtc1 $t9, $f2
li $t9, 0x4542de3c
mtc1 $t9, $f3
li $t9, 0xce312cbc
mtc1 $t9, $f4
li $t9, 0x1e1ac5c1
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f8
li $t9, 0x00000000
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 336($s7)
sw $t1, 340($s7)
mfc1 $t2, $f7
sw $t2, 344($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 348($s7)
sw $t1, 352($s7)
mfc1 $t2, $f7
sw $t2, 356($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 360($s7)
sw $t1, 364($s7)
mfc1 $t2, $f7
sw $t2, 368($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 372($s7)
sw $t1, 376($s7)
mfc1 $t2, $f7
sw $t2, 380($s7)
li $t9, 0x95fb8f7b
mtc1 $t9, $f2
li $t9, 0xf74d699d
mtc1 $t9, $f3
li $t9, 0x00000001
mtc1 $t9, $f4
li $t9, 0x00000000
mtc1 $t9, $f5
li $t9, 0xb994d1dd
mtc1 $t9, $f8
li $t9, 0x85b463da
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 384($s7)
sw $t1, 388($s7)
mfc1 $t2, $f7
sw $t2, 392($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 396($s7)
sw $t1, 400($s7)
mfc1 $t2, $f7
sw $t2, 404($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 408($s7)
sw $t1, 412($s7)
mfc1 $t2, $f7
sw $t2, 416($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 420($s7)
sw $t1, 424($s7)
mfc1 $t2, $f7
sw $t2, 428($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x40000000
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0xbff00000
mtc1 $t9, $f5
li $t9, 0xb51ab2e0
mtc1 $t9, $f8
li $t9, 0x687c7c89
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 432($s7)
sw $t1, 436($s7)
mfc1 $t2, $f7
sw $t2, 440($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 444($s7)
sw $t1, 448($s7)
mfc1 $t2, $f7
sw $t2, 452($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 456($s7)
sw $t1, 460($s7)
mfc1 $t2, $f7
sw $t2, 464($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 468($s7)
sw $t1, 472($s7)
mfc1 $t2, $f7
sw $t2, 476($s7)
li $t9, 0x45fe76ec
mtc1 $t9, $f2
li $t9, 0x945f6c1f
mtc1 $t9, $f3
li $t9, 0xeeabb2e3
mtc1 $t9, $f4
li $t9, 0x30b4f083
mtc1 $t9, $f5
li $t9, 0xbec5602c
mtc1 $t9, $f8
li $t9, 0xa6d60dda
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 480($s7)
sw $t1, 484($s7)
mfc1 $t2, $f7
sw $t2, 488($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 492($s7)
sw $t1, 496($s7)
mfc1 $t2, $f7
sw $t2, 500($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 504($s7)
sw $t1, 508($s7)
mfc1 $t2, $f7
sw $t2, 512($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 516($s7)
sw $t1, 520($s7)
mfc1 $t2, $f7
sw $t2, 524($s7)
li $t9, 0x7c0d61f2
mtc1 $t9, $f2
li $t9, 0xa706b2f2
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0xfff00000
mtc1 $t9, $f5
li $t9, 0xdf146f73
mtc1 $t9, $f8
li $t9, 0xbf3c41e5
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 528($s7)
sw $t1, 532($s7)
mfc1 $t2, $f7
sw $t2, 536($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 540($s7)
sw $t1, 544($s7)
mfc1 $t2, $f7
sw $t2, 548($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 552($s7)
sw $t1, 556($s7)
mfc1 $t2, $f7
sw $t2, 560($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 564($s7)
sw $t1, 568($s7)
mfc1 $t2, $f7
sw $t2, 572($s7)
li $t9, 0xc408d8ea
mtc1 $t9, $f2
li $t9, 0xbedcfef9
mtc1 $t9, $f3
li $t9, 0xef12d438
mtc1 $t9, $f4
li $t9, 0x3f673eb6
mtc1 $t9, $f5
li $t9, 0x134959cc
mtc1 $t9, $f8
li $t9, 0xc166f25a
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 576($s7)
sw $t1, 580($s7)
mfc1 $t2, $f7
sw $t2, 584($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 588($s7)
sw $t1, 592($s7)
mfc1 $t2, $f7
sw $t2, 596($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 600($s7)
sw $t1, 604($s7)
mfc1 $t2, $f7
sw $t2, 608($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 612($s7)
sw $t1, 616($s7)
mfc1 $t2, $f7
sw $t2, 620($s7)
li $t9, 0xe62f5cd6
mtc1 $t9, $f2
li $t9, 0x41640c6d
mtc1 $t9, $f3
li $t9, 0x695de42f
mtc1 $t9, $f4
li $t9, 0x3f56719c
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f8
li $t9, 0x7fd00000
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 624($s7)
sw $t1, 628($s7)
mfc1 $t2, $f7
sw $t2, 632($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 636($s7)
sw $t1, 640($s7)
mfc1 $t2, $f7
sw $t2, 644($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 648($s7)
sw $t1, 652($s7)
mfc1 $t2, $f7
sw $t2, 656($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 660($s7)
sw $t1, 664($s7)
mfc1 $t2, $f7
sw $t2, 668($s7)
li $t9, 0x702fee84
mtc1 $t9, $f2
li $t9, 0xc16796a2
mtc1 $t9, $f3
li $t9, 0x89363ca0
mtc1 $t9, $f4
li $t9, 0x40e6dd03
mtc1 $t9, $f5
li $t9, 0x00000001
mtc1 $t9, $f8
li $t9, 0x00100000
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 672($s7)
sw $t1, 676($s7)
mfc1 $t2, $f7
sw $t2, 680($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 684($s7)
sw $t1, 688($s7)
mfc1 $t2, $f7
sw $t2, 692($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 696($s7)
sw $t1, 700($s7)
mfc1 $t2, $f7
sw $t2, 704($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 708($s7)
sw $t1, 712($s7)
mfc1 $t2, $f7
sw $t2, 716($s7)
li $t9, 0x5ceb6850
mtc1 $t9, $f2
li $t9, 0x3e95680f
mtc1 $t9, $f3
li $t9, 0x1c660178
mtc1 $t9, $f4
li $t9, 0xc180226b
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f8
li $t9, 0x3ff00000
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 720($s7)
sw $t1, 724($s7)
mfc1 $t2, $f7
sw $t2, 728($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 732($s7)
sw $t1, 736($s7)
mfc1 $t2, $f7
sw $t2, 740($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 744($s7)
sw $t1, 748($s7)
mfc1 $t2, $f7
sw $t2, 752($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 756($s7)
sw $t1, 760($s7)
mfc1 $t2, $f7
sw $t2, 764($s7)
li $t9, 0xb689a0d0
mtc1 $t9, $f2
li $t9, 0x3f297b45
mtc1 $t9, $f3
li $t9, 0xb1e74bea
mtc1 $t9, $f4
li $t9, 0xbefcef7b
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f8
li $t9, 0x00100000
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 768($s7)
sw $t1, 772($s7)
mfc1 $t2, $f7
sw $t2, 776($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 780($s7)
sw $t1, 784($s7)
mfc1 $t2, $f7
sw $t2, 788($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 792($s7)
sw $t1, 796($s7)
mfc1 $t2, $f7
sw $t2, 800($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 804($s7)
sw $t1, 808($s7)
mfc1 $t2, $f7
sw $t2, 812($s7)
li $t9, 0xffffffff
mtc1 $t9, $f2
li $t9, 0x000fffff
mtc1 $t9, $f3
li $t9, 0x23e5bc9e
mtc1 $t9, $f4
li $t9, 0x40ee444a
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f8
li $t9, 0x00100000
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 816($s7)
sw $t1, 820($s7)
mfc1 $t2, $f7
sw $t2, 824($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 828($s7)
sw $t1, 832($s7)
mfc1 $t2, $f7
sw $t2, 836($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 840($s7)
sw $t1, 844($s7)
mfc1 $t2, $f7
sw $t2, 848($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 852($s7)
sw $t1, 856($s7)
mfc1 $t2, $f7
sw $t2, 860($s7)
li $t9, 0xf067b87e
mtc1 $t9, $f2
li $t9, 0xbf8696c2
mtc1 $t9, $f3
li $t9, 0x53601140
mtc1 $t9, $f4
li $t9, 0x261d325c
mtc1 $t9, $f5
li $t9, 0xffffffff
mtc1 $t9, $f8
li $t9, 0x000fffff
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 864($s7)
sw $t1, 868($s7)
mfc1 $t2, $f7
sw $t2, 872($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 876($s7)
sw $t1, 880($s7)
mfc1 $t2, $f7
sw $t2, 884($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 888($s7)
sw $t1, 892($s7)
mfc1 $t2, $f7
sw $t2, 896($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 900($s7)
sw $t1, 904($s7)
mfc1 $t2, $f7
sw $t2, 908($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0xfff00000
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x7ff00000
mtc1 $t9, $f5
li $t9, 0x70aed972
mtc1 $t9, $f8
li $t9, 0x40d07b59
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 912($s7)
sw $t1, 916($s7)
mfc1 $t2, $f7
sw $t2, 920($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 924($s7)
sw $t1, 928($s7)
mfc1 $t2, $f7
sw $t2, 932($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 936($s7)
sw $t1, 940($s7)
mfc1 $t2, $f7
sw $t2, 944($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 948($s7)
sw $t1, 952($s7)
mfc1 $t2, $f7
sw $t2, 956($s7)
li $t9, 0x2ee37313
mtc1 $t9, $f2
li $t9, 0x3f33713c
mtc1 $t9, $f3
li $t9, 0x00000001
mtc1 $t9, $f4
li $t9, 0x00000000
mtc1 $t9, $f5
li $t9, 0x047f5c6c
mtc1 $t9, $f8
li $t9, 0xaee25b89
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 960($s7)
sw $t1, 964($s7)
mfc1 $t2, $f7
sw $t2, 968($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 972($s7)
sw $t1, 976($s7)
mfc1 $t2, $f7
sw $t2, 980($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 984($s7)
sw $t1, 988($s7)
mfc1 $t2, $f7
sw $t2, 992($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 996($s7)
sw $t1, 1000($s7)
mfc1 $t2, $f7
sw $t2, 1004($s7)
li $t9, 0x91e1be0f
mtc1 $t9, $f2
li $t9, 0x4172ebee
mtc1 $t9, $f3
li $t9, 0xd84f6e01
mtc1 $t9, $f4
li $t9, 0xc0148dc5
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f8
li $t9, 0x00100000
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1008($s7)
sw $t1, 1012($s7)
mfc1 $t2, $f7
sw $t2, 1016($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1020($s7)
sw $t1, 1024($s7)
mfc1 $t2, $f7
sw $t2, 1028($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1032($s7)
sw $t1, 1036($s7)
mfc1 $t2, $f7
sw $t2, 1040($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1044($s7)
sw $t1, 1048($s7)
mfc1 $t2, $f7
sw $t2, 1052($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x80000000
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x3fe00000
mtc1 $t9, $f5
li $t9, 0x28e31e92
mtc1 $t9, $f8
li $t9, 0x40833fc3
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1056($s7)
sw $t1, 1060($s7)
mfc1 $t2, $f7
sw $t2, 1064($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1068($s7)
sw $t1, 1072($s7)
mfc1 $t2, $f7
sw $t2, 1076($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1080($s7)
sw $t1, 1084($s7)
mfc1 $t2, $f7
sw $t2, 1088($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1092($s7)
sw $t1, 1096($s7)
mfc1 $t2, $f7
sw $t2, 1100($s7)
li $t9, 0x3619e15f
mtc1 $t9, $f2
li $t9, 0xc15d5d68
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x00200000
mtc1 $t9, $f5
li $t9, 0xc8e7b8a6
mtc1 $t9, $f8
li $t9, 0xc0379dbe
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1104($s7)
sw $t1, 1108($s7)
mfc1 $t2, $f7
sw $t2, 1112($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1116($s7)
sw $t1, 1120($s7)
mfc1 $t2, $f7
sw $t2, 1124($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1128($s7)
sw $t1, 1132($s7)
mfc1 $t2, $f7
sw $t2, 1136($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1140($s7)
sw $t1, 1144($s7)
mfc1 $t2, $f7
sw $t2, 1148($s7)
li $t9, 0xf2873416
mtc1 $t9, $f2
li $t9, 0x3f8679ca
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x00000000
mtc1 $t9, $f5
li $t9, 0x8483971a
mtc1 $t9, $f8
li $t9, 0x3f54e306
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1152($s7)
sw $t1, 1156($s7)
mfc1 $t2, $f7
sw $t2, 1160($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1164($s7)
sw $t1, 1168($s7)
mfc1 $t2, $f7
sw $t2, 1172($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1176($s7)
sw $t1, 1180($s7)
mfc1 $t2, $f7
sw $t2, 1184($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1188($s7)
sw $t1, 1192($s7)
mfc1 $t2, $f7
sw $t2, 1196($s7)
li $t9, 0x2e7ad751
mtc1 $t9, $f2
li $t9, 0xc15b8168
mtc1 $t9, $f3
li $t9, 0x5d1b2d61
mtc1 $t9, $f4
li $t9, 0xf0fa2f31
mtc1 $t9, $f5
li $t9, 0x8586841e
mtc1 $t9, $f8
li $t9, 0xbfba9470
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1200($s7)
sw $t1, 1204($s7)
mfc1 $t2, $f7
sw $t2, 1208($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1212($s7)
sw $t1, 1216($s7)
mfc1 $t2, $f7
sw $t2, 1220($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1224($s7)
sw $t1, 1228($s7)
mfc1 $t2, $f7
sw $t2, 1232($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1236($s7)
sw $t1, 1240($s7)
mfc1 $t2, $f7
sw $t2, 1244($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0xfff00000
mtc1 $t9, $f3
li $t9, 0xc2cd0505
mtc1 $t9, $f4
li $t9, 0x3e9eb508
mtc1 $t9, $f5
li $t9, 0x6ec9f432
mtc1 $t9, $f8
li $t9, 0x8de6451c
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1248($s7)
sw $t1, 1252($s7)
mfc1 $t2, $f7
sw $t2, 1256($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1260($s7)
sw $t1, 1264($s7)
mfc1 $t2, $f7
sw $t2, 1268($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1272($s7)
sw $t1, 1276($s7)
mfc1 $t2, $f7
sw $t2, 1280($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1284($s7)
sw $t1, 1288($s7)
mfc1 $t2, $f7
sw $t2, 1292($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3fe00000
mtc1 $t9, $f3
li $t9, 0x9999999a
mtc1 $t9, $f4
li $t9, 0x3fb99999
mtc1 $t9, $f5
li $t9, 0x14213751
mtc1 $t9, $f8
li $t9, 0xc185ee1f
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1296($s7)
sw $t1, 1300($s7)
mfc1 $t2, $f7
sw $t2, 1304($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1308($s7)
sw $t1, 1312($s7)
mfc1 $t2, $f7
sw $t2, 1316($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1320($s7)
sw $t1, 1324($s7)
mfc1 $t2, $f7
sw $t2, 1328($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1332($s7)
sw $t1, 1336($s7)
mfc1 $t2, $f7
sw $t2, 1340($s7)
li $t9, 0xffffffff
mtc1 $t9, $f2
li $t9, 0x000fffff
mtc1 $t9, $f3
li $t9, 0x9de3c23e
mtc1 $t9, $f4
li $t9, 0xd295d20e
mtc1 $t9, $f5
li $t9, 0x00000001
mtc1 $t9, $f8
li $t9, 0x00000000
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1344($s7)
sw $t1, 1348($s7)
mfc1 $t2, $f7
sw $t2, 1352($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1356($s7)
sw $t1, 1360($s7)
mfc1 $t2, $f7
sw $t2, 1364($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1368($s7)
sw $t1, 1372($s7)
mfc1 $t2, $f7
sw $t2, 1376($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1380($s7)
sw $t1, 1384($s7)
mfc1 $t2, $f7
sw $t2, 1388($s7)
li $t9, 0x7d2c89e9
mtc1 $t9, $f2
li $t9, 0x3fa183c6
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x3ff00000
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f8
li $t9, 0x00200000
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1392($s7)
sw $t1, 1396($s7)
mfc1 $t2, $f7
sw $t2, 1400($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1404($s7)
sw $t1, 1408($s7)
mfc1 $t2, $f7
sw $t2, 1412($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1416($s7)
sw $t1, 1420($s7)
mfc1 $t2, $f7
sw $t2, 1424($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1428($s7)
sw $t1, 1432($s7)
mfc1 $t2, $f7
sw $t2, 1436($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x7ff00000
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0xbff00000
mtc1 $t9, $f5
li $t9, 0xffffffff
mtc1 $t9, $f8
li $t9, 0x000fffff
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1440($s7)
sw $t1, 1444($s7)
mfc1 $t2, $f7
sw $t2, 1448($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1452($s7)
sw $t1, 1456($s7)
mfc1 $t2, $f7
sw $t2, 1460($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1464($s7)
sw $t1, 1468($s7)
mfc1 $t2, $f7
sw $t2, 1472($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1476($s7)
sw $t1, 1480($s7)
mfc1 $t2, $f7
sw $t2, 1484($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3fe00000
mtc1 $t9, $f3
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x7fd00000
mtc1 $t9, $f5
li $t9, 0x00000000
mtc1 $t9, $f8
li $t9, 0x3ca00000
mtc1 $t9, $f9
li $t8, 0
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1488($s7)
sw $t1, 1492($s7)
mfc1 $t2, $f7
sw $t2, 1496($s7)
li $t8, 1
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1500($s7)
sw $t1, 1504($s7)
mfc1 $t2, $f7
sw $t2, 1508($s7)
li $t8, 2
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1512($s7)
sw $t1, 1516($s7)
mfc1 $t2, $f7
sw $t2, 1520($s7)
li $t8, 3
ctc1 $t8, $31
madd.d $f6, $f8, $f2, $f4
mfc1 $t0, $f6
cfc1 $t1, $31
sw $t0, 1524($s7)
sw $t1, 1528($s7)
mfc1 $t2, $f7
sw $t2, 1532($s7)
li $v0, 10
syscall
