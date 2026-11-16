# MAX/MIN/MAXA/MINA.fmt with an SNaN operand (MD00086 Vol II-A Rev 6.06 p.262-265): Invalid Operation is signalled (Cause/Flags V), and
# with the exception disabled the SNaN is treated "as if the SNaN were a QNaN (do not quieten the result)" (Table 4.1, p.265): one NaN operand
# gives the numeric operand ("if one input is a NaN, but not both, the value of the numeric input is returned", p.263), two NaNs give fs
# unchanged (p.263). The expected values below are the manual's; QEMU mips32r6-generic follows IEEE 754-2008 minNum/maxNum instead (an SNaN
# operand gives its quieted NaN), declared as deviations (the manual wins).
# oracle: expect mem:0x10010000=0x3f800000 mem:0x10010004=0x000d0040 mem:0x10010008=0x3f800000 mem:0x1001000c=0x000d0040
# oracle: expect mem:0x10010010=0x7f800001 mem:0x10010014=0x000d0040 mem:0x10010018=0x7fc00000 mem:0x1001001c=0x000d0040
# oracle: expect mem:0x10010020=0x3f800000 mem:0x10010024=0x000d0040 mem:0x10010028=0x3f800000 mem:0x1001002c=0x000d0040
# oracle: expect mem:0x10010030=0x7f800001 mem:0x10010034=0x000d0040 mem:0x10010038=0x7fc00000 mem:0x1001003c=0x000d0040
# oracle: expect mem:0x10010040=0x3f800000 mem:0x10010044=0x000d0040 mem:0x10010048=0x3f800000 mem:0x1001004c=0x000d0040
# oracle: expect mem:0x10010050=0x7f800001 mem:0x10010054=0x000d0040 mem:0x10010058=0x7fc00000 mem:0x1001005c=0x000d0040
# oracle: expect mem:0x10010060=0x3f800000 mem:0x10010064=0x000d0040 mem:0x10010068=0x3f800000 mem:0x1001006c=0x000d0040
# oracle: expect mem:0x10010070=0x7f800001 mem:0x10010074=0x000d0040 mem:0x10010078=0x7fc00000 mem:0x1001007c=0x000d0040
# oracle: expect mem:0x10010080=0x00000000 mem:0x10010084=0x3ff00000 mem:0x10010088=0x000d0040 mem:0x1001008c=0x00000000
# oracle: expect mem:0x10010090=0x3ff00000 mem:0x10010094=0x000d0040 mem:0x10010098=0x00000001 mem:0x1001009c=0x7ff00000
# oracle: expect mem:0x100100a0=0x000d0040 mem:0x100100a4=0x00000000 mem:0x100100a8=0x7ff80000 mem:0x100100ac=0x000d0040
# oracle: expect mem:0x100100b0=0x00000000 mem:0x100100b4=0x3ff00000 mem:0x100100b8=0x000d0040 mem:0x100100bc=0x00000000
# oracle: expect mem:0x100100c0=0x3ff00000 mem:0x100100c4=0x000d0040 mem:0x100100c8=0x00000001 mem:0x100100cc=0x7ff00000
# oracle: expect mem:0x100100d0=0x000d0040 mem:0x100100d4=0x00000000 mem:0x100100d8=0x7ff80000 mem:0x100100dc=0x000d0040
# oracle: expect mem:0x100100e0=0x00000000 mem:0x100100e4=0x3ff00000 mem:0x100100e8=0x000d0040 mem:0x100100ec=0x00000000
# oracle: expect mem:0x100100f0=0x3ff00000 mem:0x100100f4=0x000d0040 mem:0x100100f8=0x00000001 mem:0x100100fc=0x7ff00000
# oracle: expect mem:0x10010100=0x000d0040 mem:0x10010104=0x00000000 mem:0x10010108=0x7ff80000 mem:0x1001010c=0x000d0040
# oracle: expect mem:0x10010110=0x00000000 mem:0x10010114=0x3ff00000 mem:0x10010118=0x000d0040 mem:0x1001011c=0x00000000
# oracle: expect mem:0x10010120=0x3ff00000 mem:0x10010124=0x000d0040 mem:0x10010128=0x00000001 mem:0x1001012c=0x7ff00000
# oracle: expect mem:0x10010130=0x000d0040 mem:0x10010134=0x00000000 mem:0x10010138=0x7ff80000 mem:0x1001013c=0x000d0040
# oracle: expect-deviation mem:0x10010000 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010008 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010010 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010018 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010020 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010028 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010030 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010038 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010040 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010048 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010050 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010058 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010060 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010068 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010070 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010078 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010080 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010084 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x1001008c MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010090 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x1001009c MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x100100a4 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x100100a8 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x100100b0 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x100100b4 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x100100bc MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x100100c0 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x100100cc MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x100100d4 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x100100d8 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x100100e0 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x100100e4 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x100100ec MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x100100f0 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x100100fc MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010104 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010108 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010110 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010114 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x1001011c MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010120 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x1001012c MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010134 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation mem:0x10010138 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation gpr:t0 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
# oracle: expect-deviation fpr:f6 MD00086 Vol II-A Rev 6.06 MAX.fmt MIN.fmt MAXA.fmt MINA.fmt p.263 ("if one input is a NaN, but not both, the value of the numeric input is returned. If both are NaNs, the NaN in fs is returned") and Table 4.1 p.265 (SNaN with Invalid disabled: "Treat as if the SNaN were a QNaN (do not quieten the result)"): QEMU returns the quieted SNaN (IEEE 754-2008 minNum/maxNum)
.data
res: .space 320
.text
la $s7, res
li $t9, 0x7f800001
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
max.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 0($s7)
cfc1 $t1, $31
sw $t1, 4($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7f800001
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
max.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 8($s7)
cfc1 $t1, $31
sw $t1, 12($s7)
li $t9, 0x7f800001
mtc1 $t9, $f2
li $t9, 0x7fc00000
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
max.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 16($s7)
cfc1 $t1, $31
sw $t1, 20($s7)
li $t9, 0x7fc00000
mtc1 $t9, $f2
li $t9, 0xff800123
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
max.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 24($s7)
cfc1 $t1, $31
sw $t1, 28($s7)
li $t9, 0x7f800001
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
min.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 32($s7)
cfc1 $t1, $31
sw $t1, 36($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7f800001
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
min.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 40($s7)
cfc1 $t1, $31
sw $t1, 44($s7)
li $t9, 0x7f800001
mtc1 $t9, $f2
li $t9, 0x7fc00000
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
min.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 48($s7)
cfc1 $t1, $31
sw $t1, 52($s7)
li $t9, 0x7fc00000
mtc1 $t9, $f2
li $t9, 0xff800123
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
min.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 56($s7)
cfc1 $t1, $31
sw $t1, 60($s7)
li $t9, 0x7f800001
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
maxa.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 64($s7)
cfc1 $t1, $31
sw $t1, 68($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7f800001
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
maxa.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 72($s7)
cfc1 $t1, $31
sw $t1, 76($s7)
li $t9, 0x7f800001
mtc1 $t9, $f2
li $t9, 0x7fc00000
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
maxa.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 80($s7)
cfc1 $t1, $31
sw $t1, 84($s7)
li $t9, 0x7fc00000
mtc1 $t9, $f2
li $t9, 0xff800123
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
maxa.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 88($s7)
cfc1 $t1, $31
sw $t1, 92($s7)
li $t9, 0x7f800001
mtc1 $t9, $f2
li $t9, 0x3f800000
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
mina.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 96($s7)
cfc1 $t1, $31
sw $t1, 100($s7)
li $t9, 0x3f800000
mtc1 $t9, $f2
li $t9, 0x7f800001
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
mina.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 104($s7)
cfc1 $t1, $31
sw $t1, 108($s7)
li $t9, 0x7f800001
mtc1 $t9, $f2
li $t9, 0x7fc00000
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
mina.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 112($s7)
cfc1 $t1, $31
sw $t1, 116($s7)
li $t9, 0x7fc00000
mtc1 $t9, $f2
li $t9, 0xff800123
mtc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
mina.s $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 120($s7)
cfc1 $t1, $31
sw $t1, 124($s7)
li $t9, 0x00000001
mtc1 $t9, $f2
li $t9, 0x7ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x3ff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
max.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 128($s7)
mfhc1 $t0, $f6
sw $t0, 132($s7)
cfc1 $t1, $31
sw $t1, 136($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mthc1 $t9, $f2
li $t9, 0x00000001
mtc1 $t9, $f4
li $t9, 0x7ff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
max.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 140($s7)
mfhc1 $t0, $f6
sw $t0, 144($s7)
cfc1 $t1, $31
sw $t1, 148($s7)
li $t9, 0x00000001
mtc1 $t9, $f2
li $t9, 0x7ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x7ff80000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
max.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 152($s7)
mfhc1 $t0, $f6
sw $t0, 156($s7)
cfc1 $t1, $31
sw $t1, 160($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x7ff80000
mthc1 $t9, $f2
li $t9, 0x00000123
mtc1 $t9, $f4
li $t9, 0xfff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
max.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 164($s7)
mfhc1 $t0, $f6
sw $t0, 168($s7)
cfc1 $t1, $31
sw $t1, 172($s7)
li $t9, 0x00000001
mtc1 $t9, $f2
li $t9, 0x7ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x3ff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
min.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 176($s7)
mfhc1 $t0, $f6
sw $t0, 180($s7)
cfc1 $t1, $31
sw $t1, 184($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mthc1 $t9, $f2
li $t9, 0x00000001
mtc1 $t9, $f4
li $t9, 0x7ff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
min.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 188($s7)
mfhc1 $t0, $f6
sw $t0, 192($s7)
cfc1 $t1, $31
sw $t1, 196($s7)
li $t9, 0x00000001
mtc1 $t9, $f2
li $t9, 0x7ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x7ff80000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
min.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 200($s7)
mfhc1 $t0, $f6
sw $t0, 204($s7)
cfc1 $t1, $31
sw $t1, 208($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x7ff80000
mthc1 $t9, $f2
li $t9, 0x00000123
mtc1 $t9, $f4
li $t9, 0xfff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
min.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 212($s7)
mfhc1 $t0, $f6
sw $t0, 216($s7)
cfc1 $t1, $31
sw $t1, 220($s7)
li $t9, 0x00000001
mtc1 $t9, $f2
li $t9, 0x7ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x3ff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
maxa.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 224($s7)
mfhc1 $t0, $f6
sw $t0, 228($s7)
cfc1 $t1, $31
sw $t1, 232($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mthc1 $t9, $f2
li $t9, 0x00000001
mtc1 $t9, $f4
li $t9, 0x7ff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
maxa.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 236($s7)
mfhc1 $t0, $f6
sw $t0, 240($s7)
cfc1 $t1, $31
sw $t1, 244($s7)
li $t9, 0x00000001
mtc1 $t9, $f2
li $t9, 0x7ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x7ff80000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
maxa.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 248($s7)
mfhc1 $t0, $f6
sw $t0, 252($s7)
cfc1 $t1, $31
sw $t1, 256($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x7ff80000
mthc1 $t9, $f2
li $t9, 0x00000123
mtc1 $t9, $f4
li $t9, 0xfff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
maxa.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 260($s7)
mfhc1 $t0, $f6
sw $t0, 264($s7)
cfc1 $t1, $31
sw $t1, 268($s7)
li $t9, 0x00000001
mtc1 $t9, $f2
li $t9, 0x7ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x3ff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
mina.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 272($s7)
mfhc1 $t0, $f6
sw $t0, 276($s7)
cfc1 $t1, $31
sw $t1, 280($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x3ff00000
mthc1 $t9, $f2
li $t9, 0x00000001
mtc1 $t9, $f4
li $t9, 0x7ff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
mina.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 284($s7)
mfhc1 $t0, $f6
sw $t0, 288($s7)
cfc1 $t1, $31
sw $t1, 292($s7)
li $t9, 0x00000001
mtc1 $t9, $f2
li $t9, 0x7ff00000
mthc1 $t9, $f2
li $t9, 0x00000000
mtc1 $t9, $f4
li $t9, 0x7ff80000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
mina.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 296($s7)
mfhc1 $t0, $f6
sw $t0, 300($s7)
cfc1 $t1, $31
sw $t1, 304($s7)
li $t9, 0x00000000
mtc1 $t9, $f2
li $t9, 0x7ff80000
mthc1 $t9, $f2
li $t9, 0x00000123
mtc1 $t9, $f4
li $t9, 0xfff00000
mthc1 $t9, $f4
li $t8, 0x00000000
ctc1 $t8, $31
mina.d $f6, $f2, $f4
mfc1 $t0, $f6
sw $t0, 308($s7)
mfhc1 $t0, $f6
sw $t0, 312($s7)
cfc1 $t1, $31
sw $t1, 316($s7)
li $v0, 10
syscall
