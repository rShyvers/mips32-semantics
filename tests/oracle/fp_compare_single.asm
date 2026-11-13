# c.cond.s (f un eq ueq olt ult ole ule) with a<b (0:1.0 1:2.0), equal operands, and a quiet NaN (2: 0x7fc00000)
# -- bc1f/bc1t read the condition (cc0).  Per register $s0..$s7 (one per condition) bit0: a?b, bit1: b?a, bit2: a?a,
# bit3: a?NaN, bit4: NaN?NaN.  MD00086 Vol II-A Rev 6.06: C.cond.fmt p.110-113, BC1F p.56-57, BC1T p.60-61.
# Expected (manual truth table, a=1<b=2, NaN unordered): f: 0 | un: 8|16 | eq: 4 | ueq: 4|8|16 | olt: 1 | ult: 1|8|16 |
# ole: 1|4 | ule: 1|4|8|16.
# oracle: expect gpr:s0=0 gpr:s1=0x18 gpr:s2=4 gpr:s3=0x1c gpr:s4=1 gpr:s5=0x19 gpr:s6=5 gpr:s7=0x1d
li $t9, 0x3f800000
mtc1 $t9, $f0
li $t9, 0x40000000
mtc1 $t9, $f1
li $t9, 0x7fc00000
mtc1 $t9, $f2
c.f.s $f0, $f1
bc1f Ls0_0
nop
ori $s0, $s0, 1
Ls0_0: nop
c.f.s $f1, $f0
bc1f Ls0_1
nop
ori $s0, $s0, 2
Ls0_1: nop
c.f.s $f0, $f0
bc1f Ls0_2
nop
ori $s0, $s0, 4
Ls0_2: nop
c.f.s $f0, $f2
bc1f Ls0_3
nop
ori $s0, $s0, 8
Ls0_3: nop
c.f.s $f2, $f2
bc1f Ls0_4
nop
ori $s0, $s0, 16
Ls0_4: nop
c.un.s $f0, $f1
bc1f Ls1_0
nop
ori $s1, $s1, 1
Ls1_0: nop
c.un.s $f1, $f0
bc1f Ls1_1
nop
ori $s1, $s1, 2
Ls1_1: nop
c.un.s $f0, $f0
bc1f Ls1_2
nop
ori $s1, $s1, 4
Ls1_2: nop
c.un.s $f0, $f2
bc1f Ls1_3
nop
ori $s1, $s1, 8
Ls1_3: nop
c.un.s $f2, $f2
bc1f Ls1_4
nop
ori $s1, $s1, 16
Ls1_4: nop
c.eq.s $f0, $f1
bc1f Ls2_0
nop
ori $s2, $s2, 1
Ls2_0: nop
c.eq.s $f1, $f0
bc1f Ls2_1
nop
ori $s2, $s2, 2
Ls2_1: nop
c.eq.s $f0, $f0
bc1f Ls2_2
nop
ori $s2, $s2, 4
Ls2_2: nop
c.eq.s $f0, $f2
bc1f Ls2_3
nop
ori $s2, $s2, 8
Ls2_3: nop
c.eq.s $f2, $f2
bc1f Ls2_4
nop
ori $s2, $s2, 16
Ls2_4: nop
c.ueq.s $f0, $f1
bc1f Ls3_0
nop
ori $s3, $s3, 1
Ls3_0: nop
c.ueq.s $f1, $f0
bc1f Ls3_1
nop
ori $s3, $s3, 2
Ls3_1: nop
c.ueq.s $f0, $f0
bc1f Ls3_2
nop
ori $s3, $s3, 4
Ls3_2: nop
c.ueq.s $f0, $f2
bc1f Ls3_3
nop
ori $s3, $s3, 8
Ls3_3: nop
c.ueq.s $f2, $f2
bc1f Ls3_4
nop
ori $s3, $s3, 16
Ls3_4: nop
c.olt.s $f0, $f1
bc1f Ls4_0
nop
ori $s4, $s4, 1
Ls4_0: nop
c.olt.s $f1, $f0
bc1f Ls4_1
nop
ori $s4, $s4, 2
Ls4_1: nop
c.olt.s $f0, $f0
bc1f Ls4_2
nop
ori $s4, $s4, 4
Ls4_2: nop
c.olt.s $f0, $f2
bc1f Ls4_3
nop
ori $s4, $s4, 8
Ls4_3: nop
c.olt.s $f2, $f2
bc1f Ls4_4
nop
ori $s4, $s4, 16
Ls4_4: nop
c.ult.s $f0, $f1
bc1f Ls5_0
nop
ori $s5, $s5, 1
Ls5_0: nop
c.ult.s $f1, $f0
bc1f Ls5_1
nop
ori $s5, $s5, 2
Ls5_1: nop
c.ult.s $f0, $f0
bc1f Ls5_2
nop
ori $s5, $s5, 4
Ls5_2: nop
c.ult.s $f0, $f2
bc1f Ls5_3
nop
ori $s5, $s5, 8
Ls5_3: nop
c.ult.s $f2, $f2
bc1f Ls5_4
nop
ori $s5, $s5, 16
Ls5_4: nop
c.ole.s $f0, $f1
bc1f Ls6_0
nop
ori $s6, $s6, 1
Ls6_0: nop
c.ole.s $f1, $f0
bc1f Ls6_1
nop
ori $s6, $s6, 2
Ls6_1: nop
c.ole.s $f0, $f0
bc1f Ls6_2
nop
ori $s6, $s6, 4
Ls6_2: nop
c.ole.s $f0, $f2
bc1f Ls6_3
nop
ori $s6, $s6, 8
Ls6_3: nop
c.ole.s $f2, $f2
bc1f Ls6_4
nop
ori $s6, $s6, 16
Ls6_4: nop
c.ule.s $f0, $f1
bc1f Ls7_0
nop
ori $s7, $s7, 1
Ls7_0: nop
c.ule.s $f1, $f0
bc1f Ls7_1
nop
ori $s7, $s7, 2
Ls7_1: nop
c.ule.s $f0, $f0
bc1f Ls7_2
nop
ori $s7, $s7, 4
Ls7_2: nop
c.ule.s $f0, $f2
bc1f Ls7_3
nop
ori $s7, $s7, 8
Ls7_3: nop
c.ule.s $f2, $f2
bc1f Ls7_4
nop
ori $s7, $s7, 16
Ls7_4: nop
li $v0, 10
syscall
