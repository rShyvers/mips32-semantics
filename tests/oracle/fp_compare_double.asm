# c.cond.d, same truth table as fp_compare_single with doubles: a=1.0, b=2.0 and a quiet NaN.
# MD00086 Vol II-A Rev 6.06: C.cond.fmt p.110-113.
# oracle: expect gpr:s0=0 gpr:s1=0x18 gpr:s2=4 gpr:s3=0x1c gpr:s4=1 gpr:s5=0x19 gpr:s6=5 gpr:s7=0x1d
.data
.align 3
d1: .word 0x3ff00000, 0
d2: .word 0x40000000, 0
dn: .word 0x7ff80000, 0
.text
la $t0, d1
ldc1 $f0, 0($t0)
ldc1 $f2, 8($t0)
ldc1 $f4, 16($t0)
c.f.d $f0, $f2
bc1f Ld0_0
nop
ori $s0, $s0, 1
Ld0_0: nop
c.f.d $f2, $f0
bc1f Ld0_1
nop
ori $s0, $s0, 2
Ld0_1: nop
c.f.d $f0, $f0
bc1f Ld0_2
nop
ori $s0, $s0, 4
Ld0_2: nop
c.f.d $f0, $f4
bc1f Ld0_3
nop
ori $s0, $s0, 8
Ld0_3: nop
c.f.d $f4, $f4
bc1f Ld0_4
nop
ori $s0, $s0, 16
Ld0_4: nop
c.un.d $f0, $f2
bc1f Ld1_0
nop
ori $s1, $s1, 1
Ld1_0: nop
c.un.d $f2, $f0
bc1f Ld1_1
nop
ori $s1, $s1, 2
Ld1_1: nop
c.un.d $f0, $f0
bc1f Ld1_2
nop
ori $s1, $s1, 4
Ld1_2: nop
c.un.d $f0, $f4
bc1f Ld1_3
nop
ori $s1, $s1, 8
Ld1_3: nop
c.un.d $f4, $f4
bc1f Ld1_4
nop
ori $s1, $s1, 16
Ld1_4: nop
c.eq.d $f0, $f2
bc1f Ld2_0
nop
ori $s2, $s2, 1
Ld2_0: nop
c.eq.d $f2, $f0
bc1f Ld2_1
nop
ori $s2, $s2, 2
Ld2_1: nop
c.eq.d $f0, $f0
bc1f Ld2_2
nop
ori $s2, $s2, 4
Ld2_2: nop
c.eq.d $f0, $f4
bc1f Ld2_3
nop
ori $s2, $s2, 8
Ld2_3: nop
c.eq.d $f4, $f4
bc1f Ld2_4
nop
ori $s2, $s2, 16
Ld2_4: nop
c.ueq.d $f0, $f2
bc1f Ld3_0
nop
ori $s3, $s3, 1
Ld3_0: nop
c.ueq.d $f2, $f0
bc1f Ld3_1
nop
ori $s3, $s3, 2
Ld3_1: nop
c.ueq.d $f0, $f0
bc1f Ld3_2
nop
ori $s3, $s3, 4
Ld3_2: nop
c.ueq.d $f0, $f4
bc1f Ld3_3
nop
ori $s3, $s3, 8
Ld3_3: nop
c.ueq.d $f4, $f4
bc1f Ld3_4
nop
ori $s3, $s3, 16
Ld3_4: nop
c.olt.d $f0, $f2
bc1f Ld4_0
nop
ori $s4, $s4, 1
Ld4_0: nop
c.olt.d $f2, $f0
bc1f Ld4_1
nop
ori $s4, $s4, 2
Ld4_1: nop
c.olt.d $f0, $f0
bc1f Ld4_2
nop
ori $s4, $s4, 4
Ld4_2: nop
c.olt.d $f0, $f4
bc1f Ld4_3
nop
ori $s4, $s4, 8
Ld4_3: nop
c.olt.d $f4, $f4
bc1f Ld4_4
nop
ori $s4, $s4, 16
Ld4_4: nop
c.ult.d $f0, $f2
bc1f Ld5_0
nop
ori $s5, $s5, 1
Ld5_0: nop
c.ult.d $f2, $f0
bc1f Ld5_1
nop
ori $s5, $s5, 2
Ld5_1: nop
c.ult.d $f0, $f0
bc1f Ld5_2
nop
ori $s5, $s5, 4
Ld5_2: nop
c.ult.d $f0, $f4
bc1f Ld5_3
nop
ori $s5, $s5, 8
Ld5_3: nop
c.ult.d $f4, $f4
bc1f Ld5_4
nop
ori $s5, $s5, 16
Ld5_4: nop
c.ole.d $f0, $f2
bc1f Ld6_0
nop
ori $s6, $s6, 1
Ld6_0: nop
c.ole.d $f2, $f0
bc1f Ld6_1
nop
ori $s6, $s6, 2
Ld6_1: nop
c.ole.d $f0, $f0
bc1f Ld6_2
nop
ori $s6, $s6, 4
Ld6_2: nop
c.ole.d $f0, $f4
bc1f Ld6_3
nop
ori $s6, $s6, 8
Ld6_3: nop
c.ole.d $f4, $f4
bc1f Ld6_4
nop
ori $s6, $s6, 16
Ld6_4: nop
c.ule.d $f0, $f2
bc1f Ld7_0
nop
ori $s7, $s7, 1
Ld7_0: nop
c.ule.d $f2, $f0
bc1f Ld7_1
nop
ori $s7, $s7, 2
Ld7_1: nop
c.ule.d $f0, $f0
bc1f Ld7_2
nop
ori $s7, $s7, 4
Ld7_2: nop
c.ule.d $f0, $f4
bc1f Ld7_3
nop
ori $s7, $s7, 8
Ld7_3: nop
c.ule.d $f4, $f4
bc1f Ld7_4
nop
ori $s7, $s7, 16
Ld7_4: nop
li $v0, 10
syscall
