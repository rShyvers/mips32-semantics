# Rotate/byte ops: rotr rotrv seb seh wsbh; clz clo.
# MD00086 Vol II-A Rev 6.06: ROTR p.339, ROTRV p.340, SEB p.365, SEH p.366-367, WSBH p.445, CLZ p.135, CLO p.134.
# oracle: expect gpr:s0=0x81234567 gpr:s1=0x78123456 gpr:s2=0xffffff80 gpr:s3=0x00007fff gpr:s4=0x34127856
li $t0, 0x12345678
rotr $s0, $t0, 4           # 0x81234567
rotr $s1, $t0, 8           # 0x78123456
li $t1, 0x80
seb $s2, $t1
li $t2, 0x17fff
seh $s3, $t2
wsbh $s4, $t0              # swap bytes within halfwords: 0x34127856
rotr $s5, $t0, 0
rotr $s6, $t0, 31
li $t3, 36
rotrv $s7, $t0, $t3        # rotate by 36 mod 32 = 4
li $t4, 0x00f00000
clz $t5, $t4               # 8
clo $t6, $t4               # 0
li $t4, 0xfff00000
clo $t7, $t4               # 12
clz $t8, $zero             # 32
li $t4, -1
clo $t9, $t4               # 32
seb $a0, $zero
seh $a1, $t4
li $v0, 10
syscall
