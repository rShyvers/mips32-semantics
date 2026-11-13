# ext/ins (MIPS32r2): edge positions/sizes. MD00086 Vol II-A Rev 6.06: EXT p.183-184, INS p.192-193.
# ext rt,rs,pos,size: rt = zero-extended rs[pos+size-1..pos]. ins rt,rs,pos,size: rt[pos+size-1..pos] = rs[size-1..0], rest kept.
# t0 = 0x12345678.  ext(3,1)=1  ext(24,8)=0x12  ext(0,32)=0x12345678  ext(28,4)=1  ext(31,1)=0  ext(4,12)=0x567
# oracle: expect gpr:s0=1 gpr:s1=0x12 gpr:s2=0x12345678 gpr:s3=1 gpr:s4=0 gpr:s5=0x567
# oracle: expect gpr:t2=1 gpr:t3=0x80000000 gpr:t4=0xaaaa78aa gpr:t5=0 gpr:t6=0x1ffffff1 gpr:t7=0x56785555
li $t0, 0x12345678
ext $s0, $t0, 3, 1
ext $s1, $t0, 24, 8
ext $s2, $t0, 0, 32
ext $s3, $t0, 28, 4
ext $s4, $t0, 31, 1
ext $s5, $t0, 4, 12
li $t1, 0xffffffff
li $t2, 0
ins $t2, $t1, 0, 1
li $t3, 0
ins $t3, $t1, 31, 1
li $t4, 0xaaaaaaaa
ins $t4, $t0, 8, 8
li $t5, 0xdeadbeef
ins $t5, $zero, 0, 32
li $t6, 0x11111111
ins $t6, $t1, 4, 24
li $t7, 0x55555555
ins $t7, $t0, 16, 16
li $v0, 10
syscall
