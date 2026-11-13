# madd/maddu/msub/msubu accumulate into HI:LO; mul writes rd (HI/LO UNPREDICTABLE afterwards).
# MD00086 Vol II-A Rev 6.06: MADD p.255, MADDU p.261, MSUB p.286, MSUBU p.289, MUL p.299 (HI/LO UNPREDICTABLE).
# 3*5 + (-2*4) = 7, then msub 3*5 => -8, maddu 0xffffffff*2 = 0x1fffffffe, msubu back to 0.
# oracle: expect gpr:s0=0x00000007 gpr:s1=0 gpr:s2=0xfffffff8 gpr:s3=0xffffffff gpr:s4=1 gpr:s5=0xfffffffe gpr:s6=0 gpr:s7=0
li $t0, 3
li $t1, 5
mthi $zero
mtlo $zero
madd $t0, $t1              # LO=15
li $t2, -2
li $t3, 4
madd $t2, $t3              # += -8 => 7
mflo $s0
mfhi $s1                   # 0
msub $t0, $t1              # 7 - 15 = -8
mflo $s2
mfhi $s3
mthi $zero
mtlo $zero
li $t4, -1
li $t5, 2
maddu $t4, $t5             # 0x1fffffffe
mfhi $s4
mflo $s5
msubu $t4, $t5             # back to 0
mfhi $s6
mflo $s7
li $v0, 10
syscall
