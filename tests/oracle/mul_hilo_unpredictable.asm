# mul leaves HI/LO UNPREDICTABLE: they must not be compared. MD00086 Vol II-A Rev 6.06: MUL p.299.
# oracle: unpredictable hi MD00086 MUL p.299: HI UNPREDICTABLE after MUL
# oracle: unpredictable lo MD00086 MUL p.299: LO UNPREDICTABLE after MUL
# oracle: expect gpr:t2=0xffffffe8 gpr:t4=0
li $t0, -4
li $t1, 6
mthi $t0
mtlo $t1
mul $t2, $t0, $t1          # -24 = 0xffffffe8
li $t3, 0x10000
mul $t4, $t3, $t3          # low 32 bits 0
li $v0, 10
syscall
