# movn/movz: conditional move on a register (no write when the condition fails).
# MD00086 Vol II-A Rev 6.06: MOVN p.279, MOVZ p.284.
# oracle: expect gpr:s0=11 gpr:s1=22 gpr:s2=3 gpr:s3=4
li $s0, 1
li $s1, 2
li $s2, 3
li $s3, 4
li $t0, 11
li $t1, 22
movn $s0, $t0, $t0          # t0 != 0 => moved
movz $s0, $t1, $t0          # t0 != 0 => not moved
movz $s1, $t1, $zero        # zero => moved
movn $s2, $t0, $zero        # zero => not moved
movz $s3, $zero, $t0        # not moved
li $v0, 10
syscall
