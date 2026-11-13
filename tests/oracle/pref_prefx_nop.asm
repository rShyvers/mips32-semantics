# pref with every hint 0..31 and prefx, at valid, unmapped (0) and misaligned addresses, never raise an exception and change no state.
# MD00086 Vol II-A Rev 6.06: PREF p.321 ('...it is not an exception if the address is invalid / PREF does not take TLB or address-error exceptions'), PREFX p.329.
# oracle: expect gpr:s0=7
.data
d: .word 1, 2
res: .space 64
.text
la $s7, res
la $t0, d
li $t1, 4
li $s0, 7
pref 0, 0($t0)
pref 1, 0($t0)
pref 2, 0($t0)
pref 3, 0($t0)
pref 4, 0($t0)
pref 5, 0($t0)
pref 6, 0($t0)
pref 7, 0($t0)
pref 8, 0($t0)
pref 9, 0($t0)
pref 10, 0($t0)
pref 11, 0($t0)
pref 12, 0($t0)
pref 13, 0($t0)
pref 14, 0($t0)
pref 15, 0($t0)
pref 16, 0($t0)
pref 17, 0($t0)
pref 18, 0($t0)
pref 19, 0($t0)
pref 20, 0($t0)
pref 21, 0($t0)
pref 22, 0($t0)
pref 23, 0($t0)
pref 24, 0($t0)
pref 25, 0($t0)
pref 26, 0($t0)
pref 27, 0($t0)
pref 28, 0($t0)
pref 29, 0($t0)
pref 30, 0($t0)
pref 31, 0($t0)
pref 0, 1($t0)
pref 4, 0($zero)
pref 1, -1($zero)
prefx 0, $t1($t0)
prefx 31, $zero($zero)
prefx 5, $t1($t1)
lw $s1, 0($t0)
li $v0, 10
syscall
