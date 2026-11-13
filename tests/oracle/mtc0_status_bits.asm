# Single-bit writes to Status: IE, EXL(1), IM7..0, BEV(22), CU1(29) and combinations; each read back (masked to the implemented bits 0x2040ff07) and stored.
# Status is restored before exit (BEV/EXL redirect or mask the exit exception). ERL is not written: with ERL = 1 useg is unmapped on a real CPU/QEMU (the harness's TLB-mapped text would vanish).
# MD00090 Vol III Rev 6.02 Status register field descriptions (p.189 ff.: CU1 bit 29, BEV bit 22, IM bits 15..8, ERL bit 2, EXL bit 1, IE bit 0).
.data
res: .space 132
.text
la $s7, res
li $t5, 0x2040ff07
li $t0, 0x00000001
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 0($s7)
li $t0, 0x00000100
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 4($s7)
li $t0, 0x00000200
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 8($s7)
li $t0, 0x00000400
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 12($s7)
li $t0, 0x00000800
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 16($s7)
li $t0, 0x00001000
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 20($s7)
li $t0, 0x00002000
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 24($s7)
li $t0, 0x00004000
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 28($s7)
li $t0, 0x00008000
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 32($s7)
li $t0, 0x00400000
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 36($s7)
li $t0, 0x20000000
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 40($s7)
li $t0, 0x0000ff00
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 44($s7)
li $t0, 0x2000ff00
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 48($s7)
li $t0, 0x00000000
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 52($s7)
li $t0, 0x20000001
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 56($s7)
li $t0, 0x20400000
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 60($s7)
li $t0, 0x20000002
mtc0 $t0, $12
mfc0 $t1, $12
and $t1, $t1, $t5
sw $t1, 64($s7)
li $t0, 0x20000000
mtc0 $t0, $12
li $v0, 10
syscall
