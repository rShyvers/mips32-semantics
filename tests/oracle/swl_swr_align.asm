# swl/swr at all four byte offsets (big-endian), register 0x0A0B0C0D into zeroed words.
# MD00086 Vol II-A Rev 6.06: SWL p.397-398, SWR p.401-403.
# SWL stores the most-significant bytes from the addressed byte to the end of the word:
#   off0 0A0B0C0D, off1 000A0B0C, off2 00000A0B, off3 0000000A.
# SWR stores the least-significant bytes from the start of the word to the addressed byte:
#   off0 0D000000, off1 0C0D0000, off2 0B0C0D00, off3 0A0B0C0D.
# oracle: expect mem:0x10010000=0x0a0b0c0d mem:0x10010004=0x000a0b0c mem:0x10010008=0x00000a0b mem:0x1001000c=0x0000000a
# oracle: expect mem:0x10010010=0x0d000000 mem:0x10010014=0x0c0d0000 mem:0x10010018=0x0b0c0d00 mem:0x1001001c=0x0a0b0c0d
.data
buf: .space 32
.text
la $t0, buf
li $t1, 0x0A0B0C0D
swl $t1, 0($t0)
swl $t1, 5($t0)
swl $t1, 10($t0)
swl $t1, 15($t0)
swr $t1, 16($t0)
swr $t1, 21($t0)
swr $t1, 26($t0)
swr $t1, 31($t0)
li $v0, 10
syscall
