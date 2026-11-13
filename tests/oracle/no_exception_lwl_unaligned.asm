# lwl/lwr/swl/swr never raise Address Error at any alignment. MD00086 Vol II-A Rev 6.06: LWL p.240-242, SWL p.397-398.
# oracle: expect gpr:s0=1
.data
buf: .space 16
.text
la $t0, buf
lwl $t1, 3($t0)
lwr $t1, 1($t0)
swl $t1, 7($t0)
swr $t1, 6($t0)
li $s0, 1
li $v0, 10
syscall
