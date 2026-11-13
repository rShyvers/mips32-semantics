# syscall with $v0 outside the environment-call convention {1,4,10,11}: a real Syscall exception (ExcCode 8).
# MD00086 Vol II-A Rev 6.06: SYSCALL p.415.
# oracle: expect cause=0x20 epc=0x00400004
li $v0, 99
syscall
nop
