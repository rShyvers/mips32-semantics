# sync and synci are architecturally nops here (no cache/ordering model): they must neither trap nor change state.
# MD00086 Vol II-A Rev 6.06: SYNC p.407-411, SYNCI p.412-414.
# oracle: expect gpr:s0=1
la $t0, tgt
sync
synci 0($t0)
synci 8($t0)
sync
tgt: li $s0, 1
li $v0, 10
syscall
