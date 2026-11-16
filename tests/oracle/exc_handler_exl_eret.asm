# Status.EXL = 1 when an exception occurs: EPC/BD not overwritten, handler still runs at 0x80000180;
# eret clears EXL (Status.ERL = 0) and jumps to EPC; the handler points EPC at `after`.
# MD00090 Vol III Rev 6.02 "General Exception Processing"; MD00086 Vol II-A Rev 6.06 ERET p.177-178.
# oracle: expect gpr:s0=0x24000002 gpr:s1=0x00000024 gpr:s2=0x1234
.ktext
mfc0 $s2, $14            # EPC as seen by the handler (still 0x1234: not updated while EXL=1)
mfc0 $s0, $12            # Status inside the handler: EXL=1
la $k0, after
mtc0 $k0, $14
eret
.text
lui $t1, 0x2000
mtc0 $t1, $12            # Status = CU1 (agreement between QEMU and the model)
li $t0, 0x1234
mtc0 $t0, $14
mfc0 $t1, $12
ori $t1, $t1, 2          # EXL = 1
mtc0 $t1, $12
break
nop
after: mfc0 $s1, $12     # EXL cleared by eret -> Status = CU1 only: 0x20000000
srl $s1, $s1, 24         # => 0x20 (low byte of the high half)
nop
