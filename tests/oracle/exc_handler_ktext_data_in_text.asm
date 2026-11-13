# A handler that reads Cause/EPC into registers and returns to a computed address (eret to EPC set by mtc0),
# checking that mtc0 EPC / eret / mfc0 round-trip an arbitrary address.
# MD00086 Vol II-A Rev 6.06: MTC0 p.290-291, ERET p.177-178.
# oracle: expect gpr:s0=0x00000024 gpr:s1=1
.ktext
mfc0 $s0, $13
la $k0, resume
mtc0 $k0, $14
eret
.text
break
li $s1, 99                # skipped by the handler
resume: li $s1, 1
nop
