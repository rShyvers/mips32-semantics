# sc to a misaligned address (different from the LL address): Address Error on store (ExcCode 5), BadVAddr = address.
# MD00086 Vol II-A Rev 6.06: SC p.349 ("The effective address must be naturally-aligned. If either of the 2 least-significant
# bits of the address is non-zero, an Address Error exception occurs."), Exceptions list p.349.
# QEMU 11.0.3 compares the SC address with the LL address FIRST and fails the SC (rt <- 0) without checking alignment, so no
# exception is raised and execution continues: declared QEMU deviation (the manual wins, the model implements it).
# oracle: expect cause=0x14 badvaddr=0x10010001 gpr:t1=0x55
# oracle: expect-deviation term MD00086 Vol II-A Rev 6.06 SC p.349 ("If either of the 2 least-significant bits of the address is non-zero, an Address Error exception occurs"; "Providing misaligned support for Release 6 is not a requirement for this instruction"): misaligned SC must take Address Error; QEMU fails the SC silently (address != LLAddr)
# oracle: expect-deviation cause MD00086 Vol II-A Rev 6.06 SC p.349: same as term (QEMU raises no exception)
# oracle: expect-deviation epc MD00086 Vol II-A Rev 6.06 SC p.349: same as term (QEMU raises no exception)
# oracle: expect-deviation badvaddr MD00086 Vol II-A Rev 6.06 SC p.349: same as term (QEMU raises no exception)
# oracle: expect-deviation pc MD00086 Vol II-A Rev 6.06 SC p.349: same as term (QEMU raises no exception)
# oracle: expect-deviation gpr:t1 MD00086 Vol II-A Rev 6.06 SC p.349: exception leaves rt unchanged; QEMU writes 0 (SC-failed result)
.data
w: .word 0, 0
.text
la $t0, w
li $t1, 0x55
ll $t2, 0($t0)
sc $t1, 1($t0)
nop
