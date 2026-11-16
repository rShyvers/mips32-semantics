# sw to an address with low bits 10: Address Error on store (ExcCode 5), BadVAddr = address, memory unchanged.
# MD00086 Vol II-A Rev 6.06: SW p.392.
# oracle: expect cause=0x14 badvaddr=0x10010002
# oracle: unpredictable term MD00086 Vol II-A Rev 6.06 SW p.392 ("Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment") and MD00082 Vol I-A Rev 6.01 App. B.2 p.128 ("Full Misalignment Support" and "Trap (and Emulate) All Misaligneds" are both permitted): an implementation choice; the profile traps every misaligned access (DECISIONS D3, the model, checked by the expect line), QEMU mips32r6-generic performs it in hardware
# oracle: unpredictable mem MD00086 Vol II-A Rev 6.06 SW p.392 ("Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment") and MD00082 Vol I-A Rev 6.01 App. B.2 p.128 ("Full Misalignment Support" and "Trap (and Emulate) All Misaligneds" are both permitted): an implementation choice; the profile traps every misaligned access (DECISIONS D3, the model, checked by the expect line), QEMU mips32r6-generic performs it in hardware
# oracle: unpredictable epc MD00086 Vol II-A Rev 6.06 SW p.392 ("Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment") and MD00082 Vol I-A Rev 6.01 App. B.2 p.128 ("Full Misalignment Support" and "Trap (and Emulate) All Misaligneds" are both permitted): an implementation choice; the profile traps every misaligned access (DECISIONS D3, the model, checked by the expect line), QEMU mips32r6-generic performs it in hardware
# oracle: unpredictable badvaddr MD00086 Vol II-A Rev 6.06 SW p.392 ("Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment") and MD00082 Vol I-A Rev 6.01 App. B.2 p.128 ("Full Misalignment Support" and "Trap (and Emulate) All Misaligneds" are both permitted): an implementation choice; the profile traps every misaligned access (DECISIONS D3, the model, checked by the expect line), QEMU mips32r6-generic performs it in hardware
# oracle: unpredictable pc MD00086 Vol II-A Rev 6.06 SW p.392 ("Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment") and MD00082 Vol I-A Rev 6.01 App. B.2 p.128 ("Full Misalignment Support" and "Trap (and Emulate) All Misaligneds" are both permitted): an implementation choice; the profile traps every misaligned access (DECISIONS D3, the model, checked by the expect line), QEMU mips32r6-generic performs it in hardware
# oracle: unpredictable cause MD00086 Vol II-A Rev 6.06 SW p.392 ("Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment") and MD00082 Vol I-A Rev 6.01 App. B.2 p.128 ("Full Misalignment Support" and "Trap (and Emulate) All Misaligneds" are both permitted): an implementation choice; the profile traps every misaligned access (DECISIONS D3, the model, checked by the expect line), QEMU mips32r6-generic performs it in hardware
.data
w: .word 0, 0
.text
la $t0, w
li $t1, 0x1234
sw $t1, 2($t0)
nop
