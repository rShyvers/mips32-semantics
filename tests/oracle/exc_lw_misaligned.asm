# lw from an address with low bits 01: Address Error on load (ExcCode 4), BadVAddr = effective address,
# destination register unchanged. MD00086 Vol II-A Rev 6.06: LW p.235 (Exceptions: Address Error);
# MD00090 Vol III Rev 6.02 BadVAddr register.
# oracle: expect cause=0x10 badvaddr=0x10010001 gpr:t1=0x1234
# oracle: unpredictable term MD00086 Vol II-A Rev 6.06 LW p.235 ("Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment") and MD00082 Vol I-A Rev 6.01 App. B.2 p.128 ("Full Misalignment Support" and "Trap (and Emulate) All Misaligneds" are both permitted): an implementation choice; the profile traps every misaligned access (DECISIONS D3, the model, checked by the expect line), QEMU mips32r6-generic performs it in hardware
# oracle: unpredictable gpr:t1 MD00086 Vol II-A Rev 6.06 LW p.235 ("Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment") and MD00082 Vol I-A Rev 6.01 App. B.2 p.128 ("Full Misalignment Support" and "Trap (and Emulate) All Misaligneds" are both permitted): an implementation choice; the profile traps every misaligned access (DECISIONS D3, the model, checked by the expect line), QEMU mips32r6-generic performs it in hardware
# oracle: unpredictable epc MD00086 Vol II-A Rev 6.06 LW p.235 ("Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment") and MD00082 Vol I-A Rev 6.01 App. B.2 p.128 ("Full Misalignment Support" and "Trap (and Emulate) All Misaligneds" are both permitted): an implementation choice; the profile traps every misaligned access (DECISIONS D3, the model, checked by the expect line), QEMU mips32r6-generic performs it in hardware
# oracle: unpredictable badvaddr MD00086 Vol II-A Rev 6.06 LW p.235 ("Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment") and MD00082 Vol I-A Rev 6.01 App. B.2 p.128 ("Full Misalignment Support" and "Trap (and Emulate) All Misaligneds" are both permitted): an implementation choice; the profile traps every misaligned access (DECISIONS D3, the model, checked by the expect line), QEMU mips32r6-generic performs it in hardware
# oracle: unpredictable pc MD00086 Vol II-A Rev 6.06 LW p.235 ("Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment") and MD00082 Vol I-A Rev 6.01 App. B.2 p.128 ("Full Misalignment Support" and "Trap (and Emulate) All Misaligneds" are both permitted): an implementation choice; the profile traps every misaligned access (DECISIONS D3, the model, checked by the expect line), QEMU mips32r6-generic performs it in hardware
# oracle: unpredictable cause MD00086 Vol II-A Rev 6.06 LW p.235 ("Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment") and MD00082 Vol I-A Rev 6.01 App. B.2 p.128 ("Full Misalignment Support" and "Trap (and Emulate) All Misaligneds" are both permitted): an implementation choice; the profile traps every misaligned access (DECISIONS D3, the model, checked by the expect line), QEMU mips32r6-generic performs it in hardware
.data
w: .word 0, 0
.text
la $t0, w
li $t1, 0x1234
lw $t1, 1($t0)
nop
