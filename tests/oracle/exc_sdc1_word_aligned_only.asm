# sdc1 at a misaligned address: Address Error on store (ExcCode 5), the profile's choice for every misaligned access (DECISIONS D3).
# Release 6 permits either Address Error or a hardware misaligned access (MD00086 Vol II-A Rev 6.06 SDC1 p.362; MD00082 Vol I-A Rev 6.01
# App. B.2 p.128); QEMU mips32r6-generic performs the access, so the exception fields are not compared (the model is checked by `expect`).
# oracle: expect cause=0x14 badvaddr=0x10010004
# oracle: unpredictable term MD00086 Vol II-A Rev 6.06 SDC1 p.362: "Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment"; MD00082 Vol I-A Rev 6.01 App. B.2 p.128 (Address Error for all misaligned accesses is permitted); profile decision D3 chooses Address Error, QEMU mips32r6-generic performs the access
# oracle: unpredictable epc MD00086 Vol II-A Rev 6.06 SDC1 p.362: "Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment"; MD00082 Vol I-A Rev 6.01 App. B.2 p.128 (Address Error for all misaligned accesses is permitted); profile decision D3 chooses Address Error, QEMU mips32r6-generic performs the access
# oracle: unpredictable badvaddr MD00086 Vol II-A Rev 6.06 SDC1 p.362: "Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment"; MD00082 Vol I-A Rev 6.01 App. B.2 p.128 (Address Error for all misaligned accesses is permitted); profile decision D3 chooses Address Error, QEMU mips32r6-generic performs the access
# oracle: unpredictable pc MD00086 Vol II-A Rev 6.06 SDC1 p.362: "Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment"; MD00082 Vol I-A Rev 6.01 App. B.2 p.128 (Address Error for all misaligned accesses is permitted); profile decision D3 chooses Address Error, QEMU mips32r6-generic performs the access
# oracle: unpredictable cause MD00086 Vol II-A Rev 6.06 SDC1 p.362: "Release 6 allows hardware to provide address misalignment support in lieu of requiring natural alignment"; MD00082 Vol I-A Rev 6.01 App. B.2 p.128 (Address Error for all misaligned accesses is permitted); profile decision D3 chooses Address Error, QEMU mips32r6-generic performs the access
.data
.align 3
w: .word 0, 0, 0, 0
.text
la $t0, w
sdc1 $f0, 4($t0)
nop
