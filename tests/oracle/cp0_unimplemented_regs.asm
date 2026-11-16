# Release 6: an unimplemented or reserved CP0 register reads 0 and ignores writes. Each register is written with all ones and read back
# (the old value is restored at once: on QEMU these are live TLB registers); the results are logged at res.
# MD00086 Vol II-A Rev 6.06 MFC0 p.266 ("Release 6: Reading a reserved register or a register that is not implemented for the current core
# configuration returns 0"), MTC0 p.290 ("Release 6: Writes to a register that is reserved or not defined for the current core configuration are
# ignored"); MD00090 Vol III Rev 6.02 sec A.1.3 p.317 (Fixed Mapping MMU: "The Index, Random, EntryLo0, EntryLo1, Context, PageMask, Wired, and
# EntryHi registers are no longer required and may be removed. ... For Release 6, writes to these registers are ignored, reads return 0 as if the
# registers were Reserved for Architecture"), Table 9.1 p.111-116 ((16,6) "Available for implementation-dependent", (17,1) MAAR (sec 9.53 p.271, optional, absent:
# Config5.MRP = 0, Table 9.69 p.264), (21,*) "Reserved for future extensions", (22,*) "Available for implementation-dependent").
# Wired (res+0x10) reads 0 on QEMU too and stays compared. The run is in kseg0 (.ktext, reached by jr): on QEMU a changed EntryHi ASID would unmap the kuseg text.
# oracle: expect gpr:s4=1 mem:0x10010000=0 mem:0x10010004=0 mem:0x10010008=0 mem:0x1001000c=0 mem:0x10010010=0 mem:0x10010014=0 mem:0x10010018=0 mem:0x1001001c=0 mem:0x10010020=0 mem:0x10010024=0
# oracle: unpredictable mem:0x10010000 MD00082 Vol I-A Rev 6.01 sec 2.4.2 p.32 ("The standard TLB-based memory management unit may be replaced with: a simpler MMU (e.g., a Fixed Mapping MMU ...)") and MD00090 Vol III Rev 6.02 sec A.1.3 p.317: the MMU type is an implementation choice; the profile has the Fixed Mapping MMU (DECISIONS D4: register reads 0, write ignored, asserted by expect), QEMU mips32r6-generic has a TLB MMU where Index is implemented
# oracle: unpredictable mem:0x10010004 MD00082 Vol I-A Rev 6.01 sec 2.4.2 p.32 ("The standard TLB-based memory management unit may be replaced with: a simpler MMU (e.g., a Fixed Mapping MMU ...)") and MD00090 Vol III Rev 6.02 sec A.1.3 p.317: the MMU type is an implementation choice; the profile has the Fixed Mapping MMU (DECISIONS D4: register reads 0, write ignored, asserted by expect), QEMU mips32r6-generic has a TLB MMU where EntryLo0 is implemented
# oracle: unpredictable mem:0x10010008 MD00082 Vol I-A Rev 6.01 sec 2.4.2 p.32 ("The standard TLB-based memory management unit may be replaced with: a simpler MMU (e.g., a Fixed Mapping MMU ...)") and MD00090 Vol III Rev 6.02 sec A.1.3 p.317: the MMU type is an implementation choice; the profile has the Fixed Mapping MMU (DECISIONS D4: register reads 0, write ignored, asserted by expect), QEMU mips32r6-generic has a TLB MMU where Context is implemented
# oracle: unpredictable mem:0x1001000c MD00082 Vol I-A Rev 6.01 sec 2.4.2 p.32 ("The standard TLB-based memory management unit may be replaced with: a simpler MMU (e.g., a Fixed Mapping MMU ...)") and MD00090 Vol III Rev 6.02 sec A.1.3 p.317: the MMU type is an implementation choice; the profile has the Fixed Mapping MMU (DECISIONS D4: register reads 0, write ignored, asserted by expect), QEMU mips32r6-generic has a TLB MMU where PageMask is implemented
# oracle: unpredictable mem:0x10010014 MD00082 Vol I-A Rev 6.01 sec 2.4.2 p.32 ("The standard TLB-based memory management unit may be replaced with: a simpler MMU (e.g., a Fixed Mapping MMU ...)") and MD00090 Vol III Rev 6.02 sec A.1.3 p.317: the MMU type is an implementation choice; the profile has the Fixed Mapping MMU (DECISIONS D4: register reads 0, write ignored, asserted by expect), QEMU mips32r6-generic has a TLB MMU where EntryHi is implemented
.data
res: .word 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99
.ktext
nop
kcode:
# (0,0) Index: res+0x0
mfc0 $t9, $0, 0
mtc0 $t8, $0, 0
ehb
mfc0 $t7, $0, 0
mtc0 $t9, $0, 0
ehb
sw $t7, 0($s7)
# (2,0) EntryLo0: res+0x4
mfc0 $t9, $2, 0
mtc0 $t8, $2, 0
ehb
mfc0 $t7, $2, 0
mtc0 $t9, $2, 0
ehb
sw $t7, 4($s7)
# (4,0) Context: res+0x8
mfc0 $t9, $4, 0
mtc0 $t8, $4, 0
ehb
mfc0 $t7, $4, 0
mtc0 $t9, $4, 0
ehb
sw $t7, 8($s7)
# (5,0) PageMask: res+0xc
mfc0 $t9, $5, 0
mtc0 $t8, $5, 0
ehb
mfc0 $t7, $5, 0
mtc0 $t9, $5, 0
ehb
sw $t7, 12($s7)
# (6,0) Wired: res+0x10
mfc0 $t9, $6, 0
mtc0 $t8, $6, 0
ehb
mfc0 $t7, $6, 0
mtc0 $t9, $6, 0
ehb
sw $t7, 16($s7)
# (10,0) EntryHi: res+0x14
mfc0 $t9, $10, 0
mtc0 $t8, $10, 0
ehb
mfc0 $t7, $10, 0
mtc0 $t9, $10, 0
ehb
sw $t7, 20($s7)
# (16,6) impl-dep: res+0x18
mfc0 $t9, $16, 6
mtc0 $t8, $16, 6
ehb
mfc0 $t7, $16, 6
mtc0 $t9, $16, 6
ehb
sw $t7, 24($s7)
# (17,1) MAAR: res+0x1c
mfc0 $t9, $17, 1
mtc0 $t8, $17, 1
ehb
mfc0 $t7, $17, 1
mtc0 $t9, $17, 1
ehb
sw $t7, 28($s7)
# (21,0) Reserved: res+0x20
mfc0 $t9, $21, 0
mtc0 $t8, $21, 0
ehb
mfc0 $t7, $21, 0
mtc0 $t9, $21, 0
ehb
sw $t7, 32($s7)
# (22,0) impl-dep: res+0x24
mfc0 $t9, $22, 0
mtc0 $t8, $22, 0
ehb
mfc0 $t7, $22, 0
mtc0 $t9, $22, 0
ehb
sw $t7, 36($s7)
li $s4, 1
li $t7, 0
li $t9, 0
la $t6, done
jr $t6
nop
.text
li $s4, 0
la $s7, res
li $t8, -1
la $t6, kcode
jr $t6
nop
done:
li $t6, 0
li $t8, 0
