# LLAddr (CP0 17 sel 0) bit 0 is LLB, the software-visible LLbit: set by ll; mtc0 with bit 0 = 0 clears it (a following sc fails); mtc0 with
# bit 0 = 1 does not set it (sc still fails) and keeps it when set (sc succeeds).
# MD00090 Vol III Rev 6.02 sec 9.52 p.269 ("In Release 6, Config5LLB is read-only 1, and CP0 LLAddr is required"), Table 9.72 p.270 (LLB, bit 0, R/W:
# "LLB is set when the LL instruction is executed", "This field allows the LLbit to be software accessible", "LLB can be cleared by software but
# cannot be set"; PAddr 31..1: "The format of this register is implementation-dependent", so only bit 0 is compared); MD00086 Vol II-A Rev 6.06
# LL p.223, SC p.347 (SC stores and writes 1 iff the LLbit is set; MFC0/MTC0 are not loads or stores).
# s0 = LLB after ll; s1 = LLB after mtc0 0; s2 = sc result (0); s3 = LLB after mtc0 1 with LLB = 0; s4 = sc result (0);
# s5 = LLB after ll + mtc0 1; s6 = sc result (1); memory: only the last sc stores.
# oracle: expect gpr:s0=1 gpr:s1=0 gpr:s2=0 gpr:s3=0 gpr:s4=0 gpr:s5=1 gpr:s6=1 mem:0x10010000=0x00000066
# oracle: expect-deviation gpr:s0 MD00090 Vol III Rev 6.02 Table 9.72 p.270 (LLB, bit 0, R/W: "LLB is set when the LL instruction is executed"; "Required (Release 6)") and sec 9.50 Table 9.69 p.264 ("In Release 6, Config5LLB is read-only 1": "LLbit is software accessible through LLAddr[0]"): QEMU mips32r6-generic reads LLAddr bit 0 as 0 after ll
# oracle: expect-deviation gpr:s2 MD00090 Vol III Rev 6.02 Table 9.72 p.270 (LLB "can be cleared by software") and MD00086 Vol II-A Rev 6.06 SC p.347: QEMU ignores the LLB write of 0, so its sc succeeds (1) where the cleared LLbit must make it fail (0)
# oracle: expect-deviation gpr:s5 MD00090 Vol III Rev 6.02 Table 9.72 p.270 (LLB set by ll, kept by a write of 1): QEMU reads LLAddr bit 0 as 0 (as for s0)
.data
w: .word 5
.text
la $t0, w
li $t2, 1
ll $t1, 0($t0)
mfc0 $s0, $17
andi $s0, $s0, 1
mtc0 $zero, $17
mfc0 $s1, $17
andi $s1, $s1, 1
li $s2, 0x22
sc $s2, 0($t0)
mtc0 $t2, $17
mfc0 $s3, $17
andi $s3, $s3, 1
li $s4, 0x44
sc $s4, 0($t0)
ll $t1, 0($t0)
mtc0 $t2, $17
mfc0 $s5, $17
andi $s5, $s5, 1
li $s6, 0x66
sc $s6, 0($t0)
li $t1, 0
li $v0, 10
syscall
