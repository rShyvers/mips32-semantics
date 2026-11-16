# Config4 and Config5 (CP0 16 sel 4, 5) in Kernel Mode, and Config5.SBRI (bit 6) read/write.
# Config4 (MD00090 Vol III Rev 6.02 sec 9.49 Table 9.68 p.253-256): M = 1 (Config5 present, p.253); IE (30..29) = 0: TLBINV/TLBINVF are not
# supported by a Fixed Mapping MMU ("Release 6: On processors that include a Block Address Translation (BAT) or Fixed Mapping (FM) MMU (ConfigMT =
# 2 or 3), the operation of this instruction causes a Reserved Instruction exception", MD00086 Vol II-A Rev 6.06 TLBINV p.423); KScrExist (23..16)
# = 0xfc ("For Release 6, bits 2-7 are always 1", p.255); the TLB fields are 0. Model: 0x80fc0000 (s0, asserted); s4 = Config4 without IE.
# Config5 (sec 9.50 Table 9.69 p.259-264): XNP (13) = 1 (no LLX/SCX, p.261), DEC (11) = 0 ("Only Little-Endian mode supported", p.261), L2C (10) = 0
# (Config2 present, p.261), SBRI (6) R/W reset 0 (p.263), LLB (4) = 1 ("In Release 6, Config5LLB is read-only 1", p.264), every optional-module bit
# 0 (DECISIONS D5): 0x00002010. s1 = Config5, s2 = after writing SBRI = 1, s3 = after writing it back to 0.
# oracle: expect gpr:s0=0x80fc0000 gpr:s4=0x80fc0000 gpr:s1=0x00002010 gpr:s2=0x00002050 gpr:s3=0x00002010
# oracle: unpredictable gpr:s0 MD00090 Vol III Rev 6.02 Table 9.68 p.254 (Config4.IE, "Preset by hardware"; "Always Required for implementations with TLBs") and MD00086 Vol II-A Rev 6.06 TLBINV p.423 (RI with a Fixed Mapping MMU): IE depends on the MMU type, an implementation choice (MD00082 Vol I-A Rev 6.01 sec 2.4.2 p.32); profile Fixed Mapping (DECISIONS D4), QEMU mips32r6-generic has a TLB with IE = 3 (raw 0xe0fc0000); compared without IE in s4
.text
mfc0 $s0, $16, 4
li $t1, 0x9fffffff
and $s4, $s0, $t1
mfc0 $s1, $16, 5
ori $t0, $s1, 0x40
mtc0 $t0, $16, 5
mfc0 $s2, $16, 5
mtc0 $s1, $16, 5
mfc0 $s3, $16, 5
li $t0, 0
li $t1, 0
li $v0, 10
syscall
