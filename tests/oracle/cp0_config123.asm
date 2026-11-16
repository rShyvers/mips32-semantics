# mfc0 Config1/Config2/Config3 (CP0 16 sel 1..3) in Kernel Mode, and mtc0 of all ones to Config2/Config3 (read-only: ignored).
# Config3 is present ("Required if any optional feature described by this register is implemented: Release 2 of the Architecture", MD00090 Vol III Rev 6.02 sec 9.48 p.245),
# hence Config2 ("Required if ... the Config3 register is required", sec 9.47 p.241), Config1.M = 1 (Table 9.65 p.237) and Config2.M = 1 (Table 9.66 p.241).
# "All fields in the Config3 register are read-only" (p.245); Config2's only R/W fields TU/SU "should read as zero and be ignored on write" when not implemented (p.241-242).
# Release 6 Config3 (Table 9.67): M = 1 (Config4 present, p.245), BP = BI = 1 ("Release 6: BadInstrP/BadInstr is always implemented", p.246),
# ULRI = 1 ("Release 6: UserLocal is always implemented", p.248), RXI = 1 ("Release 6: The RIE and XIE bits are always implemented", p.248);
# every optional-module bit is 0 in the profile (DECISIONS D5): the model's Config3 is 0x8C003000 (s4, asserted by `expect`).
# QEMU mips32r6-generic also implements MSA (MSAP, bit 28, p.245) and microMIPS (ISA, bits 15..14 = 2, p.248), both optional modules absent
# from the profile: the raw value s4 is not compared, s5 and s7 are Config3 with bits 28 and 15..14 cleared, s6 is Config2 after the write.
# s1 = Config1.M, s3 = Config2.M; Config2 (s2, s6) is compared whole.
# Config3.ISAOnExc (bit 16) is not written: with microMIPS implemented QEMU would take the exit syscall in microMIPS mode.
# oracle: expect gpr:s1=1 gpr:s3=1 gpr:s4=0x8c003000 gpr:s5=0x8c003000 gpr:s7=0x8c003000
# oracle: unpredictable gpr:s0 MD00090 Vol III Rev 6.02 sec 9.46 p.237-240: Config1 describes the implementation's TLB, caches and options (implementation-dependent; M checked in s1)
# oracle: unpredictable gpr:s4 MD00090 Vol III Rev 6.02 sec 9.48 Table 9.67 p.245 (MSAP, bit 28, "Preset by hardware") and p.248 (ISA, bits 15..14, "Preset by hardware", "Required if microMIPS is implemented"): implementation-dependent; the profile has neither MSA nor microMIPS (DECISIONS D5), QEMU mips32r6-generic has both (raw 0x9c00b000); compared masked in s5/s7
.text
mfc0 $s0, $16, 1
srl $s1, $s0, 31
mfc0 $s2, $16, 2
srl $s3, $s2, 31
mfc0 $s4, $16, 3
li $t0, 0xefff3fff
and $s5, $s4, $t0
li $t1, -1
mtc0 $t1, $16, 2
li $t1, 0xfffeffff
mtc0 $t1, $16, 3
mfc0 $s6, $16, 2
mfc0 $s7, $16, 3
and $s7, $s7, $t0
li $t0, 0
li $v0, 10
syscall
