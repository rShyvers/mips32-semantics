# mfc0 Config1/Config2/Config3 (CP0 16 sel 1..3) in Kernel Mode, and mtc0 of all ones to Config2/Config3 (read-only: ignored).
# A Release 2 processor has Config3 ("Required if any optional feature described by this register is implemented: Release 2 of the Architecture", MD00090 Vol III Rev 6.02 sec 9.48 p.245),
# hence Config2 ("Required if ... the Config3 register is required", sec 9.47 p.241), Config1.M = 1 (Table 9.65 p.237) and Config2.M = 1 (Table 9.66 p.241).
# "All fields in the Config3 register are read-only" (p.245); Config2's only R/W fields TU/SU "should read as zero and be ignored on write" when not implemented (p.241-242).
# s1 = Config1.M, s3 = Config2.M, s5 = Config3 VInt/VEIC/ISA/ULRI (bits 5,6,15..14,13) are compared; Config2 (s2) and Config3 (s4) are compared whole.
# Config3.ISAOnExc (bit 16) is not written: QEMU mips32r6-generic implements microMIPS (absent in the profile, DECISIONS D5) and would take the
# exit syscall in microMIPS mode.
# oracle: unpredictable gpr:s0 MD00090 Vol III Rev 6.02 sec 9.46 p.237-240: Config1 describes the implementation's TLB, caches and options (implementation-dependent; M checked in s1)
# oracle: known-model-bug gpr:s4 MD00090 Vol III Rev 6.02 sec 9.48 Config3 p.246 (BI/BP: "Release 6: BadInstr is always implemented") and p.248 (ULRI 13: "Release 6: UserLocal is always implemented"; RXI 12: "Release 6: The RIE and XIE bits are always implemented"): W2: the model's Config3 is still the pre-Release 6 value 0 (QEMU mips32r6-generic also has M = 1 and ISA = 2 for microMIPS, absent in the profile, DECISIONS D5)
# oracle: known-model-bug gpr:s5 MD00090 Vol III Rev 6.02 sec 9.48 Config3 p.246 (BI/BP: "Release 6: BadInstr is always implemented") and p.248 (ULRI 13: "Release 6: UserLocal is always implemented"; RXI 12: "Release 6: The RIE and XIE bits are always implemented"): W2: the model's Config3 is still the pre-Release 6 value 0 (QEMU mips32r6-generic also has M = 1 and ISA = 2 for microMIPS, absent in the profile, DECISIONS D5)
# oracle: known-model-bug gpr:s7 MD00090 Vol III Rev 6.02 sec 9.48 Config3 p.246 (BI/BP: "Release 6: BadInstr is always implemented") and p.248 (ULRI 13: "Release 6: UserLocal is always implemented"; RXI 12: "Release 6: The RIE and XIE bits are always implemented"): W2: the model's Config3 is still the pre-Release 6 value 0 (QEMU mips32r6-generic also has M = 1 and ISA = 2 for microMIPS, absent in the profile, DECISIONS D5)
.text
mfc0 $s0, $16, 1
srl $s1, $s0, 31
mfc0 $s2, $16, 2
srl $s3, $s2, 31
mfc0 $s4, $16, 3
li $t0, 0x0000e060
and $s5, $s4, $t0
li $t1, -1
mtc0 $t1, $16, 2
li $t1, 0xfffeffff
mtc0 $t1, $16, 3
mfc0 $s6, $16, 2
mfc0 $s7, $16, 3
li $v0, 10
syscall
