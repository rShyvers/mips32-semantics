# jr to an address with low bits 10: Address Error (instruction fetch, ExcCode 4) when the target is fetched,
# BadVAddr = target. MD00086 Vol II-A Rev 6.06: JR p.206-207 ("the Address Error exception occurs when the
# branch target is fetched"); MD00090 Vol III BadVAddr.
# (Low bits 01 are not tested: a QEMU 24Kf treats bit 0 as the MIPS16e ISA-mode bit, the model does not
# implement MIPS16e, MD00086 JR p.206 "processors that do not implement MIPS16e": Address Error. Not comparable.)
# oracle: expect cause=0x10 badvaddr=0x00400016
la $t0, tgt
addiu $t0, $t0, 2
jr $t0
nop
tgt: nop
