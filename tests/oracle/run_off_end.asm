# Execution runs off the end of the program (no exit): model halts `no_instruction`; the QEMU harness ends in a TLB
# refill beyond the text pages (pc/Status/Cause/EPC are not compared for this termination kind, see scripts/README.md).
li $s0, 5
addiu $s0, $s0, 1
