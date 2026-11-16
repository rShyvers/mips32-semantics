# Release 6: PREF with hint 24..31 raises Reserved Instruction (ExcCode 10). The handler counts the exceptions in $s4 and skips the instruction.
# The model executes every PREF as a no-op: a known model bug.
# MD00086 Vol II-A Rev 6.06 PREF Table 5.2 p.322-323 (hints 24, 25, 26-29, 30, 31: 'Release 6: ... not implemented in the Release 6 architecture and generate(s)
# a Reserved Instruction exception (RI)').
# oracle: known-model-bug gpr:s4 MD00086 Vol II-A Rev 6.06 PREF Table 5.2 p.322-323: hints 24..31 raise Reserved Instruction in Release 6; model (lead, Exec Memory/decoder): PREF is a no-op for every hint
# oracle: known-model-bug gpr:k0 same (the handler's EPC never read in the model)
.data
d: .word 1, 2
res: .space 64
.ktext
addiu $s4, $s4, 1
mfc0 $k0, $14
addiu $k0, $k0, 4
mtc0 $k0, $14
eret
.text
li $s4, 0
la $t0, d
pref 24, 0($t0)
pref 25, 0($t0)
pref 26, 0($t0)
pref 27, 0($t0)
pref 28, 0($t0)
pref 29, 0($t0)
pref 30, 0($t0)
pref 31, 0($t0)
li $s0, 7
