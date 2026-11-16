import Semantics.Asm.Operands

/-!
# Asm.Memory — loads, stores, LL/SC, PREF, SYNCI

`rt, offset(base)`. The classic loads/stores and SYNCI take a signed 16-bit offset; the Release 6
`ll`/`sc`/`pref` (SPECIAL3) take a signed **9-bit** offset, -256..255 (LL p.223, SC p.347, PREF
p.321). The FPU loads/stores are in `Asm/Fpu.lean`.
-/

namespace Asm

/-- Loads, stores, LL/SC, PREF, SYNCI. -/
def memoryTable : EncTable :=
  [ ("lb",  memOp 16 gpr .lb),
    ("lbu", memOp 16 gpr .lbu),
    ("lh",  memOp 16 gpr .lh),
    ("lhu", memOp 16 gpr .lhu),
    ("lw",  memOp 16 gpr .lw),
    ("sb",  memOp 16 gpr .sb),
    ("sh",  memOp 16 gpr .sh),
    ("sw",  memOp 16 gpr .sw),
    ("ll",  memOp 9 gpr .ll),
    ("sc",  memOp 9 gpr .sc),
    ("pref", hintMem 9 .pref),
    ("synci", memOnly .synci) ]

end Asm
