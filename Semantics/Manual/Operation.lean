import Semantics.Manual.Ops.IntArith
import Semantics.Manual.Ops.Memory
import Semantics.Manual.Ops.Unaligned
import Semantics.Manual.Ops.Atomic
import Semantics.Manual.Ops.Trap
import Semantics.Manual.Ops.Syscall
import Semantics.Manual.Ops.Branch
import Semantics.Manual.Ops.BranchLikely
import Semantics.Manual.Ops.FpuArith
import Semantics.Manual.Ops.Cp0

/-!
# Manual.Operation — the Operation section of each instruction

One arm per `Instruction` constructor, naming the transcribed Operation of its manual page
(`Semantics/Manual/Ops/*.lean`). Sub-wave 7A covers the pilot instructions; `none` marks a
constructor whose page is not transcribed yet (7B makes this total).
-/

namespace Manual

/-- **The Operation of instruction `i`** (`none`: not transcribed yet). -/
def Operation : Instruction → Option (Pseudo Unit)
  | .add rs rt rd => some (Ops.ADD rs rt rd)
  | .lw base rt off => some (Ops.LW base rt off)
  | .sw base rt off => some (Ops.SW base rt off)
  | .lwl base rt off => some (Ops.LWL base rt off)
  | .beq rs rt off => some (Ops.BEQ rs rt off)
  | .beql rs rt off => some (Ops.BEQL rs rt off)
  | .addS fd fs ft => some (Ops.ADD_S fd fs ft)
  | .mtc0 rt rd sel => some (Ops.MTC0 rt rd sel)
  -- 7B S2 memory/atomic/trap/syscall
  | .lb base rt off => some (Ops.LB base rt off)
  | .lbu base rt off => some (Ops.LBU base rt off)
  | .lh base rt off => some (Ops.LH base rt off)
  | .lhu base rt off => some (Ops.LHU base rt off)
  | .sb base rt off => some (Ops.SB base rt off)
  | .sh base rt off => some (Ops.SH base rt off)
  | .pref base hint off => some (Ops.PREF base hint off)
  | .sync stype => some (Ops.SYNC stype)
  | .synci base off => some (Ops.SYNCI base off)
  | .ll base rt off => some (Ops.LL base rt off)
  | .sc base rt off => some (Ops.SC base rt off)
  | .lwr base rt off => some (Ops.LWR base rt off)
  | .swl base rt off => some (Ops.SWL base rt off)
  | .swr base rt off => some (Ops.SWR base rt off)
  | .teq rs rt code => some (Ops.TEQ rs rt code)
  | .tne rs rt code => some (Ops.TNE rs rt code)
  | .tlt rs rt code => some (Ops.TLT rs rt code)
  | .tge rs rt code => some (Ops.TGE rs rt code)
  | .tltu rs rt code => some (Ops.TLTU rs rt code)
  | .tgeu rs rt code => some (Ops.TGEU rs rt code)
  | .teqi rs imm => some (Ops.TEQI rs imm)
  | .tnei rs imm => some (Ops.TNEI rs imm)
  | .tgei rs imm => some (Ops.TGEI rs imm)
  | .tgeiu rs imm => some (Ops.TGEIU rs imm)
  | .tlti rs imm => some (Ops.TLTI rs imm)
  | .tltiu rs imm => some (Ops.TLTIU rs imm)
  | .syscall code => some (Ops.SYSCALL code)
  | .break code => some (Ops.BREAK code)
  | _ => none

end Manual
