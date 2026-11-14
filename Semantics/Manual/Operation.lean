import Semantics.Manual.Ops.IntArith
import Semantics.Manual.Ops.Memory
import Semantics.Manual.Ops.Unaligned
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
  | _ => none

end Manual
