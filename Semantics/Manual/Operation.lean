import Semantics.Manual.Ops.IntArith
import Semantics.Manual.Ops.Memory
import Semantics.Manual.Ops.Unaligned
import Semantics.Manual.Ops.Branch
import Semantics.Manual.Ops.BranchLikely
import Semantics.Manual.Ops.FpuArith
import Semantics.Manual.Ops.Cp0
-- 7B S3 control + system
import Semantics.Manual.Ops.Jump
import Semantics.Manual.Ops.System
-- end 7B S3

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
  -- 7B S3 control + system
  | .bne rs rt off => some (Ops.BNE rs rt off)
  | .blez rs off => some (Ops.BLEZ rs off)
  | .bgtz rs off => some (Ops.BGTZ rs off)
  | .bltz rs off => some (Ops.BLTZ rs off)
  | .bgez rs off => some (Ops.BGEZ rs off)
  | .bltzal rs off => some (Ops.BLTZAL rs off)
  | .bgezal rs off => some (Ops.BGEZAL rs off)
  | .bnel rs rt off => some (Ops.BNEL rs rt off)
  | .blezl rs off => some (Ops.BLEZL rs off)
  | .bgtzl rs off => some (Ops.BGTZL rs off)
  | .bltzl rs off => some (Ops.BLTZL rs off)
  | .bgezl rs off => some (Ops.BGEZL rs off)
  | .bltzall rs off => some (Ops.BLTZALL rs off)
  | .bgezall rs off => some (Ops.BGEZALL rs off)
  | .j target => some (Ops.J target)
  | .jal target => some (Ops.JAL target)
  | .jr rs => some (Ops.JR rs)
  | .jalr rs rd => some (Ops.JALR rs rd)
  | .mfc0 rt rd sel => some (Ops.MFC0 rt rd sel)
  | .di rt => some (Ops.DI rt)
  | .ei rt => some (Ops.EI rt)
  | .eret => some Ops.ERET
  | .wait code => some (Ops.WAIT code)
  | .rdpgpr rd rt => some (Ops.RDPGPR rd rt)
  | .wrpgpr rd rt => some (Ops.WRPGPR rd rt)
  | .rdhwr rt rd => some (Ops.RDHWR rt rd)
  -- end 7B S3
  | _ => none

end Manual
