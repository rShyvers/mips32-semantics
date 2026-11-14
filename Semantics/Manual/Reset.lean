import Semantics.Manual.Exceptions

/-!
# Manual.Reset — the Reset exception

MD00090 Vol III Rev 6.02 §6.2.5 "Reset Exception" (p.89-90).
-/

namespace Manual

/-- **The Reset exception** (§6.2.5, Operation, p.89-90), restricted to the registers of this
profile (Random, PageMask, PageGrain, Wired, EntryHi, SRSMap, Config2, Config3, WatchLo, PerfCnt do
not exist; `IntCtlVS`, `SRSCtl` are constant 0):
```
HWREna ← 0
StatusRP ← 0; StatusBEV ← 1; StatusTS ← 0; StatusSR ← 0; StatusNMI ← 0; StatusERL ← 1
CauseDC ← 0
EBaseExceptionBase ← 0
Config ← ConfigurationState; ConfigK0 ← 2
if InstructionInBranchDelaySlot then ErrorEPC ← restartPC # PC of branch/jump
else ErrorEPC ← restartPC # PC of instruction
PC ← 0xBFC0 0000
```
"On a Reset Exception, only the following registers have defined state" (p.89): the others are
`Oracle.resetUndefined`. The reset aborts the pending `I+1:` effect and restarts a pipeline stopped
by `WAIT` ("The assertion of any reset or NMI must restart the pipeline", MD00086 Vol II-A Rev 6.06,
WAIT, p.442). `RP`, `TS`, `SR`, `NMI` are not implemented (they read 0 already). -/
def ResetException (o : Oracle) (a0 : Arch) : Arch :=
  let a1 := o.resetUndefined a0
  -- the oracle's Status is limited to the bits Status has on this profile (`StatusWritable`): the
  -- others are not implemented and read 0 (Vol III Table 9.47, p.189-196)
  let a := { a1 with Status := a1.Status &&& StatusWritable }
  let restartPC := if a0.BranchDelay.isSome then a0.PC - 4#32 else a0.PC
  { a with
      HWREna := 0#32
      Status := a.Status ||| (1#32 <<< 22) ||| (1#32 <<< 2)
      Cause := a.Cause &&& ~~~(1#32 <<< 27)
      EBase := 1#32 <<< 31
      ConfigK0 := 2#3
      ErrorEPC := restartPC
      PC := 0xBFC00000#32
      BranchDelay := none
      Nullify := false
      LowPower := false }

end Manual
