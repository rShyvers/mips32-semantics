import Semantics.Manual.Exceptions

/-!
# Manual.Reset — the Reset exception

MD00090 Vol III Rev 6.02 §6.2.5 "Reset Exception" (p.89-90).
-/

namespace Manual

/-- **The Reset exception** (§6.2.5, Operation, p.89-90), restricted to the registers of this
profile (Random, PageMask, PageGrain, Wired, EntryHi, SRSMap, WatchLo, PerfCnt do not exist;
`IntCtlVS`, `SRSCtl` are constant 0; `Config1`, `Config2`, `Config3 ← ConfigurationState` (p.90) hold
already: they are the implementation constants `Impl.Config1`/`Config2`/`Config3`):
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
WAIT, p.442). `RP`, `TS`, `SR`, `NMI` are not implemented (they read 0 already; `RP` and `TS` are
reserved in Release 6, "This bit becomes reserved in Release 6", p.89-90).

The Release 6 registers the list does not name have the reset state of their field table where it
gives one: `Config5.SBRI ← 0` (MD00090 Vol III Rev 6.02 Table 9.69, p.263: reset state 0) and
`LLAddr.LLB ← 0`, i.e. `LLbit ← 0` (Table 9.72, p.270: reset state 0); `Config4` and the read-only
fields of `Config5` are "Preset by hardware" (implementation constants); `UserLocal`, `BadInstr`,
`BadInstrP`, `KScratch1..6` have reset state "Undefined" (Tables 9.19, 9.42, 9.43, 9.84) and are
`Oracle.resetUndefined`'s. -/
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
      LowPower := false
      -- BEGIN R6-2
      Config5SBRI := false
      LLbit := false
      -- END R6-2
      }

end Manual
