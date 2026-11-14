import Semantics.Manual.CP0

/-!
# Manual.Exceptions — general exception processing

MD00090 Vol III Rev 6.02 §6.2.3 "General Exception Processing" (p.86-88), with the extra state
of each exception (§6.2.9 Address Error, p.92-93; §6.2.22 Coprocessor Unusable, p.100; §6.2.26
Interrupt, p.102) and the exception codes of Table 9.53 (p.212-213).
-/

namespace Manual

/-- **`Cause.ExcCode` of each exception** (Vol III Table 9.53, p.212-213): Int 0, AdEL 4, AdES 5,
Sys 8, Bp 9, RI 10, CpU 11, Ov 12, Tr 13, FPE 15. -/
def ExcCode : Exception → BitVec 5
  | .Interrupt => 0
  | .AddressErrorLoad _ => 4
  | .AddressErrorStore _ => 5
  | .SystemCall => 8
  | .Breakpoint => 9
  | .ReservedInstruction => 10
  | .CoprocessorUnusable _ => 11
  | .IntegerOverflow => 12
  | .Trap => 13
  | .FloatingPoint => 15

/-- **`FaultingCoprocessorNumber`** (§6.2.3, p.87-88: "CauseCE ← FaultingCoprocessorNumber"): the
unit for Coprocessor Unusable ("CauseCE unit number of the coprocessor being referenced", §6.2.22,
p.100); for any other exception "The CE field is loaded, but not defined" (p.87): the oracle's
choice. -/
def FaultingCoprocessorNumber (o : Oracle) (a : Arch) : Exception → BitVec 2
  | .CoprocessorUnusable u => BitVec.ofNat 2 u
  | e => o.causeCE a e

/-- **"Additional State Saved"** of each exception: Address Error saves `BadVAddr ← failing address`
(§6.2.9, p.93; the TLB registers it also names do not exist with a Fixed Mapping MMU). -/
def AdditionalState (e : Exception) (a : Arch) : Arch :=
  match e with
  | .AddressErrorLoad v | .AddressErrorStore v => { a with BadVAddr := v }
  | _ => a

/-- **`vectorOffset`** (§6.2.3 Operation, p.87-88; Table 6.9, p.85-86): `0x180` when
`StatusEXL = 1`; for an Interrupt, `0x180` when `CauseIV = 0`, else `0x200` "if (StatusBEV = 1) or
(IntCtlVS = 0)" (`IntCtl.VS` = bits 9..5 is 0 on this profile: no vectored interrupts, so the
`VecNum` branch is not transcribed); `0x180` for every other exception (no TLB Refill: no TLB). -/
def vectorOffset (a : Arch) (e : Exception) : W32 :=
  if StatusEXL a then 0x180#32
  else match e with
    | .Interrupt =>
      if !CauseIV a then 0x180#32
      else 0x200#32   -- "(StatusBEV = 1) or (IntCtlVS = 0)": `IntCtl.VS` reads 0 (`Impl.IntCtl`)
    | _ => 0x180#32

/-- **`vectorBase`** (§6.2.3 Operation, p.88): "if StatusBEV = 1 then vectorBase ← 0xBFC0.0200 else
if ArchitectureRevision ≥ 2 then vectorBase ← EBase31..12 || 0x000". -/
def vectorBase (a : Arch) : W32 :=
  if StatusBEV a then 0xBFC00200#32 else EBaseRead a &&& ~~~0xFFF#32

/-- **General exception processing** for exception `e` signalled by the instruction at `a.PC`
(MD00090 Vol III Rev 6.02 §6.2.3, Operation, p.87-88):
```
if StatusEXL = 1 then vectorOffset ← 0x180
else
   if InstructionInBranchDelaySlot then EPC ← restartPC /* PC of branch/jump */; CauseBD ← 1
   else EPC ← restartPC /* PC of instruction */; CauseBD ← 0
   (vector offsets, shadow sets: SRSCtlHSS = 0, so nothing)
CauseCE ← FaultingCoprocessorNumber
CauseExcCode ← ExceptionType
StatusEXL ← 1
PC ← vectorBase31..30 || (vectorBase29..0 + vectorOffset29..0)
```
`restartPC` is the address of the instruction, or of the branch or jump (PC − 4) in a delay slot
(Table 6.11, p.87). "The processor is started at the exception vector" (p.87): the pending `I+1:`
effect of the branch, if any, does not happen. `LLbit ← 0`: "Exceptions between the LL and SC cause
SC to fail" (MD00086 Vol II-A Rev 6.06, SC, p.350). -/
def GeneralExceptionProcessing (o : Oracle) (e : Exception) (a0 : Arch) : Arch :=
  let a := AdditionalState e a0
  let inSlot := a.BranchDelay.isSome
  let restartPC := if inSlot then a.PC - 4#32 else a.PC
  -- if StatusEXL = 1 then (EPC and CauseBD unchanged) else EPC ← restartPC; CauseBD ← inSlot
  let epc := if StatusEXL a then a.EPC else restartPC
  let causeBD :=
    if StatusEXL a then a.Cause
    else if inSlot then a.Cause ||| (1#32 <<< 31) else a.Cause &&& ~~~(1#32 <<< 31)
  -- CauseCE ← FaultingCoprocessorNumber; CauseExcCode ← ExceptionType
  let cause := (causeBD &&& ~~~((3#32 <<< 28) ||| (0x1F#32 <<< 2))) |||
    ((FaultingCoprocessorNumber o a0 e).setWidth 32 <<< 28) ||| ((ExcCode e).setWidth 32 <<< 2)
  -- PC ← vectorBase31..30 || (vectorBase29..0 + vectorOffset29..0)
  let base := vectorBase a0
  let off := vectorOffset a0 e
  { a with
      EPC := epc
      Cause := cause
      Status := a.Status ||| (1#32 <<< 1)   -- StatusEXL ← 1
      PC := base.extractLsb' 30 2 ++ (base.extractLsb' 0 30 + off.extractLsb' 0 30)
      BranchDelay := none
      Nullify := false
      LLbit := false }

end Manual
