import Semantics.Manual.CP0
import Semantics.Manual.Memory

/-!
# Manual.Exceptions — general exception processing

MD00090 Vol III Rev 6.02 §6.2.3 "General Exception Processing" (p.86-88), with the extra state
of each exception (§6.2.9 Address Error, p.92-93; §6.2.22 Coprocessor Unusable, p.100; §6.2.26
Interrupt, p.102) and the exception codes of Table 9.53 (p.212-213); the Release 6 registers
`BadInstr` (§9.25, p.179) and `BadInstrP` (§9.26, p.181), which every exception synchronous to an
instruction writes.
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

/-- `IntCtlVS` (bits 9..5 of IntCtl; Vol III Table 9.48, p.201), "Vector Spacing", as `IntCtl` reads
under `i` (0 under `Impl.WF`). -/
def IntCtlVS (i : Impl) : BitVec 5 := i.IntCtl.extractLsb' 5 5

/-- **`vectorOffset`** (§6.2.3 Operation, p.87-88; Table 6.9, p.85-86): `0x180` when
`StatusEXL = 1`; for an Interrupt, `0x180` when `CauseIV = 0`, else `0x200` "if (StatusBEV = 1) or
(IntCtlVS = 0)"; `0x180` for every other exception (no TLB Refill: no TLB). The vectored arm
(`IntCtlVS ≠ 0`: `VecNum ← VIntPriorityEncoder()`, `vectorOffset ← 0x200 + (VecNum × (IntCtlVS ||
0b00000))`) needs VI or EIC interrupt mode, which this profile does not have (`Config3.VInt = VEIC = 0`);
`Impl.WF` requires `IntCtlVS = 0` ("If neither EIC interrupt mode nor VI mode are implemented ...,
this field is ignored on write and reads as zero", Table 9.48, p.201). That arm is not transcribed:
outside `Impl.WF` the spec gives `0x200` there. -/
def vectorOffset (i : Impl) (a : Arch) (e : Exception) : W32 :=
  if StatusEXL a then 0x180#32
  else match e with
    | .Interrupt =>
      if !CauseIV a then 0x180#32
      -- if (StatusBEV = 1) or (IntCtlVS = 0) then vectorOffset ← 0x200
      else if StatusBEV a || IntCtlVS i == 0#5 then 0x200#32
      -- else (vectored interrupts; not on this profile, see above)
      else 0x200#32
    | _ => 0x180#32

/-- **`vectorBase`** (§6.2.3 Operation, p.88): "if StatusBEV = 1 then vectorBase ← 0xBFC0.0200 else
if ArchitectureRevision ≥ 2 then vectorBase ← EBase31..12 || 0x000". -/
def vectorBase (a : Arch) : W32 :=
  if StatusBEV a then 0xBFC00200#32 else EBaseRead a &&& ~~~0xFFF#32

-- BEGIN R6-2
/-- **The faulting instruction word** (`BadInstr`, MD00090 Vol III Rev 6.02 §9.25, Table 9.42, p.179:
"Faulting instruction word"): the word the instruction fetch at `PC` delivers (`InstructionFetch`).
"When a synchronous exception occurs for which there is no valid instruction word (for example TLB
Refill - Instruction Fetch), the value stored in BadInstr is UNPREDICTABLE" (p.179): when that fetch
signals, the oracle's `badInstrNoWord`. -/
def FaultingInstructionWord (i : Impl) (o : Oracle) (a : Arch) : W32 :=
  match (InstructionFetch.run { impl := i, oracle := o } { arch := a }).1 with
  | .ok w => w
  | .signal _ => o.badInstrNoWord a

/-- **The instruction word at virtual address `vAddr`**: the memory element the Fixed Mapping MMU
maps it to (`FixedMapping` with the current `StatusERL`, `MemElemAt`), without the address check. For
the prior branch of `BadInstrP`: the branch at `PC - 4` was fetched from there. -/
def InstructionWordAt (a : Arch) (vAddr : W32) : W32 :=
  MemElemAt a.Mem (FixedMapping (StatusERL a) vAddr)
-- END R6-2

/-- **General exception processing** for exception `e` signalled by the instruction at `a.PC`
(MD00090 Vol III Rev 6.02 §6.2.3, Operation, p.87-88):
```
if StatusEXL = 1 then vectorOffset ← 0x180
else
   if InstructionInBranchDelaySlot then EPC ← restartPC /* PC of branch/jump */; CauseBD ← 1
   else EPC ← restartPC /* PC of instruction */; CauseBD ← 0
   (vector offsets; shadow sets: SRSCtlHSS = 0 under Impl.WF, so nothing)
CauseCE ← FaultingCoprocessorNumber
CauseExcCode ← ExceptionType
StatusEXL ← 1
PC ← vectorBase31..30 || (vectorBase29..0 + vectorOffset29..0)
```
`restartPC` is the address of the instruction, or of the branch or jump (PC − 4) in a delay slot
(Table 6.11, p.87). "The processor is started at the exception vector" (p.87): the pending `I+1:`
effect of the branch, if any, does not happen. `LLbit` is not changed: the event that makes an `SC`
fail is "An ERET instruction is executed. (Release 5 includes ERETNC, which will not cause the SC to
fail.)" (MD00086 Vol II-A Rev 6.06, SC, p.347); ERETNC "will never cause the SC to fail" (p.179). The
programming note "Exceptions between the LL and SC cause SC to fail" (SC, p.350) holds through the
handler's `ERET`.

**`BadInstr`, `BadInstrP`** (Release 6). The Operation of §6.2.3 does not name them; their pages do:
"The BadInstr register is only set by exceptions which are synchronous to an instruction. The BadInstr
register is not set by Interrupts, NMI, Machine check, Bus Error or Cache Error exceptions" (§9.25,
p.179; the list of exceptions there covers every other exception of this profile: Coprocessor
Unusable, Reserved Instruction, Integer Overflow, Trap, System Call, Breakpoint, Floating-Point,
Address Error); "The BadInstrP register contains the prior branch instruction, when the faulting
instruction is in a branch delay slot" and "When a synchronous exception occurs and the faulting
instruction is not in a branch delay slot, then the value stored in BadInstrP is UNPREDICTABLE"
(§9.26, p.181). So for every exception but the Interrupt: `BadInstr ← FaultingInstructionWord`,
`BadInstrP ←` the word of the branch at `PC - 4` in a delay slot, else the oracle's `badInstrP`. -/
def GeneralExceptionProcessing (i : Impl) (o : Oracle) (e : Exception) (a0 : Arch) : Arch :=
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
  let off := vectorOffset i a0 e
  { a with
      EPC := epc
      Cause := cause
      Status := a.Status ||| (1#32 <<< 1)   -- StatusEXL ← 1
      PC := base.extractLsb' 30 2 ++ (base.extractLsb' 0 30 + off.extractLsb' 0 30)
      BranchDelay := none
      -- BEGIN R6-2
      -- BadInstr / BadInstrP: every exception synchronous to an instruction (not the Interrupt)
      BadInstr := if e = .Interrupt then a.BadInstr else FaultingInstructionWord i o a0
      BadInstrP :=
        if e = .Interrupt then a.BadInstrP
        else if inSlot then InstructionWordAt a0 (a0.PC - 4#32) else o.badInstrP a0
      -- END R6-2
      }

end Manual
