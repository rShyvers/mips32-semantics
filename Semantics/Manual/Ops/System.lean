import Semantics.Manual.CP0
import Semantics.Manual.Interrupts
import Semantics.Manual.Memory

/-!
# Manual.Ops.System — exception return, standby, hardware registers (MD00086 Vol II-A Rev 6.06)

7B S3, wave R6-2. `ERET`, `ERETNC`, `WAIT` and `CACHE` are in the COP0 encoding space: the
Coprocessor Unusable check ("If access to Coprocessor 0 is not enabled, a Coprocessor Unusable
Exception is signaled", ERET Exceptions p.178, ERETNC p.180, WAIT Restrictions p.443, CACHE p.119) is
made for the whole space before the Operation runs (`Manual.Cycle`). `RDHWR` is a SPECIAL3
instruction and makes its own access check.
-/

namespace Manual.Ops

open Manual

/-- **ERET** — MD00086 Vol II-A Rev 6.06, ERET, p.177-178.
```
if StatusERL = 1 then
   temp ← ErrorEPC
   StatusERL ← 0
else
   temp ← EPC
   StatusEXL ← 0
   if (ArchitectureRevision() ≥ 2) and (SRSCtlHSS ≠ 0) and (StatusBEV = 0) then
      SRSCtlCSS ← SRSCtlPSS
   endif
endif
if IsMIPS16Implemented() | (Config3ISA ≠ 0) then
   PC ← temp_{31..1} || 0
   ISAMode ← temp_0
else
   PC ← temp
endif
LLbit ← 0
ClearHazards()
```
"ERET does not execute the next instruction (that is, it has no delay slot)" (Description, p.177),
so `PC ← temp` is at time `I` (`setPC`). `SRSCtl.HSS = 0` (`Impl.WF`): the `SRSCtlCSS ← SRSCtlPSS`
arm is never taken (`SRSCtl.CSS` is not a stored state here).
`IsMIPS16Implemented()` is false and `Config3ISA = 0` (see `Manual.Ops.Jump`). `ClearHazards()`
has no architectural state. ERET is a CTI: in a delay slot Release 6 signals Reserved Instruction
before the Operation (`Manual.Execute`; BEQ, Restrictions, p.72). -/
def ERET : Pseudo Unit := do
  let a ← Pseudo.get
  let temp : W32 ←
    -- if StatusERL = 1 then
    if StatusERL a then do
      -- temp ← ErrorEPC; StatusERL ← 0
      Pseudo.modify fun x => { x with Status := x.Status &&& ~~~(1#32 <<< 2) }
      pure a.ErrorEPC
    else do
      -- temp ← EPC; StatusEXL ← 0
      Pseudo.modify fun x => { x with Status := x.Status &&& ~~~(1#32 <<< 1) }
      -- if (ArchitectureRevision() ≥ 2) and (SRSCtlHSS ≠ 0) and (StatusBEV = 0) then SRSCtlCSS ← SRSCtlPSS
      --   `SRSCtlHSS = 0` (`Impl.WF`): never taken; `SRSCtl.CSS` is not state of the spec
      pure a.EPC
  -- PC ← temp
  setPC temp
  -- LLbit ← 0
  Pseudo.modify fun x => { x with LLbit := false }
  -- ClearHazards(): no architectural state

-- BEGIN R6-2
/-- **ERETNC** — MD00086 Vol II-A Rev 6.06, ERETNC, p.179-180.
```
if StatusERL = 1 then
   temp ← ErrorEPC
   StatusERL ← 0
else
   temp ← EPC
   StatusEXL ← 0
   if (ArchitectureRevision() ≥ 2) and (SRSCtlHSS ≠ 0) and (StatusBEV = 0) then
      SRSCtlCSS ← SRSCtlPSS
   endif
endif
if IsMIPS16Implemented() | (Config3ISA ≠ 0) then
   PC ← temp_{31..1} || 0
   ISAMode ← temp_0
else
   PC ← temp
endif
ClearHazards()
```
"ERETNC is identical to ERET except that an ERETNC will not clear the LLbit" (p.179): the Operation
has no `LLbit ← 0`. "ERETNC does not execute the next instruction (i.e., it has no delay slot)":
`PC ← temp` at time `I`. `SRSCtl.HSS = 0` (`Impl.WF`), `IsMIPS16Implemented()` is false and
`Config3ISA = 0`, as for `ERET`. A CTI: "Release 6 implementations are required to signal a Reserved
Instruction exception if ERETNC is executed in the delay slot" (p.179), before the Operation
(`Manual.Execute`). -/
def ERETNC : Pseudo Unit := do
  let a ← Pseudo.get
  let temp : W32 ←
    -- if StatusERL = 1 then
    if StatusERL a then do
      -- temp ← ErrorEPC; StatusERL ← 0
      Pseudo.modify fun x => { x with Status := x.Status &&& ~~~(1#32 <<< 2) }
      pure a.ErrorEPC
    else do
      -- temp ← EPC; StatusEXL ← 0
      Pseudo.modify fun x => { x with Status := x.Status &&& ~~~(1#32 <<< 1) }
      -- if (ArchitectureRevision() ≥ 2) and (SRSCtlHSS ≠ 0) and (StatusBEV = 0) then SRSCtlCSS ← SRSCtlPSS
      --   `SRSCtlHSS = 0` (`Impl.WF`): never taken
      pure a.EPC
  -- PC ← temp
  setPC temp
  -- ClearHazards(): no architectural state

/-- **CACHE op, offset(base)** — MD00086 Vol II-A Rev 6.06, CACHE, p.114-119 (Release 6 diagram:
9-bit offset).
```
vAddr ← GPR[base] + sign_extend(offset)
(pAddr, uncached) ← AddressTranslation(vAddr, DataReadReference)
CacheOp(op, vAddr, pAddr)
```
This profile has no cache (`Config1.IL = DL = 0`, `Config2.SL = TL = 0`), so every operation/cache
combination is not implemented: "The operation of this instruction is UNDEFINED for any
operation/cache combination that is not implemented. In Release 6, the instruction in this case
should perform no operation" (Restrictions, p.119): `CacheOp` changes nothing (DECISIONS D8).
`DataReadReference` is `AddressTranslation(vAddr, DATA, LOAD)`. -/
def CACHE (base _op off : W32) : Pseudo Unit := do
  -- vAddr ← GPR[base] + sign_extend(offset)
  let vAddr := (← GPR (reg base)) + sign_extend (imm9 off)
  -- (pAddr, uncached) ← AddressTranslation(vAddr, DataReadReference)
  let _ ← AddressTranslation vAddr .DATA .LOAD
  -- CacheOp(op, vAddr, pAddr): no cache, no operation
  pure ()

/-- **WAIT code** — MD00086 Vol II-A Rev 6.06, WAIT, p.442-443, the Release 6 Operation.
```
I:   if IsCoprocessorEnabled(0) then
        while ( !interrupt_pending_and_not_masked_out() &&
                !implementation_dependent_wake_event() )
           <enter or remain in low power mode or stand-by mode>
     else
        SignalException(CoprocessorUnusable, 0)
     endif
I+1: if ( interrupt_pending() && interrupts_enabled() ) then
        EPC ← PC + 4
        < process interrupt; execute ERET eventually >
     else
        // unblock on non-enabled interrupt or imp dep wake event.
        PC ← PC + 4
        < continue execution at instruction after wait >
     endif

function interrupt_pending_and_not_masked_out
   return (Config3VEIC && IntCtlVS && CauseIV && !StatusBEV)
           ? CauseRIPL > StatusIPL : CauseIP & StatusIM;
```
`IsCoprocessorEnabled(0)` is `CP0Usable` (the Cycle makes the same check for the COP0 space first, so
the `else` arm is never reached). `Config3VEIC = 0` (`Impl.WF`): `interrupt_pending_and_not_masked_out`
is `CauseIP & StatusIM` (`InterruptRequests`). This profile has no implementation-dependent wake
event. The `while` loop is one instruction time per iteration once entered: `LowPower` records whether
it is entered (no request pending and not masked out when `WAIT` completes), and each
following instruction time is `Manual.LowPowerTime` until a request is pending and not masked out; the
`I+1:` statements are the Cycle's next instruction time (an enabled interrupt is taken with `EPC` =
the instruction after the `WAIT`, `Manual.InstructionTime`; otherwise execution continues there).
The `code` bits select nothing ("If not implemented, then such unimplemented encodings must default to
WAIT 0", p.442), and `Count` keeps counting ("In Release 6, the encoding of WAIT with bits 24:6 of the
opcode set to 0 will never disable CP0 Count", p.442). WAIT is a CTI: in a delay slot Release 6
signals Reserved Instruction before the Operation (`Manual.Execute`; WAIT, Restrictions, p.442). -/
def WAIT (_code : W32) : Pseudo Unit := do
  let impl ← Pseudo.impl
  let a ← Pseudo.get
  -- if IsCoprocessorEnabled(0) then
  if CP0Usable a then
    -- while (!interrupt_pending_and_not_masked_out() && ...) <enter or remain in low power mode>:
    -- the processor is in the loop (`LowPower`) exactly when no request is pending and not masked out
    Pseudo.modify fun x => { x with LowPower := decide (InterruptRequests impl a = 0#8) }
  -- else SignalException(CoprocessorUnusable, 0)
  else SignalException (.CoprocessorUnusable 0)
  -- I+1: Manual.InstructionTime (the next instruction time)
-- END R6-2

/-- **PAUSE** — MD00086 Vol II-A Rev 6.06, PAUSE, p.317.
```
if LLBit ≠ 0 then
   EPC ← PC + 4                  /* Resume at the following instruction */
   DescheduleInstructionStream()
endif
```
`DescheduleInstructionStream()` is not defined by the manual; the Description says "In a
single-threaded processor, this may be implemented as a short-term WAIT operation which resumes at the
next instruction when the LLBit is zero or on some other external event such as an interrupt" (p.317).
**Pin:** it enters the lower power mode `WAIT` enters (`LowPower`, left by `Manual.LowPowerTime` and
the interrupt of `Manual.InstructionTime`), and the instruction completes (`PC` advances to the next
instruction). On this single processor nothing else clears `LLbit` while the pipeline is stopped.
PAUSE is a CTI ("CTIs include all branches and jumps, NAL, ERET, ERETNC, DERET, WAIT, and PAUSE", BEQ
p.72; "Release 6: Implementations are required to signal a Reserved Instruction exception if PAUSE is
encountered in the delay slot", p.317): `Manual.Execute` signals Reserved Instruction there before the
Operation. -/
def PAUSE : Pseudo Unit := do
  let a ← Pseudo.get
  let pc ← PC
  -- if LLBit ≠ 0 then
  if a.LLbit then
    -- EPC ← PC + 4
    Pseudo.modify fun x => { x with EPC := pc + 4#32 }
    -- DescheduleInstructionStream(): the lower power mode of WAIT (pin)
    Pseudo.modify fun x => { x with LowPower := true }

/-- **RDHWR rt, rd, sel** — MD00086 Vol II-A Rev 6.06, RDHWR, p.332-334 (Release 6 diagram: `sel` in
bits 8..6, bits 10..9 zero).
```
if ((rd≠4) and (sel==0))
   case rd
      0: temp ← EBaseCPUNum
      1: temp ← SYNCI_StepSize()
      2: temp ← Count
      3: temp ← CountResolution()
      if (≥2) 5: temp ← Config5XNP endif     // Release 6
      29: temp ← UserLocal
      30: temp ← Implementation-Dependent-Value
      31: temp ← Implementation-Dependent-Value
      otherwise: SignalException(ReservedInstruction)
   endcase
elseif ((rd==4) and (≥2) and (sel==defined))  // Release 6
   temp ← PerfCtr[sel]
else
endif
GPR[rt] ← temp
```
(the page's first line reads `rs!=4`; the field is `rd`, as in the `elseif` and Table 5.4.)
Restrictions (p.333): "Access to the specified hardware register is enabled if Coprocessor 0 is
enabled, or if the corresponding bit is set in the HWREna register. If access is not allowed or the
register is not implemented, a Reserved Instruction Exception is signaled"; "In Release 6, when the
3-bit sel is undefined for use with a specific register number, then a Reserved Instruction Exception
is signaled". `sel ≠ 0` is defined for no register of this profile: `PerfCtr` (register 4) needs
performance counters (`Config1.PC = 0`; Table 9.40, p.176: "Required if any PerfCnt register is
implemented"), so register 4 is not implemented with any `sel` and signals Reserved Instruction (the
empty `else` arm is not reached with a defined `sel`). Registers 30-31: "If they are not implemented,
access results in a Reserved Instruction Exception"; none is implemented. `EBaseCPUNum` is `EBase` bits
9..0 (one processor, `EBaseRead`), `SYNCI_StepSize()` is `Impl.SYNCIStep`, `CountResolution()` is
`Impl.CCRes` (Table 5.4, p.332), `Config5XNP` is bit 13 of `Config5` (MD00090 Vol III Rev 6.02 Table
9.69, p.261), `UserLocal` the CP0 register (4, 2) ("In Release 6, the UserLocal register is required",
Table 9.40, p.176). -/
def RDHWR (rt rd sel : W32) : Pseudo Unit := do
  let impl ← Pseudo.impl
  let a ← Pseudo.get
  let r := rd.toNat
  -- (Restrictions) a sel undefined for the register: Reserved Instruction
  if sel != 0#32 then SignalException .ReservedInstruction
  else
  -- Restrictions: access is enabled if Coprocessor 0 is enabled, or the HWREna bit is set
  let enabled := CP0Usable a || bit a.HWREna r
  if !enabled then SignalException .ReservedInstruction
  else
    let temp : W32 ← match r with
      -- 0: temp ← EBaseCPUNum
      | 0 => pure (zero_extend (bits (EBaseRead a) 9 0))
      -- 1: temp ← SYNCI_StepSize()
      | 1 => pure impl.SYNCIStep
      -- 2: temp ← Count
      | 2 => pure a.Count
      -- 3: temp ← CountResolution()
      | 3 => pure impl.CCRes
      -- 5: temp ← Config5XNP (Release 6)
      | 5 => pure (zero_extend (bits (Config5Read impl a) 13 13))
      -- 29: temp ← UserLocal
      | 29 => pure a.UserLocal
      -- 4 (no PerfCtr), 30, 31 (not implemented), otherwise: SignalException(ReservedInstruction)
      | _ => SignalException .ReservedInstruction
    -- GPR[rt] ← temp
    setGPR (reg rt) temp

end Manual.Ops
