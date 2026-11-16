import Semantics.Manual.CP0

/-!
# Manual.Ops.System — exception return, standby, hardware registers (MD00086 Vol II-A Rev 6.06)

7B S3. `ERET` and `WAIT` are in the COP0 encoding space: the Coprocessor Unusable check ("If access
to Coprocessor 0 is not enabled, a Coprocessor Unusable Exception is signaled", ERET Exceptions
p.178, WAIT Restrictions p.443) is made for the whole space before the Operation runs
(`Manual.Cycle`). `RDHWR` is a SPECIAL3 instruction and makes its own access check.
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

/-- **WAIT code** — MD00086 Vol II-A Rev 6.06, WAIT, p.442-443, pre-Release 6 Operation.
```
I:   Enter implementation dependent lower power mode
I+1: /* Potential interrupt taken here */
```
"The WAIT instruction is implemented by stalling the pipeline at the completion of the instruction
and entering a lower power mode" (Description, p.442). The restart on an external event or an
interrupt, and `Impl.WaitRestartsOnNotEnabled`, are in `Manual.Cycle` (`LowPowerTime`); the `code`
bits (19, implementation-dependent) are not used ("A value of zero for code bits is the default
and must be valid in all implementations"). WAIT is a CTI: in a delay slot Release 6 signals Reserved
Instruction before the Operation (`Manual.Execute`; BEQ, Restrictions, p.72).
-- W2: the Release 6 WAIT Operation (p.442-443) replaces this pre-Release 6 one (DECISIONS D9). -/
def WAIT (_code : W32) : Pseudo Unit := do
  -- I: Enter implementation dependent lower power mode
  Pseudo.modify fun a => { a with LowPower := true }
  -- I+1: /* Potential interrupt taken here */ (Manual.Cycle)

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
is signaled". `sel ≠ 0` is defined for no register implemented here (`PerfCtr`, register 4, needs
performance counters, `Config1.PC = 0`), so it signals Reserved Instruction. Register 29 `UserLocal` is
"if it is implemented" and 30-31 "If they are not implemented, access results in a Reserved
Instruction Exception": none is implemented. `EBaseCPUNum` is `EBase` bits 9..0 (one processor,
`EBaseRead`), `SYNCI_StepSize()` is `Impl.SYNCIStep`, `CountResolution()` is `Impl.CCRes` (Table 5.4,
p.332).
-- W2: register 5 (`XNP` = `Config5.XNP`, DECISIONS D13) and 29 (`UserLocal`) as Release 6 defines
-- them; until then they signal Reserved Instruction, as the model does. -/
def RDHWR (rt rd sel : W32) : Pseudo Unit := do
  let impl ← Pseudo.impl
  let a ← Pseudo.get
  let r := rd.toNat
  -- (Restrictions) a sel undefined for the register: Reserved Instruction
  if sel != 0#32 then SignalException .ReservedInstruction
  else
  -- Restrictions: access is enabled if Coprocessor 0 is enabled, or the HWREna bit is set
  let enabled := CP0Usable a || (r < 4 && bit a.HWREna r)
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
      -- 5, 29, 30, 31 (not implemented), otherwise: SignalException(ReservedInstruction)
      | _ => SignalException .ReservedInstruction
    -- GPR[rt] ← temp
    setGPR (reg rt) temp

end Manual.Ops
