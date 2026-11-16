import Semantics.Exec.Base

/-!
# Exec.System — ERET, WAIT, PAUSE and RDHWR

The execution of ERET, WAIT, PAUSE and RDHWR (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of ERET, WAIT, PAUSE and RDHWR; `none` for every other instruction. -/
def execSystem (s : State) : Instruction → Option State
  -- `eret` (MD00086 "ERET"):
  --   if Status.ERL = 1 then PC ← ErrorEPC; Status.ERL ← 0
  --   else                   PC ← EPC;      Status.EXL ← 0
  --   LLbit ← 0
  -- It has no delay slot: `pc` is set directly. (`eret` *in* a delay slot
  -- never reaches this arm: `execInstr` raises Reserved Instruction for it.)
  | .eret => some <|
    if s.cp0Status &&& statusErlMask != 0#32 then
      { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask, llBit := false }
    else
      { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask, llBit := false }
  -- `wait` (MD00086 Vol II-A Rev 6.06, WAIT, p.442-443): "The WAIT instruction
  -- is implemented by stalling the pipeline at the completion of the
  -- instruction and entering a lower power mode. The pipeline is restarted when
  -- an external event, such as an interrupt or external request occurs, and
  -- execution continues with the instruction following the WAIT instruction".
  -- Pre-Release-6 Operation: "I: Enter implementation dependent lower power
  -- mode / I+1: Potential interrupt taken here". The instruction completes
  -- (`PC ← PC + 4`) and the processor enters standby (`State.standby`); `step`
  -- then does nothing but advance the timer until an interrupt request restarts
  -- it (`standbyStep`, `takeInterrupt`). The 19-bit code selects nothing (every
  -- code is WAIT 0: "If not implemented, then such unimplemented encodings must
  -- default to WAIT 0", p.442), and `Count` keeps counting ("Prior to Release 6,
  -- whether Count is disabled was implementation-dependent", p.442: pin).
  | .wait _ => some <| mkNext s { s with standby := true }
  -- PAUSE (MD00086 Vol II-A Rev 6.06, PAUSE, p.317): "if LLBit ≠ 0 then EPC ← PC + 4 /* Resume at
  -- the following instruction */; DescheduleInstructionStream() endif". "In a single-threaded
  -- processor, this may be implemented as a short-term WAIT operation which resumes at the next
  -- instruction when the LLBit is zero or on some other external event such as an interrupt"
  -- (p.317). Pin: with `LLbit = 1` the processor enters standby as after WAIT (`State.standby`,
  -- `pc` = the next instruction): on this single hart nothing else can clear `LLbit`, so only an
  -- interrupt (or reset) restarts it. With `LLbit = 0` PAUSE is a no-op.
  | .pause => some <|
    if s.llBit then mkNext s { s with cp0Epc := s.pc + 4#32, standby := true } else mkNext s s
  -- `rdhwr` (MD00086 Vol II-A Rev 6.06, RDHWR, p.332-334): `GPR[rt] ← HWR[rd]` when the register is
  -- implemented (`hwrValue`) and access is allowed (`rdhwrAllowed`); "If access is not allowed or the
  -- register is not implemented, a Reserved Instruction Exception is signaled" (p.333). It is not a
  -- coprocessor-0 instruction: outside Kernel Mode it raises Reserved Instruction, never
  -- Coprocessor Unusable ("Exceptions: Reserved Instruction", p.334).
  | .rdhwr rt rd sel => some <|
    -- Release 6: "when the 3-bit sel is undefined for use with a specific register number, then a
    -- Reserved Instruction Exception is signaled" (RDHWR p.333); `sel = 0` is the only defined
    -- value for the registers the model implements.
    -- W2: register 4 (PerfCtr), 5 (XNP), 29 (ULR).
    if sel != 0#32 then takeException s excCodeRI else
    match hwrValue s rd with
    | some v => if rdhwrAllowed s rd then mkNext s (writeReg s (regIdx rt) v)
                else takeException s excCodeRI
    | none => takeException s excCodeRI
  | _ => none
