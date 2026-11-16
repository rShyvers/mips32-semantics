import Semantics.Exec.Base

/-!
# Exec.System — ERET, ERETNC, WAIT, PAUSE, RDHWR and CACHE

The execution of ERET, ERETNC, WAIT, PAUSE, RDHWR and CACHE (`execBody`, `Step.lean`, dispatches here through `execTables`). Each arm is
the instruction's effect after `execInstr`'s guards (no control transfer in a delay slot; coprocessor
usable); `none` for every instruction of another family.
-/

/-- The effect of ERET, ERETNC, WAIT, PAUSE, RDHWR and CACHE; `none` for every other instruction. -/
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
  -- BEGIN R6-2
  -- `eretnc` (MD00086 Vol II-A Rev 6.06, ERETNC, p.179-180): the Operation of ERET without
  -- `LLbit ← 0` ("ERETNC is identical to ERET except that an ERETNC will not clear the LLbit").
  -- No delay slot; in a delay slot `execInstr` raises Reserved Instruction (p.179).
  | .eretnc => some <|
    if s.cp0Status &&& statusErlMask != 0#32 then
      { s with pc := s.cp0ErrorEpc, cp0Status := s.cp0Status &&& ~~~statusErlMask }
    else
      { s with pc := s.cp0Epc, cp0Status := s.cp0Status &&& ~~~statusExlMask }
  -- `cache op, offset(base)` (MD00086 Vol II-A Rev 6.06, CACHE, p.114-119): "vAddr ← GPR[base] +
  -- sign_extend(offset); (pAddr, uncached) ← AddressTranslation(vAddr, DataReadReference);
  -- CacheOp(op, vAddr, pAddr)". The model has no cache, so every operation/cache combination is
  -- not implemented: "In Release 6, the instruction in this case should perform no operation"
  -- (p.119; DECISIONS D8). The address translation can fail only for a kernel address in User Mode,
  -- where coprocessor 0 is not usable and `execInstr` has raised Coprocessor Unusable already; it is
  -- kept as the Operation writes it (an Address Error, AdEL, `BadVAddr` = `vAddr`).
  | .cache base _ off => some <|
    let va := readReg s (regIdx base) + signExt9 off
    match translate s va with
    | none => takeAddressException s excCodeAdEL va
    | some _ => mkNext s s
  -- END R6-2
  -- `wait` (MD00086 Vol II-A Rev 6.06, WAIT, p.442-443): "The WAIT instruction
  -- is implemented by stalling the pipeline at the completion of the
  -- instruction and entering a lower power mode. The pipeline is restarted when
  -- an external event, such as an interrupt or external request occurs, and
  -- execution continues with the instruction following the WAIT instruction".
  -- Release 6 Operation: "I: if IsCoprocessorEnabled(0) then while
  -- (!interrupt_pending_and_not_masked_out() && !implementation_dependent_wake_event())
  -- <enter or remain in low power mode or stand-by mode> else SignalException(CoprocessorUnusable,
  -- 0) endif; I+1: if (interrupt_pending() && interrupts_enabled()) then EPC ← PC + 4 <process
  -- interrupt> else PC ← PC + 4 <continue execution at instruction after wait> endif" (p.442-443).
  -- The coprocessor check is `execInstr`'s. The instruction completes (`PC ← PC + 4`) and the
  -- processor enters standby (`State.standby`); `step` then does nothing but advance the timer
  -- until a request that is pending and not masked out restarts it (`standbyStep`; with an enabled
  -- one, `takeInterrupt` with `EPC` = the instruction after the `wait`). The 19-bit code selects
  -- nothing (every code is WAIT 0: "If not implemented, then such unimplemented encodings must
  -- default to WAIT 0", p.442), and `Count` keeps counting ("In Release 6, the encoding of WAIT with
  -- bits 24:6 of the opcode set to 0 will never disable CP0 Count", p.442).
  -- The `while` loop is not entered when a request is already pending and not masked out
  -- (`interruptRequests s ≠ 0`): then the processor does not stop at all.
  | .wait _ => some <| mkNext s { s with standby := interruptRequests s == 0#32 }
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
    -- value for the registers the model implements (`sel` selects among performance counters, of
    -- register 4, which the model does not have).
    if sel != 0#32 then takeException s excCodeRI else
    match hwrValue s rd with
    | some v => if rdhwrAllowed s rd then mkNext s (writeReg s (regIdx rt) v)
                else takeException s excCodeRI
    | none => takeException s excCodeRI
  | _ => none
