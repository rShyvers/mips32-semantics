import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# Trap — conditional traps, `break` and `sigrie`

Constructors: `teq` `tne` `tlt` `tge` `tltu` `tgeu` `break` `sigrie` (Release 6 removed the trap-immediate
instructions TEQI/TNEI/TGEI/TGEIU/TLTI/TLTIU).

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  TEQ p.416; TNE p.438; TLT p.434; TGE p.418; TLTU p.437; TGEU p.421; BREAK p.109; SIGRIE p.375.

Reference: `docs/spec/INSTRUCTION-REF.md`, sections "Coprocessor 0 / traps and exceptions (real MIPS32 ISA)"; "Summary table".

## Theorems in this file (8)

  `break_spec_raw` `sigrie_spec_raw` `teq_spec_raw` `tne_spec_raw` `tlt_spec_raw` `tge_spec_raw`
  `tltu_spec_raw` `tgeu_spec_raw`
-/

set_option maxRecDepth 4000

/-! ## `teq`, `tne`, `tlt`, `tge`, `tltu`, `tgeu`, `break`

`docs/spec/INSTRUCTION-REF.md` "Coprocessor 0 / traps and exceptions" and its "teq / tne / tlt /
tge / tltu / tgeu" / "break" subsections. When the trap fires the right-hand side is
`takeException s code`; `Exception.lean` (`exceptionEntry_*`) states what that does to
`EPC`/`Cause`/`Status`/`pc`. When it does not fire the instruction falls through to `pc + 4`.

Every theorem needs `hpb : s.pendingBranch = none`, even `break` (whose own semantics never
consult `pendingBranch`): `execInstr` first tests `s.pendingBranch.isSome && isBranchLike instr`,
which does not compute until `s.pendingBranch` is known. -/

/-- **`break` unconditionally raises the Breakpoint exception** (ExcCode
9) — in any state, in or out of a delay slot. What `takeException` does to
`EPC`/`Cause`/`Status`/`pc`/`pendingBranch` is stated once, in `Exception.lean`
(`exceptionEntry_*`) (INSTRUCTION-REF "break" section). -/
theorem break_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.break code)) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeBp) := by
  rw [step_of_executesInstr s hexec]; unfold execute
  rw [hfetch]
  dsimp only
  rw [hdecode]
  rfl

-- BEGIN R6-2
/-- **`sigrie` unconditionally raises the Reserved Instruction exception** (ExcCode 10), in any
state, in or out of a delay slot (MD00086 Vol II-A Rev 6.06, SIGRIE, p.375: "SignalException(
ReservedInstruction)"; "Implementations should use exactly the same mechanisms as they use for
reserved instructions that are not defined by the Architecture": the same `takeException s
excCodeRI` as an undecodable word, `step_reserved_instruction`). The 16-bit `code` is "available for
software use" only. -/
theorem sigrie_spec_raw (s : State) (w code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sigrie code))
    (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeRI) := by
  rw [step_of_executesInstr s hexec]; unfold execute
  rw [hfetch]
  dsimp only
  rw [hdecode]
  rfl
-- END R6-2

-- `break_spec_raw`: a concrete `break` lands exactly on the exception
-- vector with the `Bp` exception code packed into `Cause`.
#guard (let s := stepIn (prog1Spec (.break 0#32)) (initialState textBase)
        s.cp0Epc == textBase && s.cp0Cause == (excCodeBp <<< 2) &&
            s.cp0Status == (statusCu1Mask ||| statusExlMask) && s.pc == exceptionVectorAddr) = true

/-- **`teq` traps iff `$rs == $rt`**, taking the shared coprocessor-0
exception with `excCode = excCodeTr`; otherwise it is a complete no-op
beyond the ordinary fallthrough to `pc + 4#32` — no CP0 state touched at
all (INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu" section). -/
theorem teq_spec_raw (s : State) (w rs rt code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.teq rs rt code))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        takeException s excCodeTr
      else
        { s with pc := s.pc + 4#32 }) := by
  step_spec

/-- **`tne` traps iff `$rs ≠ $rt`** — the mirror image of `teq`
(INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu" section). -/
theorem tne_spec_raw (s : State) (w rs rt code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.tne rs rt code))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt) then
        takeException s excCodeTr
      else
        { s with pc := s.pc + 4#32 }) := by
  step_spec

/-- **`tlt` traps iff `$rs <s $rt`**, a *signed* comparison
(INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu" section: "`tlt`:
`$rs <s $rt` (signed)"). -/
theorem tlt_spec_raw (s : State) (w rs rt code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.tlt rs rt code))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if asSigned (readReg s (regIdxSpec rs)) < asSigned (readReg s (regIdxSpec rt)) then
        takeException s excCodeTr
      else
        { s with pc := s.pc + 4#32 }) := by
  step_spec

/-- **`tge` traps iff `$rs ≥s $rt`**, a *signed* comparison — the mirror
image of `tlt` (INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu"
section). -/
theorem tge_spec_raw (s : State) (w rs rt code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.tge rs rt code))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if asSigned (readReg s (regIdxSpec rs)) ≥ asSigned (readReg s (regIdxSpec rt)) then
        takeException s excCodeTr
      else
        { s with pc := s.pc + 4#32 }) := by
  step_spec

/-- **`tltu` traps iff `$rs <u $rt`**, an *unsigned* comparison on the raw
bit patterns (INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu"
section: "`tltu`: `$rs <u $rt` (unsigned)"). -/
theorem tltu_spec_raw (s : State) (w rs rt code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.tltu rs rt code))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if (readReg s (regIdxSpec rs)).toNat < (readReg s (regIdxSpec rt)).toNat then
        takeException s excCodeTr
      else
        { s with pc := s.pc + 4#32 }) := by
  step_spec

/-- **`tgeu` traps iff `$rs ≥u $rt`**, an *unsigned* comparison — the
mirror image of `tltu` (INSTRUCTION-REF "teq / tne / tlt / tge / tltu /
tgeu" section). -/
theorem tgeu_spec_raw (s : State) (w rs rt code : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.tgeu rs rt code))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if (readReg s (regIdxSpec rs)).toNat ≥ (readReg s (regIdxSpec rt)).toNat then
        takeException s excCodeTr
      else
        { s with pc := s.pc + 4#32 }) := by
  step_spec

-- `teq_spec_raw`/`tne_spec_raw`: equal registers trap under `teq` (and are
-- a no-op under `tne`); unequal registers are the mirror image. One
-- `#guard` per instruction per branch, matching the house style used for
-- `beq`/`bne` above.
#guard (let s := stepIn (prog1Spec (.teq 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)])
        s.cp0Epc == textBase && s.cp0Cause == (excCodeTr <<< 2) &&
            s.cp0Status == (statusCu1Mask ||| statusExlMask) && s.pc == exceptionVectorAddr) = true

#guard (let s := stepIn (prog1Spec (.teq 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)])
        s.pc == textBase + 4#32 && s.cp0Status == statusCu1Mask) = true

#guard (let s := stepIn (prog1Spec (.tne 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)])
        s.cp0Epc == textBase && s.cp0Cause == (excCodeTr <<< 2) &&
            s.cp0Status == (statusCu1Mask ||| statusExlMask) && s.pc == exceptionVectorAddr) = true

#guard (let s := stepIn (prog1Spec (.tne 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)])
        s.pc == textBase + 4#32 && s.cp0Status == statusCu1Mask) = true

-- `tlt_spec_raw`/`tge_spec_raw`: `-1` (as `0xffffffff`) is signed-less-than
-- `1`, so `tlt` traps and `tge` does not; swapping the operands flips both.
#guard (let s := stepIn (prog1Spec (.tlt 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)])
        s.pc == exceptionVectorAddr) = true

#guard (let s := stepIn (prog1Spec (.tge 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)])
        s.pc == textBase + 4#32) = true

-- `tltu_spec_raw`/`tgeu_spec_raw`: the same bit pattern `0xffffffff` is the
-- *largest* unsigned value, so it is never `<u 1` but always `≥u 1`.
#guard (let s := stepIn (prog1Spec (.tltu 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)])
        s.pc == textBase + 4#32) = true

#guard (let s := stepIn (prog1Spec (.tgeu 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)])
        s.pc == exceptionVectorAddr) = true
