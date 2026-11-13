import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# Trap — conditional traps and `break`

Constructors: `teq` `tne` `tlt` `tge` `tltu` `tgeu` `teqi` `tnei` `tgei` `tgeiu` `tlti` `tltiu` `break`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  TEQ p.416; TNE p.438; TLT p.434; TGE p.418; TLTU p.437; TGEU p.421; TEQI p.417; TNEI p.439;
  TGEI p.419; TGEIU p.420; TLTI p.435; TLTIU p.436; BREAK p.109.

Reference: `docs/spec/INSTRUCTION-REF.md`, sections "Coprocessor 0 / traps and exceptions (real MIPS32 ISA)"; "Summary table".

## Theorems in this file (13)

  `break_spec_raw` `teq_spec_raw` `tne_spec_raw` `tlt_spec_raw` `tge_spec_raw` `tltu_spec_raw`
  `tgeu_spec_raw` `teqi_spec_raw` `tnei_spec_raw` `tgei_spec_raw` `tgeiu_spec_raw` `tlti_spec_raw`
  `tltiu_spec_raw`
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
theorem break_spec_raw (p : Program) (s : State) (w code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.break code)) :
    step p s = takeException s excCodeBp := by
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  rfl

-- `break_spec_raw`: a concrete `break` lands exactly on the exception
-- vector with the `Bp` exception code packed into `Cause`.
#guard (match step (prog1Spec (.break 0#32)) (initialState textBase) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeBp <<< 2) &&
            s.cp0Status == (statusCu1Mask ||| statusExlMask) && s.pc == exceptionVectorAddr
        | .halt _ => false) = true

/-- **`teq` traps iff `$rs == $rt`**, taking the shared coprocessor-0
exception with `excCode = excCodeTr`; otherwise it is a complete no-op
beyond the ordinary fallthrough to `pc + 4#32` — no CP0 state touched at
all (INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu" section). -/
theorem teq_spec_raw (p : Program) (s : State) (w rs rt code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.teq rs rt code))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

/-- **`tne` traps iff `$rs ≠ $rt`** — the mirror image of `teq`
(INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu" section). -/
theorem tne_spec_raw (p : Program) (s : State) (w rs rt code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tne rs rt code))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt) then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

/-- **`tlt` traps iff `$rs <s $rt`**, a *signed* comparison
(INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu" section: "`tlt`:
`$rs <s $rt` (signed)"). -/
theorem tlt_spec_raw (p : Program) (s : State) (w rs rt code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tlt rs rt code))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) < asSigned (readReg s (regIdxSpec rt)) then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

/-- **`tge` traps iff `$rs ≥s $rt`**, a *signed* comparison — the mirror
image of `tlt` (INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu"
section). -/
theorem tge_spec_raw (p : Program) (s : State) (w rs rt code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tge rs rt code))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) ≥ asSigned (readReg s (regIdxSpec rt)) then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

/-- **`tltu` traps iff `$rs <u $rt`**, an *unsigned* comparison on the raw
bit patterns (INSTRUCTION-REF "teq / tne / tlt / tge / tltu / tgeu"
section: "`tltu`: `$rs <u $rt` (unsigned)"). -/
theorem tltu_spec_raw (p : Program) (s : State) (w rs rt code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tltu rs rt code))
    (hpb : s.pendingBranch = none) :
    step p s =
      if (readReg s (regIdxSpec rs)).toNat < (readReg s (regIdxSpec rt)).toNat then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

/-- **`tgeu` traps iff `$rs ≥u $rt`**, an *unsigned* comparison — the
mirror image of `tltu` (INSTRUCTION-REF "teq / tne / tlt / tge / tltu /
tgeu" section). -/
theorem tgeu_spec_raw (p : Program) (s : State) (w rs rt code : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tgeu rs rt code))
    (hpb : s.pendingBranch = none) :
    step p s =
      if (readReg s (regIdxSpec rs)).toNat ≥ (readReg s (regIdxSpec rt)).toNat then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

-- `teq_spec_raw`/`tne_spec_raw`: equal registers trap under `teq` (and are
-- a no-op under `tne`); unequal registers are the mirror image. One
-- `#guard` per instruction per branch, matching the house style used for
-- `beq`/`bne` above.
#guard (match step (prog1Spec (.teq 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeTr <<< 2) &&
            s.cp0Status == (statusCu1Mask ||| statusExlMask) && s.pc == exceptionVectorAddr
        | .halt _ => false) = true

#guard (match step (prog1Spec (.teq 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == statusCu1Mask
        | .halt _ => false) = true

#guard (match step (prog1Spec (.tne 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)]) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeTr <<< 2) &&
            s.cp0Status == (statusCu1Mask ||| statusExlMask) && s.pc == exceptionVectorAddr
        | .halt _ => false) = true

#guard (match step (prog1Spec (.tne 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == statusCu1Mask
        | .halt _ => false) = true

-- `tlt_spec_raw`/`tge_spec_raw`: `-1` (as `0xffffffff`) is signed-less-than
-- `1`, so `tlt` traps and `tge` does not; swapping the operands flips both.
#guard (match step (prog1Spec (.tlt 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true

#guard (match step (prog1Spec (.tge 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true

-- `tltu_spec_raw`/`tgeu_spec_raw`: the same bit pattern `0xffffffff` is the
-- *largest* unsigned value, so it is never `<u 1` but always `≥u 1`.
#guard (match step (prog1Spec (.tltu 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true

#guard (match step (prog1Spec (.tgeu 8#32 9#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true

/-! ## `teqi`, `tnei`, `tgei`, `tgeiu`, `tlti`, `tltiu`

`docs/spec/INSTRUCTION-REF.md` REGIMM trap-immediate subsection, `docs/spec/MIPS-COVERAGE-GAPS.md`
§3.8. Same shape as the register-register traps above, comparing `$rs` with `signExt16 imm`.
`tgeiu`/`tltiu` sign-extend the immediate first, exactly like `sltiu`, and only then compare the
two bit patterns as unsigned (not zero-extension, and not a signed comparison). -/

/-- **`teqi` traps iff `$rs == sext16(imm)`**, taking the shared
coprocessor-0 exception with `excCode = excCodeTr`; otherwise it is a
complete no-op beyond the ordinary fallthrough to `pc + 4#32` (REGIMM
trap-immediate subsection; mirrors `teq_spec_raw` with `sext16 imm` in
place of `$rt`). -/
theorem teqi_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.teqi rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) == signExt16 imm then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

/-- **`tnei` traps iff `$rs ≠ sext16(imm)`** — the mirror image of `teqi`
(REGIMM trap-immediate subsection). -/
theorem tnei_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tnei rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if readReg s (regIdxSpec rs) ≠ signExt16 imm then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

/-- **`tgei` traps iff `$rs ≥s sext16(imm)`**, a *signed* comparison
(REGIMM trap-immediate subsection; mirrors `tge_spec_raw`). -/
theorem tgei_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tgei rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) ≥ asSigned (signExt16 imm) then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

/-- **`tgeiu` sign-extends the 16-bit immediate to a full 32-bit value
first, exactly like `tgei`, then compares the resulting bit patterns as
*unsigned*** — the "u" affects only the comparison, not the immediate's
extension (same convention as `sltiu`; confirmed against `Step.lean`'s
`.tgeiu` case, which calls `signExt16 imm` and then compares `.toNat`
values). -/
theorem tgeiu_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tgeiu rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if (readReg s (regIdxSpec rs)).toNat ≥ (signExt16 imm).toNat then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

/-- **`tlti` traps iff `$rs <s sext16(imm)`**, a *signed* comparison
(REGIMM trap-immediate subsection; mirrors `tlt_spec_raw`). -/
theorem tlti_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tlti rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if asSigned (readReg s (regIdxSpec rs)) < asSigned (signExt16 imm) then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

/-- **`tltiu` sign-extends the 16-bit immediate to a full 32-bit value
first, exactly like `tlti`, then compares the resulting bit patterns as
*unsigned*** — the mirror image of `tgeiu` (same convention as `sltiu`;
confirmed against `Step.lean`'s `.tltiu` case, which calls `signExt16 imm`
and then compares `.toNat` values). -/
theorem tltiu_spec_raw (p : Program) (s : State) (w rs imm : W32)
    (hfetch : fetchWord p s.pc = some w) (hdecode : decode w = some (.tltiu rs imm))
    (hpb : s.pendingBranch = none) :
    step p s =
      if (readReg s (regIdxSpec rs)).toNat < (signExt16 imm).toNat then
        takeException s excCodeTr
      else
        StepResult.next { s with pc := s.pc + 4#32 } := by
  step_spec

-- `teqi_spec_raw`/`tnei_spec_raw`: `$rs == sext16(imm)` traps under `teqi`
-- (and is a no-op under `tnei`); a mismatch is the mirror image. One
-- `#guard` per instruction per branch, matching the house style used for
-- `teq`/`tne` above.
#guard (match step (prog1Spec (.teqi 8#32 5#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeTr <<< 2) &&
            s.cp0Status == (statusCu1Mask ||| statusExlMask) && s.pc == exceptionVectorAddr
        | .halt _ => false) = true

#guard (match step (prog1Spec (.teqi 8#32 5#32))
          (setRegsSpec (initialState textBase) [(8, 6#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == statusCu1Mask
        | .halt _ => false) = true

#guard (match step (prog1Spec (.tnei 8#32 5#32))
          (setRegsSpec (initialState textBase) [(8, 6#32)]) with
        | .next s =>
          s.cp0Epc == textBase && s.cp0Cause == (excCodeTr <<< 2) &&
            s.cp0Status == (statusCu1Mask ||| statusExlMask) && s.pc == exceptionVectorAddr
        | .halt _ => false) = true

#guard (match step (prog1Spec (.tnei 8#32 5#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)]) with
        | .next s => s.pc == textBase + 4#32 && s.cp0Status == statusCu1Mask
        | .halt _ => false) = true

-- `tgei_spec_raw`/`tlti_spec_raw`: `sext16 0xffff = -1`, so `-1` (as
-- `0xffffffff`) is signed-greater-or-equal to `-1` under `tgei` (traps) but
-- not signed-less-than `-1` under `tlti` (no trap); `1 < 1` is false so
-- `tlti 1` also does not trap on `$rs = 1`.
#guard (match step (prog1Spec (.tgei 8#32 0xffff#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true

#guard (match step (prog1Spec (.tgei 8#32 0xffff#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffe#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true

#guard (match step (prog1Spec (.tlti 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true

#guard (match step (prog1Spec (.tlti 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 1#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true

-- `tgeiu_spec_raw`/`tltiu_spec_raw`: `sext16 1 = 1`, and `0xffffffff` is the
-- *largest* unsigned value, so `$rs = 0xffffffff` is never `<u 1` under
-- `tltiu` but always `≥u 1` under `tgeiu` — the same edge case
-- `sltiu`/`tltu`/`tgeu` above use. A second pair with `sext16 0xffff =
-- 0xffffffff` and `$rs = 1` confirms `tgeiu` really compares unsigned
-- (`1 ≥u 0xffffffff` is false), not signed like `tgei` (where the same
-- inputs trap, since `1 ≥s -1`).
#guard (match step (prog1Spec (.tgeiu 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true

#guard (match step (prog1Spec (.tltiu 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true

#guard (match step (prog1Spec (.tltiu 8#32 1#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true

#guard (match step (prog1Spec (.tgeiu 8#32 0xffff#32))
          (setRegsSpec (initialState textBase) [(8, 1#32)]) with
        | .next s => s.pc == textBase + 4#32
        | .halt _ => false) = true

#guard (match step (prog1Spec (.tgei 8#32 0xffff#32))
          (setRegsSpec (initialState textBase) [(8, 1#32)]) with
        | .next s => s.pc == exceptionVectorAddr
        | .halt _ => false) = true
