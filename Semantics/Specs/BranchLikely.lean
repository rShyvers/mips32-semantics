import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# BranchLikely — the branch-likely family (delay slot nullified when not taken)

Constructors: `beql` `bnel` `blezl` `bgtzl` `bltzl` `bgezl` `bltzall` `bgezall`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  BEQL p.73-74; BNEL p.104-106; BLEZL p.95-96; BGTZL p.89-91; BLTZL p.101-102; BGEZL p.86-87;
  BLTZALL p.99-100; BGEZALL p.80-81.

Reference: `docs/spec/INSTRUCTION-REF.md`, section ""Branch likely" family (real MIPS32; deprecated in MIPS32, removed in Release 6) — v1.x addition".

## Theorems in this file (9)

  `beql_spec_raw` `bnel_spec_raw` `blezl_spec_raw` `bgtzl_spec_raw` `bltzl_spec_raw`
  `bgezl_spec_raw` `bltzall_spec_raw` `bgezall_spec_raw` `beql_not_taken_squashes_delay_slot`
-/

set_option maxRecDepth 4000

/-! ## `beql bnel blezl bgtzl bltzl bgezl bltzall bgezall`

`docs/spec/INSTRUCTION-REF.md` "branch likely" section. A **taken** branch-likely schedules
`pendingBranch` exactly like its non-likely counterpart (the delay slot executes normally). A
**not-taken** one nullifies its delay-slot instruction: this same step moves `pc` straight to
`pc + 8` and leaves `pendingBranch = none`, so the instruction at `pc + 4` is never fetched,
decoded or executed (see `beql_not_taken_squashes_delay_slot` below). -/

/-- **`beql`/`bnel` step-level shape**: identical field layout and taken
condition to `beq` (`$rs == $rt`), but the not-taken case skips the delay
slot (`pc := pc + 8`, no pending branch) instead of executing it
(INSTRUCTION-REF "beql / bnel" section). -/
theorem beql_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beql rs rt imm))
    (hpb : s.pendingBranch = none) :
    step s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 8#32 } := by
  step_spec

/-- **`bnel`**: the mirror image of `beql` — taken on `$rs ≠ $rt`, squashes
(skips the delay slot (`pc := pc + 8`)) when `$rs == $rt` instead. -/
theorem bnel_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bnel rs rt imm))
    (hpb : s.pendingBranch = none) :
    step s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        { s with pc := s.pc + 8#32 }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  step_spec

/-- **`blezl`**: same condition as `blez` (`$rs ≤ 0`, signed), not-taken
skips the delay slot (`pc := pc + 8`) instead of falling through plainly. -/
theorem blezl_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.blezl rs imm))
    (hpb : s.pendingBranch = none) :
    step s =
      if asSigned (readReg s (regIdxSpec rs)) ≤ 0 then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 8#32 } := by
  step_spec

/-- **`bgtzl`**: same condition as `bgtz` (`$rs > 0`, signed), not-taken
skips the delay slot (`pc := pc + 8`). -/
theorem bgtzl_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgtzl rs imm))
    (hpb : s.pendingBranch = none) :
    step s =
      if 0 < asSigned (readReg s (regIdxSpec rs)) then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 8#32 } := by
  step_spec

/-- **`bltzl`** (REGIMM `rt = 0x02`): same condition as `bltz` (`$rs < 0`,
signed), not-taken skips the delay slot (`pc := pc + 8`). -/
theorem bltzl_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bltzl rs imm))
    (hpb : s.pendingBranch = none) :
    step s =
      if asSigned (readReg s (regIdxSpec rs)) < 0 then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 8#32 } := by
  step_spec

/-- **`bgezl`** (REGIMM `rt = 0x03`): same condition as `bgez` (`$rs ≥ 0`,
signed), not-taken skips the delay slot (`pc := pc + 8`). -/
theorem bgezl_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgezl rs imm))
    (hpb : s.pendingBranch = none) :
    step s =
      if 0 ≤ asSigned (readReg s (regIdxSpec rs)) then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 8#32 } := by
  step_spec

/-- **`bltzall`** (REGIMM `rt = 0x12`): same unconditional-`$ra`-link
convention as `bltzal` (`$ra := PC_next + 4`, written before the
taken/not-taken test, independent of the branch outcome), then the same
`$rs < 0` condition as `bltzl` — not-taken skips the delay slot (`pc := pc + 8`)
instead of plainly falling through, exactly like every other branch-likely
instruction above; the link still happens on the squashed path, matching
INSTRUCTION-REF's explicit note that the link "survives the squash case". -/
theorem bltzall_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bltzall rs imm))
    (hpb : s.pendingBranch = none) :
    step s =
      let pcNext := s.pc + 4#32
      let s' := writeReg s 31 (pcNext + 4#32)
      if asSigned (readReg s (regIdxSpec rs)) < 0 then
        { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
      else
        { s' with pc := s.pc + 8#32 } := by
  step_spec

/-- **`bgezall`** (REGIMM `rt = 0x13`): same unconditional link as
`bltzall`, mirrored branch condition (`$rs ≥ 0`, same as `bgezl`/`bgezal`).
Not-taken skips the delay slot (`pc := pc + 8`); the link still happens either
way. -/
theorem bgezall_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgezall rs imm))
    (hpb : s.pendingBranch = none) :
    step s =
      let pcNext := s.pc + 4#32
      let s' := writeReg s 31 (pcNext + 4#32)
      if 0 ≤ asSigned (readReg s (regIdxSpec rs)) then
        { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
      else
        { s' with pc := s.pc + 8#32 } := by
  step_spec

/-! ### Satisfiable examples

Each pair exercises the taken case (ordinary `pendingBranch` scheduling) and the not-taken case
(`pc + 8`, `pendingBranch` left `none`). -/

-- `beql`: `5 == 5` schedules the target with no squash; `5 == 6` is false
-- and squashes instead of plainly falling through (contrast `beq`'s
-- not-taken example above, where the delay slot still executes).
#guard (let s := stepIn (prog1Spec (.beql 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

#guard (let s := stepIn (prog1Spec (.beql 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)])
        s.pc == textBase + 8#32 && s.pendingBranch == none) = true

-- `bnel`: opposite polarity to `beql`, same squash mechanism.
#guard (let s := stepIn (prog1Spec (.bnel 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

#guard (let s := stepIn (prog1Spec (.bnel 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)])
        s.pc == textBase + 8#32 && s.pendingBranch == none) = true

-- `blezl`/`bgtzl`: same conditions as `blez`/`bgtz`, squash instead of
-- plain fall-through on not-taken.
#guard (let s := stepIn (prog1Spec (.blezl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

#guard (let s := stepIn (prog1Spec (.blezl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)])
        s.pc == textBase + 8#32 && s.pendingBranch == none) = true

#guard (let s := stepIn (prog1Spec (.bgtzl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

#guard (let s := stepIn (prog1Spec (.bgtzl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)])
        s.pc == textBase + 8#32 && s.pendingBranch == none) = true

-- `bltzl`/`bgezl` (REGIMM): same conditions as `bltz`/`bgez`.
#guard (let s := stepIn (prog1Spec (.bltzl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

#guard (let s := stepIn (prog1Spec (.bltzl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)])
        s.pc == textBase + 8#32 && s.pendingBranch == none) = true

#guard (let s := stepIn (prog1Spec (.bgezl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

#guard (let s := stepIn (prog1Spec (.bgezl 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)])
        s.pc == textBase + 8#32 && s.pendingBranch == none) = true

-- `bltzall`/`bgezall` (REGIMM): `$ra` links to `pc + 8` unconditionally in
-- both the taken and squashed cases, mirroring `bltzal`/`bgezal`'s own
-- examples above; the not-taken side lands on `pc + 8` directly.
#guard (let s := stepIn (prog1Spec (.bltzall 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)])
        readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

#guard (let s := stepIn (prog1Spec (.bltzall 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)])
        readReg s 31 == textBase + 8#32 && s.pc == textBase + 8#32 &&
            s.pendingBranch == none) = true

#guard (let s := stepIn (prog1Spec (.bgezall 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)])
        readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

#guard (let s := stepIn (prog1Spec (.bgezall 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)])
        readReg s 31 == textBase + 8#32 && s.pc == textBase + 8#32 &&
            s.pendingBranch == none) = true

/-! ## Branch-likely nullification is a property of `step`

A not-taken branch-likely nullifies its delay-slot instruction. That is
part of the branch-likely's own `step` (it moves `pc` to `pc + 8` and
leaves no pending branch), so the theorem below needs **no hypothesis about
what memory holds at `s.pc + 4`**: a real instruction, undecodable garbage, or
nothing at all — it is never fetched. `run`, being `step` iterated, agrees. -/

/-- **A not-taken `beql` skips its delay slot in one `step`**, whatever the
memory holds there; `run` for one step lands in the same state. -/
theorem beql_not_taken_squashes_delay_slot (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beql rs rt imm))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) :
    step s = { s with pc := s.pc + 8#32 } ∧
      run s 1 = { s with pc := s.pc + 8#32 } := by
  have hstep : step s = { s with pc := s.pc + 8#32 } := by
    rw [beql_spec_raw s w rs rt imm hfetch hdecode hpb]
    simp [hnot]
  refine ⟨hstep, ?_⟩
  show step s = _
  exact hstep

-- Concrete instance: `prog1Spec` maps *only* `textBase` (the `beql`); there
-- is no instruction at `textBase + 4`. One bare `step` reaches
-- `textBase + 8` with no pending branch and no exception.
#guard (let s := stepIn (prog1Spec (.beql 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)])
        s.pc == textBase + 8#32 && s.pendingBranch == none && s.cp0Status == statusCu1Mask) = true
