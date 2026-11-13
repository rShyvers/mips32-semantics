import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures

/-!
# Branch — conditional branches (compare two registers, compare with zero, and-link)

Constructors: `beq` `bne` `blez` `bgtz` `bltz` `bgez` `bltzal` `bgezal`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  BEQ p.72; BNE p.103; BLEZ p.94; BGTZ p.88; BLTZ p.97; BGEZ p.75; BLTZAL p.98; BGEZAL p.76.

Reference: `docs/spec/INSTRUCTION-REF.md`, sections "Control flow"; "REGIMM zero-comparison branches (real MIPS32 ISA) — v1.x addition".

## Theorems in this file (27)

  `beq_spec_raw` `bne_spec_raw` `beq_taken_spec` `beq_not_taken_spec` `bne_taken_spec`
  `bne_not_taken_spec` `beq_taken_delay_slot_lands_on_target` `blez_spec_raw` `blez_taken_spec`
  `blez_not_taken_spec` `bgtz_spec_raw` `bgtz_taken_spec` `bgtz_not_taken_spec` `bltz_spec_raw`
  `bltz_taken_spec` `bltz_not_taken_spec` `bgez_spec_raw` `bgez_taken_spec` `bgez_not_taken_spec`
  `bltzal_spec_raw` `bltzal_taken_spec` `bltzal_not_taken_spec` `bltzal_sets_ra` `bgezal_spec_raw`
  `bgezal_taken_spec` `bgezal_not_taken_spec` `bgezal_sets_ra`
-/

set_option maxRecDepth 4000

/-- **`beq`/`bne` branch target and condition, in one equation — real
MIPS32 one-delay-slot semantics.** Mirrors `step`'s own code: the
comparison `$rs == $rt` picks between an ordinary fallthrough to `PC_next`
and *scheduling* (not jumping to) `PC_next + (sext16(offset) << 2)` via
`pendingBranch`, with `beq` and `bne` using the comparison the opposite way
around. A taken branch never updates `pc` past `PC_next` in this same step
— the delay-slot instruction at `PC_next` always executes first; the
schedule is committed by the *next* step's `advance` (`Step.lean`), see
`beq_taken_delay_slot_lands_on_target` below for the two-step composition
(SPEC-NOTES §9 item 1; INSTRUCTION-REF Global rule 3 — this supersedes the
old no-delay-slot MARS-default behavior). The hypothesis `hpb` restricts
this equation to the ordinary case where `s` is not itself sitting in
another pending delay slot; see `branch_in_delay_slot_reserved_instruction` for that other
case. -/
theorem beq_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none) :
    step s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  step_spec

theorem bne_spec_raw (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bne rs rt imm))
    (hpb : s.pendingBranch = none) :
    step s =
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  step_spec

/-- **`beq`, taken**: when `$rs = $rt`, `beq` schedules
`PC_next + (offset << 2)` as the pending delay-slot transfer and itself
falls through to `PC_next` — it does **not** jump immediately
(INSTRUCTION-REF Global rule 3: real MIPS32 always executes one delay-slot
instruction first). -/
theorem beq_taken_spec (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt)) :
    step s = { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [beq_spec_raw s w rs rt imm hfetch hdecode hpb, ite_of_pos (by simpa using htaken)]

/-- **`beq`, not taken**: when `$rs ≠ $rt`, control simply falls through to
`PC_next`, exactly as an ordinary instruction — no `pendingBranch` is ever
set (INSTRUCTION-REF "beq" section). -/
theorem beq_not_taken_spec (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) :
    step s = { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [beq_spec_raw s w rs rt imm hfetch hdecode hpb, ite_of_neg (by simpa using hnot)]

/-- **`bne`, taken**: when `$rs ≠ $rt`, schedules `PC_next + (offset << 2)`
— the mirror image of `beq`, same one-delay-slot discipline. -/
theorem bne_taken_spec (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bne rs rt imm))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) :
    step s = { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bne_spec_raw s w rs rt imm hfetch hdecode hpb, ite_of_neg (by simpa using htaken)]

/-- **`bne`, not taken**: when `$rs = $rt`, falls through to `PC_next`. -/
theorem bne_not_taken_spec (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bne rs rt imm))
    (hpb : s.pendingBranch = none)
    (hnot : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt)) :
    step s = { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [bne_spec_raw s w rs rt imm hfetch hdecode hpb, ite_of_pos (by simpa using hnot)]

/-- **Two-step delay-slot composition for a taken `beq`**: the branch's own
step only schedules the target (`beq_taken_spec`); it is the *following*
step — executing the delay-slot instruction — that actually lands `pc` on
it (`advance` in `Step.lean`, triggered by any ordinary, non-branch-like
instruction; demonstrated concretely here with `sll $zero,$zero,0` i.e.
`nop` as the delay-slot filler). This is the theorem that directly
witnesses "real MIPS32 branch delay slot" as a two-instruction behavior,
matching the task's exact semantics rather than only the one-step schedule
captured by `beq_taken_spec`. -/
theorem beq_taken_delay_slot_lands_on_target (s : State) (w w2 rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beq rs rt imm))
    (hpb : s.pendingBranch = none)
    (htaken : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt))
    (hfetch2 : readMemWord s (s.pc + 4#32) = some w2)
    (hdecode2 : decode w2 = some (.sll 0#32 0#32 0#32)) :
    ∃ s1 s2,
      step s = s1 ∧
      step s1 = s2 ∧
      s2.pc = (s.pc + 4#32) + (signExt16 imm <<< 2) := by
  have h1 := beq_taken_spec s w rs rt imm hfetch hdecode hpb htaken
  have h2 : step { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } = { s with pc := (s.pc + 4#32) + (signExt16 imm <<< 2), pendingBranch := none } := by
    unfold step
    rw [show readMemWord ({ s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } : State) ({ s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } : State).pc = some w2 from hfetch2]
    dsimp only
    rw [hdecode2]
    dsimp only
    rfl
  exact ⟨_, _, h1, h2, rfl⟩

/-! ### Satisfiable examples -/

-- `beq_taken_spec`/`beq_not_taken_spec`: equal registers schedule the
-- target via `pendingBranch` and fall through to the delay slot first
-- (real MIPS32 one-delay-slot semantics); unequal registers fall through
-- exactly as an ordinary instruction.
#guard (let s := stepIn (prog1Spec (.beq 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

#guard (let s := stepIn (prog1Spec (.beq 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 8#32)) = true

-- `bne_taken_spec`/`bne_not_taken_spec`: the mirror image of `beq`.
#guard (let s := stepIn (prog1Spec (.bne 8#32 9#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 6#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

-- `beq_taken_delay_slot_lands_on_target`: the delay-slot instruction's own
-- step is what actually lands `pc` on the scheduled target.
#guard (let s1 := stepIn (buildProgSpec textBase [.beq 8#32 9#32 3#32, .sll 0#32 0#32 0#32])
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 5#32)])
        let s2 := step s1
        s2.pc == textBase + 4#32 + 12#32) = true

/-! ## `blez`/`bgtz` and the REGIMM family `bltz`/`bgez`/`bltzal`/`bgezal`

Each `_spec_raw` theorem is one equation with an `if … then … else …` on the branch condition;
the taken / not-taken corollaries follow from it by `ite_of_pos`/`ite_of_neg`, like
`beq_taken_spec`/`beq_not_taken_spec`. (`j`/`jal`/`jr`/`jalr` are in `Jump.lean`.) -/

/-- **`blez` branch target and condition** — single-register comparison
against zero, otherwise identical delay-slot shape to `beq`/`bne`: if
`$rs ≤ 0` (signed, zero included), schedules `PC = PC_next + (offset << 2)`
via `pendingBranch` and itself falls through to `PC_next`; otherwise it is
an ordinary fallthrough with no scheduled transfer (INSTRUCTION-REF "blez"
section). -/
theorem blez_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.blez rs imm))
    (hpb : s.pendingBranch = none) :
    step s =
      if asSigned (readReg s (regIdxSpec rs)) ≤ 0 then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  step_spec

/-- **`blez`, taken**: when `$rs ≤ 0`, schedules `PC_next + (offset << 2)`
as the delay-slot transfer and falls through to `PC_next` first — same
one-delay-slot discipline as `beq` (INSTRUCTION-REF "blez" section). -/
theorem blez_taken_spec (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.blez rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : asSigned (readReg s (regIdxSpec rs)) ≤ 0) :
    step s = { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [blez_spec_raw s w rs imm hfetch hdecode hpb, ite_of_pos htaken]

/-- **`blez`, not taken**: when `$rs > 0`, falls through to `PC_next` with
no scheduled transfer. -/
theorem blez_not_taken_spec (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.blez rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : 0 < asSigned (readReg s (regIdxSpec rs))) :
    step s = { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [blez_spec_raw s w rs imm hfetch hdecode hpb, ite_of_neg (by omega)]

/-- **`bgtz` branch target and condition** — the mirror image of `blez`:
if `$rs > 0` (signed, strictly positive), schedules
`PC = PC_next + (offset << 2)`, same one-delay-slot discipline
(INSTRUCTION-REF "bgtz" section). -/
theorem bgtz_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgtz rs imm))
    (hpb : s.pendingBranch = none) :
    step s =
      if 0 < asSigned (readReg s (regIdxSpec rs)) then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  step_spec

/-- **`bgtz`, taken**: when `$rs > 0`, schedules `PC_next + (offset << 2)`
as the delay-slot transfer. -/
theorem bgtz_taken_spec (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgtz rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : 0 < asSigned (readReg s (regIdxSpec rs))) :
    step s = { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bgtz_spec_raw s w rs imm hfetch hdecode hpb, ite_of_pos htaken]

/-- **`bgtz`, not taken**: when `$rs ≤ 0`, falls through to `PC_next` with
no scheduled transfer. -/
theorem bgtz_not_taken_spec (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgtz rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : asSigned (readReg s (regIdxSpec rs)) ≤ 0) :
    step s = { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [bgtz_spec_raw s w rs imm hfetch hdecode hpb, ite_of_neg (by omega)]

/-- **`bltz` branch target and condition** (REGIMM, opcode `0x01`,
`rt = 0x00`): if `$rs < 0` (signed), schedules
`PC = PC_next + (offset << 2)`, same one-delay-slot discipline as
`blez`/`bgtz` (INSTRUCTION-REF "bltz" section). -/
theorem bltz_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bltz rs imm))
    (hpb : s.pendingBranch = none) :
    step s =
      if asSigned (readReg s (regIdxSpec rs)) < 0 then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  step_spec

/-- **`bltz`, taken**: when `$rs < 0`, schedules `PC_next + (offset << 2)`. -/
theorem bltz_taken_spec (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bltz rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step s = { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bltz_spec_raw s w rs imm hfetch hdecode hpb, ite_of_pos htaken]

/-- **`bltz`, not taken**: when `$rs ≥ 0`, falls through to `PC_next`. -/
theorem bltz_not_taken_spec (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bltz rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : 0 ≤ asSigned (readReg s (regIdxSpec rs))) :
    step s = { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [bltz_spec_raw s w rs imm hfetch hdecode hpb, ite_of_neg (by omega)]

/-- **`bgez` branch target and condition** (REGIMM, `rt = 0x01`) — the
mirror image of `bltz`: if `$rs ≥ 0` (signed, zero included), schedules
`PC = PC_next + (offset << 2)` (INSTRUCTION-REF "bgez" section). -/
theorem bgez_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgez rs imm))
    (hpb : s.pendingBranch = none) :
    step s =
      if 0 ≤ asSigned (readReg s (regIdxSpec rs)) then
        { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  step_spec

/-- **`bgez`, taken**: when `$rs ≥ 0`, schedules `PC_next + (offset << 2)`. -/
theorem bgez_taken_spec (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgez rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : 0 ≤ asSigned (readReg s (regIdxSpec rs))) :
    step s = { s with pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bgez_spec_raw s w rs imm hfetch hdecode hpb, ite_of_pos htaken]

/-- **`bgez`, not taken**: when `$rs < 0`, falls through to `PC_next`. -/
theorem bgez_not_taken_spec (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgez rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step s = { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [bgez_spec_raw s w rs imm hfetch hdecode hpb, ite_of_neg (by omega)]

/-- **`bltzal` links `$ra` to `pc + 8` unconditionally, then — independent
of the link — branches on `$rs < 0` exactly like `bltz`.** This two-part
structure (unconditional link, conditional branch) is the real MIPS32
architectural definition, not a simplification: every execution of
`bltzal` writes `$ra`, whether or not the branch itself is taken
(INSTRUCTION-REF "bltzal" section — `GPR[31] <- PC + 8` happens in the
instruction's own cycle regardless of the branch condition tested one cycle
later). The branch condition reads `$rs` from the state *before* the link
write, matching this simulator's documented resolution of the `rs = $ra`
UNPREDICTABLE case. -/
theorem bltzal_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bltzal rs imm))
    (hpb : s.pendingBranch = none) :
    step s =
      let pcNext := s.pc + 4#32
      let s' := writeReg s 31 (pcNext + 4#32)
      if asSigned (readReg s (regIdxSpec rs)) < 0 then
        { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
      else
        { s' with pc := pcNext, pendingBranch := some (s.pc + 8#32) } := by
  step_spec

/-- **`bltzal`, taken**: `$ra` links to `pc + 8` (as always) and the branch
also schedules `PC_next + (offset << 2)`. -/
theorem bltzal_taken_spec (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bltzal rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step s = { (writeReg s 31 ((s.pc + 4#32) + 4#32)) with
        pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bltzal_spec_raw s w rs imm hfetch hdecode hpb, ite_of_pos htaken]

/-- **`bltzal`, not taken**: `$ra` still links to `pc + 8` (the link is
unconditional), but no transfer is scheduled — control simply falls
through to `PC_next`. -/
theorem bltzal_not_taken_spec (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bltzal rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : 0 ≤ asSigned (readReg s (regIdxSpec rs))) :
    step s = { (writeReg s 31 ((s.pc + 4#32) + 4#32)) with
        pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [bltzal_spec_raw s w rs imm hfetch hdecode hpb, ite_of_neg (by omega)]

/-- Corollary of `bltzal_taken_spec`/`bltzal_not_taken_spec`: `$ra` reads
back exactly `pc + 8` regardless of whether the branch is taken — the
unconditional-link half of `bltzal` stated on its own. -/
theorem bltzal_sets_ra (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bltzal rs imm))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32) :
    ∃ s', step s = s' ∧ readReg s' (regIdxSpec 31#32) = s.pc + 8#32 := by
  have h31 : regIdxSpec 31#32 = (31 : Fin 32) := by decide
  have hreads : readReg (writeReg s 31 ((s.pc + 4#32) + 4#32)) (regIdxSpec 31#32) = s.pc + 8#32 := by
    rw [h31, writeReg_reads_back s 31 ((s.pc + 4#32) + 4#32) (by decide) hsize32, BitVec.add_assoc]
    congr 1
  by_cases htaken : asSigned (readReg s (regIdxSpec rs)) < 0
  · exact ⟨_, bltzal_taken_spec s w rs imm hfetch hdecode hpb htaken, hreads⟩
  · exact ⟨_, bltzal_not_taken_spec s w rs imm hfetch hdecode hpb (by omega), hreads⟩

/-- **`bgezal` links `$ra` to `pc + 8` unconditionally, then branches on
`$rs ≥ 0` exactly like `bgez`** — same unconditional-link/conditional-
branch structure as `bltzal` (INSTRUCTION-REF "bgezal" section). -/
theorem bgezal_spec_raw (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgezal rs imm))
    (hpb : s.pendingBranch = none) :
    step s =
      let pcNext := s.pc + 4#32
      let s' := writeReg s 31 (pcNext + 4#32)
      if 0 ≤ asSigned (readReg s (regIdxSpec rs)) then
        { s' with pc := pcNext, pendingBranch := some (pcNext + (signExt16 imm <<< 2)) }
      else
        { s' with pc := pcNext, pendingBranch := some (s.pc + 8#32) } := by
  step_spec

/-- **`bgezal`, taken**: `$ra` links to `pc + 8` (as always) and the branch
also schedules `PC_next + (offset << 2)`. -/
theorem bgezal_taken_spec (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgezal rs imm))
    (hpb : s.pendingBranch = none)
    (htaken : 0 ≤ asSigned (readReg s (regIdxSpec rs))) :
    step s = { (writeReg s 31 ((s.pc + 4#32) + 4#32)) with
        pc := s.pc + 4#32, pendingBranch := some ((s.pc + 4#32) + (signExt16 imm <<< 2)) } := by
  rw [bgezal_spec_raw s w rs imm hfetch hdecode hpb, ite_of_pos htaken]

/-- **`bgezal`, not taken**: `$ra` still links to `pc + 8` (the link is
unconditional), but no transfer is scheduled. -/
theorem bgezal_not_taken_spec (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgezal rs imm))
    (hpb : s.pendingBranch = none)
    (hnot : asSigned (readReg s (regIdxSpec rs)) < 0) :
    step s = { (writeReg s 31 ((s.pc + 4#32) + 4#32)) with
        pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) } := by
  rw [bgezal_spec_raw s w rs imm hfetch hdecode hpb, ite_of_neg (by omega)]

/-- Corollary of `bgezal_taken_spec`/`bgezal_not_taken_spec`: `$ra` reads
back exactly `pc + 8` regardless of whether the branch is taken. -/
theorem bgezal_sets_ra (s : State) (w rs imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgezal rs imm))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32) :
    ∃ s', step s = s' ∧ readReg s' (regIdxSpec 31#32) = s.pc + 8#32 := by
  have h31 : regIdxSpec 31#32 = (31 : Fin 32) := by decide
  have hreads : readReg (writeReg s 31 ((s.pc + 4#32) + 4#32)) (regIdxSpec 31#32) = s.pc + 8#32 := by
    rw [h31, writeReg_reads_back s 31 ((s.pc + 4#32) + 4#32) (by decide) hsize32, BitVec.add_assoc]
    congr 1
  by_cases htaken : 0 ≤ asSigned (readReg s (regIdxSpec rs))
  · exact ⟨_, bgezal_taken_spec s w rs imm hfetch hdecode hpb htaken, hreads⟩
  · exact ⟨_, bgezal_not_taken_spec s w rs imm hfetch hdecode hpb (by omega), hreads⟩

/-! ### Satisfiable examples (`blez` … `bgezal`) -/

-- `blez_taken_spec`/`blez_not_taken_spec`: `-5 ≤ 0` schedules the target;
-- `5 ≤ 0` is false and falls through.
#guard (let s := stepIn (prog1Spec (.blez 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

#guard (let s := stepIn (prog1Spec (.blez 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 8#32)) = true

-- `bgtz_taken_spec`/`bgtz_not_taken_spec`: the mirror image of `blez`.
#guard (let s := stepIn (prog1Spec (.bgtz 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

#guard (let s := stepIn (prog1Spec (.bgtz 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 8#32)) = true

-- `bltz_taken_spec`/`bltz_not_taken_spec`: `-5 < 0` taken, `5 < 0` false.
#guard (let s := stepIn (prog1Spec (.bltz 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

#guard (let s := stepIn (prog1Spec (.bltz 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 8#32)) = true

-- `bgez_taken_spec`/`bgez_not_taken_spec`: the mirror image of `bltz`.
#guard (let s := stepIn (prog1Spec (.bgez 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

#guard (let s := stepIn (prog1Spec (.bgez 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 8#32)) = true

-- `bltzal_sets_ra`/`bltzal_taken_spec`: `$ra` links unconditionally even
-- though the branch itself is taken here.
#guard (let s := stepIn (prog1Spec (.bltzal 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)])
        readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some (textBase + 4#32 + 12#32)) = true

-- `bltzal_not_taken_spec`: `$ra` *still* links even though `5 < 0` is
-- false and no transfer is scheduled — the unconditional-link half fires
-- regardless of the branch outcome.
#guard (let s := stepIn (prog1Spec (.bltzal 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 5#32)])
        readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 8#32)) = true

-- `bgezal_sets_ra`/`bgezal_not_taken_spec`: same unconditional-link
-- convention as `bltzal`, mirrored branch condition.
#guard (let s := stepIn (prog1Spec (.bgezal 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0xfffffffb#32)])
        readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 && s.pendingBranch == some (textBase + 8#32)) = true

#guard (let s := stepIn (prog1Spec (.bgezal 8#32 3#32))
          (setRegsSpec (initialState textBase) [(8, 0#32)])
        readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some (textBase + 4#32 + 12#32)) = true
