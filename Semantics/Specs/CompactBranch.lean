import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures
import Semantics.Specs.DelaySlot

/-!
# CompactBranch — the Release 6 compact branches

Constructors: `bc` `balc` `beqc` `bnec` `bltc` `bgec` `bltuc` `bgeuc` `blezc` `bgezc` `bgtzc`
`bltzc` `beqzc` `bnezc` `blezalc` `bgezalc` `bgtzalc` `bltzalc` `beqzalc` `bnezalc` `bovc` `bnvc`
(`jic`, `jialc`: `Specs/Jump.lean`).

Manual pages (MD00086 Vol II-A Rev 6.06, printed page): BC p.53; BALC p.52; B<cond>C p.82-85;
B{LE,GE,GT,LT,EQ,NE}ZALC p.77-79; BOVC/BNVC p.107-108. Forbidden slots: MD00082 Vol I-A Rev 6.01
§5.3.2, p.62-63.

**What these theorems say.** A compact branch has no delay slot: taken, `pc` is the target at once
(`pc + 4 + offset`, `pendingBranch = none`). A conditional compact branch not taken leaves the next
instruction in its forbidden slot, which the model represents as the delay slot of a not-taken branch:
`pc := pc + 4`, `pendingBranch := some (pc + 8)` (`Exec/Branch.lean`). So a control transfer there raises
Reserved Instruction (`branch_in_delay_slot_reserved_instruction`), an exception there reports
`EPC` = the branch with `Cause.BD = 1`, and any other instruction completes as in a delay slot
(`delay_slot_commits_target`). `BC`/`BALC` never leave a slot.

Like every `_spec_raw` theorem these restate `step` (they are proved by computation, `step_spec`);
the independent correctness result is `Refine.step_eq_manual` (`Refine/CompactBranch.lean` holds the
per-instruction refinements).

## Theorems in this file (26)

  `bc_spec_raw` `balc_spec_raw` `beqc_spec_raw` `bnec_spec_raw` `bltc_spec_raw` `bgec_spec_raw`
  `bltuc_spec_raw` `bgeuc_spec_raw` `blezc_spec_raw` `bgezc_spec_raw` `bgtzc_spec_raw` `bltzc_spec_raw`
  `beqzc_spec_raw` `bnezc_spec_raw` `blezalc_spec_raw` `bgezalc_spec_raw` `bgtzalc_spec_raw`
  `bltzalc_spec_raw` `beqzalc_spec_raw` `bnezalc_spec_raw` `bovc_spec_raw` `bnvc_spec_raw`
  `compact_taken_no_slot` `compact_not_taken_forbidden_slot` `forbidden_slot_cti_reserved`
  `balc_sets_ra`
-/

set_option maxRecDepth 4000

/-- **`bc`: an unconditional compact branch** (BC p.53: `PC ← PC + 4 + sign_extend(offset || 0^2)`,
26-bit offset): no delay slot, no forbidden slot. -/
theorem bc_spec_raw (s : State) (w off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bc off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick { s with pc := s.pc + 4#32 + (signExt26 off <<< 2), pendingBranch := none } := by
  step_spec

/-- **`balc`: `$ra ← pc + 4`, then as `bc`** (BALC p.52). The link is the address of the
instruction after the branch (no delay slot). -/
theorem balc_spec_raw (s : State) (w off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.balc off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick { writeReg s 31 (s.pc + 4#32) with
      pc := s.pc + 4#32 + (signExt26 off <<< 2), pendingBranch := none } := by
  step_spec

/-- Corollary of `balc_spec_raw`: `$ra` reads back exactly `pc + 4`. -/
theorem balc_sets_ra (s : State) (w off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.balc off))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32) (hexec : executesInstr s = true) :
    readReg (step s) (regIdxSpec 31#32) = s.pc + 4#32 := by
  rw [balc_spec_raw s w off hfetch hdecode hpb hexec]
  show readReg (writeReg s 31 (s.pc + 4#32)) (regIdxSpec 31#32) = s.pc + 4#32
  have h31 : regIdxSpec 31#32 = (31 : Fin 32) := by decide
  rw [h31, writeReg_reads_back s 31 (s.pc + 4#32) (by decide) hsize32]

/-- **`beqc`: branch if `GPR[rs] = GPR[rt]`**, compact: taken, `pc ← pc + 4 + offset` at once; not taken, the next
instruction is in the forbidden slot (`pendingBranch := some (pc + 8)`). -/
theorem beqc_spec_raw (s : State) (w rs rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beqc rs rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readReg s (regIdxSpec rs) == readReg s (regIdxSpec rt) then
        { s with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bnec`: branch if `GPR[rs] ≠ GPR[rt]`**, compact: taken, `pc ← pc + 4 + offset` at once; not taken, the next
instruction is in the forbidden slot (`pendingBranch := some (pc + 8)`). -/
theorem bnec_spec_raw (s : State) (w rs rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bnec rs rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readReg s (regIdxSpec rs) != readReg s (regIdxSpec rt) then
        { s with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bltc`: branch if `GPR[rs] < GPR[rt]`, signed**, compact: taken, `pc ← pc + 4 + offset` at once; not taken, the next
instruction is in the forbidden slot (`pendingBranch := some (pc + 8)`). -/
theorem bltc_spec_raw (s : State) (w rs rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bltc rs rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if decide (asSigned (readReg s (regIdxSpec rs)) < asSigned (readReg s (regIdxSpec rt))) then
        { s with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bgec`: branch if `GPR[rs] ≥ GPR[rt]`, signed**, compact: taken, `pc ← pc + 4 + offset` at once; not taken, the next
instruction is in the forbidden slot (`pendingBranch := some (pc + 8)`). -/
theorem bgec_spec_raw (s : State) (w rs rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgec rs rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if decide (asSigned (readReg s (regIdxSpec rt)) ≤ asSigned (readReg s (regIdxSpec rs))) then
        { s with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bltuc`: branch if `GPR[rs] < GPR[rt]`, unsigned**, compact: taken, `pc ← pc + 4 + offset` at once; not taken, the next
instruction is in the forbidden slot (`pendingBranch := some (pc + 8)`). -/
theorem bltuc_spec_raw (s : State) (w rs rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bltuc rs rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if BitVec.ult (readReg s (regIdxSpec rs)) (readReg s (regIdxSpec rt)) then
        { s with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bgeuc`: branch if `GPR[rs] ≥ GPR[rt]`, unsigned**, compact: taken, `pc ← pc + 4 + offset` at once; not taken, the next
instruction is in the forbidden slot (`pendingBranch := some (pc + 8)`). -/
theorem bgeuc_spec_raw (s : State) (w rs rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgeuc rs rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if !BitVec.ult (readReg s (regIdxSpec rs)) (readReg s (regIdxSpec rt)) then
        { s with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`blezc`: branch if `GPR[rt] ≤ 0`**, compact: taken, `pc ← pc + 4 + offset` at once; not taken, the next
instruction is in the forbidden slot (`pendingBranch := some (pc + 8)`). -/
theorem blezc_spec_raw (s : State) (w rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.blezc rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if decide (asSigned (readReg s (regIdxSpec rt)) ≤ 0) then
        { s with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bgezc`: branch if `GPR[rt] ≥ 0`**, compact: taken, `pc ← pc + 4 + offset` at once; not taken, the next
instruction is in the forbidden slot (`pendingBranch := some (pc + 8)`). -/
theorem bgezc_spec_raw (s : State) (w rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgezc rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if decide (0 ≤ asSigned (readReg s (regIdxSpec rt))) then
        { s with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bgtzc`: branch if `GPR[rt] > 0`**, compact: taken, `pc ← pc + 4 + offset` at once; not taken, the next
instruction is in the forbidden slot (`pendingBranch := some (pc + 8)`). -/
theorem bgtzc_spec_raw (s : State) (w rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgtzc rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if decide (0 < asSigned (readReg s (regIdxSpec rt))) then
        { s with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bltzc`: branch if `GPR[rt] < 0`**, compact: taken, `pc ← pc + 4 + offset` at once; not taken, the next
instruction is in the forbidden slot (`pendingBranch := some (pc + 8)`). -/
theorem bltzc_spec_raw (s : State) (w rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bltzc rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if decide (asSigned (readReg s (regIdxSpec rt)) < 0) then
        { s with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`beqzc`: branch if `GPR[rs] = 0` (21-bit offset)**, compact: taken, `pc ← pc + 4 + offset` at once; not taken, the next
instruction is in the forbidden slot (`pendingBranch := some (pc + 8)`). -/
theorem beqzc_spec_raw (s : State) (w rs off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beqzc rs off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readReg s (regIdxSpec rs) == 0#32 then
        { s with pc := s.pc + 4#32 + (signExt21 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bnezc`: branch if `GPR[rs] ≠ 0` (21-bit offset)**, compact: taken, `pc ← pc + 4 + offset` at once; not taken, the next
instruction is in the forbidden slot (`pendingBranch := some (pc + 8)`). -/
theorem bnezc_spec_raw (s : State) (w rs off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bnezc rs off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readReg s (regIdxSpec rs) != 0#32 then
        { s with pc := s.pc + 4#32 + (signExt21 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bovc`: branch if the signed 32-bit addition `GPR[rs] + GPR[rt]` overflows (BOVC p.107)**, compact: taken, `pc ← pc + 4 + offset` at once; not taken, the next
instruction is in the forbidden slot (`pendingBranch := some (pc + 8)`). -/
theorem bovc_spec_raw (s : State) (w rs rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bovc rs rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if addOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (readReg s (regIdxSpec rt)))
          (asSigned (readReg s (regIdxSpec rs) + readReg s (regIdxSpec rt))) then
        { s with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bnvc`: branch if the signed 32-bit addition `GPR[rs] + GPR[rt]` does not overflow (BNVC p.107)**, compact: taken, `pc ← pc + 4 + offset` at once; not taken, the next
instruction is in the forbidden slot (`pendingBranch := some (pc + 8)`). -/
theorem bnvc_spec_raw (s : State) (w rs rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bnvc rs rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if !addOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (readReg s (regIdxSpec rt)))
          (asSigned (readReg s (regIdxSpec rs) + readReg s (regIdxSpec rt))) then
        { s with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { s with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`blezalc`: `$ra ← pc + 4` unconditionally, then branch if `GPR[rt] ≤ 0`** (B{LE,GE,GT,LT,EQ,NE}ZALC
p.77-79), compact with a forbidden slot. `GPR[rt]` is read after the link is written (the order of
the Operation; with `rt = 31` the result is UNPREDICTABLE, p.78, and the model compares the link). -/
theorem blezalc_spec_raw (s : State) (w rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.blezalc rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if decide (asSigned (readReg (writeReg s 31 (s.pc + 4#32)) (regIdxSpec rt)) ≤ 0) then
        { writeReg s 31 (s.pc + 4#32) with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { writeReg s 31 (s.pc + 4#32) with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bgezalc`: `$ra ← pc + 4` unconditionally, then branch if `GPR[rt] ≥ 0`** (B{LE,GE,GT,LT,EQ,NE}ZALC
p.77-79), compact with a forbidden slot. `GPR[rt]` is read after the link is written (the order of
the Operation; with `rt = 31` the result is UNPREDICTABLE, p.78, and the model compares the link). -/
theorem bgezalc_spec_raw (s : State) (w rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgezalc rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if decide (0 ≤ asSigned (readReg (writeReg s 31 (s.pc + 4#32)) (regIdxSpec rt))) then
        { writeReg s 31 (s.pc + 4#32) with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { writeReg s 31 (s.pc + 4#32) with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bgtzalc`: `$ra ← pc + 4` unconditionally, then branch if `GPR[rt] > 0`** (B{LE,GE,GT,LT,EQ,NE}ZALC
p.77-79), compact with a forbidden slot. `GPR[rt]` is read after the link is written (the order of
the Operation; with `rt = 31` the result is UNPREDICTABLE, p.78, and the model compares the link). -/
theorem bgtzalc_spec_raw (s : State) (w rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bgtzalc rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if decide (0 < asSigned (readReg (writeReg s 31 (s.pc + 4#32)) (regIdxSpec rt))) then
        { writeReg s 31 (s.pc + 4#32) with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { writeReg s 31 (s.pc + 4#32) with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bltzalc`: `$ra ← pc + 4` unconditionally, then branch if `GPR[rt] < 0`** (B{LE,GE,GT,LT,EQ,NE}ZALC
p.77-79), compact with a forbidden slot. `GPR[rt]` is read after the link is written (the order of
the Operation; with `rt = 31` the result is UNPREDICTABLE, p.78, and the model compares the link). -/
theorem bltzalc_spec_raw (s : State) (w rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bltzalc rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if decide (asSigned (readReg (writeReg s 31 (s.pc + 4#32)) (regIdxSpec rt)) < 0) then
        { writeReg s 31 (s.pc + 4#32) with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { writeReg s 31 (s.pc + 4#32) with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`beqzalc`: `$ra ← pc + 4` unconditionally, then branch if `GPR[rt] = 0`** (B{LE,GE,GT,LT,EQ,NE}ZALC
p.77-79), compact with a forbidden slot. `GPR[rt]` is read after the link is written (the order of
the Operation; with `rt = 31` the result is UNPREDICTABLE, p.78, and the model compares the link). -/
theorem beqzalc_spec_raw (s : State) (w rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beqzalc rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readReg (writeReg s 31 (s.pc + 4#32)) (regIdxSpec rt) == 0#32 then
        { writeReg s 31 (s.pc + 4#32) with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { writeReg s 31 (s.pc + 4#32) with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-- **`bnezalc`: `$ra ← pc + 4` unconditionally, then branch if `GPR[rt] ≠ 0`** (B{LE,GE,GT,LT,EQ,NE}ZALC
p.77-79), compact with a forbidden slot. `GPR[rt]` is read after the link is written (the order of
the Operation; with `rt = 31` the result is UNPREDICTABLE, p.78, and the model compares the link). -/
theorem bnezalc_spec_raw (s : State) (w rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.bnezalc rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      if readReg (writeReg s 31 (s.pc + 4#32)) (regIdxSpec rt) != 0#32 then
        { writeReg s 31 (s.pc + 4#32) with pc := s.pc + 4#32 + (signExt16 off <<< 2), pendingBranch := none }
      else
        { writeReg s 31 (s.pc + 4#32) with pc := s.pc + 4#32, pendingBranch := some (s.pc + 8#32) }) := by
  step_spec

/-! ## No delay slot; the forbidden slot -/

/-- **A taken compact branch leaves no slot**: after `beqc` with `GPR[rs] = GPR[rt]` the machine is at
the target with nothing pending, so the instruction there runs as an ordinary instruction (a CTI there
is not in a delay or forbidden slot: MD00082 Vol I-A Rev 6.01 §5.3.2.4.4, p.63, "Forbidden Slot Only
if Not Taken"). -/
theorem compact_taken_no_slot (s : State) (w rs rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beqc rs rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true)
    (htaken : readReg s (regIdxSpec rs) = readReg s (regIdxSpec rt)) :
    (step s).pc = s.pc + 4#32 + (signExt16 off <<< 2) ∧ (step s).pendingBranch = none := by
  rw [beqc_spec_raw s w rs rt off hfetch hdecode hpb hexec]
  simp [htaken, timerTick_pc, timerTick_pendingBranch]

/-- **A not-taken conditional compact branch leaves the next instruction in its forbidden slot**:
after `beqc` with `GPR[rs] ≠ GPR[rt]` the machine is at `pc + 4` with the fall-through `pc + 8`
pending, as in the delay slot of a not-taken branch (see the module doc). -/
theorem compact_not_taken_forbidden_slot (s : State) (w rs rt off : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beqc rs rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true)
    (hnot : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt)) :
    (step s).pc = s.pc + 4#32 ∧ (step s).pendingBranch = some (s.pc + 8#32) := by
  rw [beqc_spec_raw s w rs rt off hfetch hdecode hpb hexec]
  simp [hnot, timerTick_pc, timerTick_pendingBranch]

/-- **A control transfer in the forbidden slot raises Reserved Instruction** (MD00086 Vol II-A Rev
6.06, B<cond>C, Restrictions, p.84: "If a control transfer instruction (CTI) is placed in the
forbidden slot of a compact branch, Release 6 implementations are required to signal a Reserved
Instruction exception, but only when the branch is not taken"): after a not-taken `beqc`, a CTI as the
next instruction is not executed; the step takes the Reserved Instruction exception from the slot
(`EPC` = the branch, `Cause.BD = 1` when `EXL = 0`: DECISIONS D6, MD00082 Vol I-A Rev 6.01 §5.3.2.2,
p.62). -/
theorem forbidden_slot_cti_reserved (s : State) (w w2 rs rt off : W32) (instr : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.beqc rs rt off))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true)
    (hnot : readReg s (regIdxSpec rs) ≠ readReg s (regIdxSpec rt))
    (hfetch2 : readMemWord (step s) (step s).pc = some w2) (hdecode2 : decode w2 = some instr)
    (hcti : isBranchLikeSpec instr = true) (hexec2 : executesInstr (step s) = true) :
    step (step s) = timerTick (takeException (step s) excCodeRI) := by
  have h := (compact_not_taken_forbidden_slot s w rs rt off hfetch hdecode hpb hexec hnot).2
  exact branch_in_delay_slot_reserved_instruction (step s) w2 instr hfetch2 hdecode2
    (by rw [h]; rfl) hcti hexec2
