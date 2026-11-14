import Semantics.Specs.Tactics
import Semantics.Specs.DecodeSpec
import Semantics.Specs.Fixtures

/-!
# Shift — shifts and rotates

Constructors: `sll` `srl` `sra` `sllv` `srlv` `srav` `rotr` `rotrv`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  SLL p.376; SRL p.385; SRA p.383; SLLV p.377; SRLV p.386; SRAV p.384; ROTR p.339; ROTRV p.340.

Reference: `docs/spec/INSTRUCTION-REF.md`, sections "R-type arithmetic / logic"; "MIPS32 GPR multiply and variable shifts (v1.x addition)"; "MIPS32r2 rotate and bitfield extract/insert (v1.x addition)".

## Theorems in this file (11)

  `sll_spec_raw` `srl_spec_raw` `sra_spec_raw` `sllv_spec_raw` `srlv_spec_raw` `srav_spec_raw`
  `rotr_spec_raw` `rotrv_spec_raw` `rotr_wraps_not_zero_fill` `srl_zero_fills_same_input`
  `rotr_output_ne_srl_output`
-/

set_option maxRecDepth 4000

/-! ## `sll`, `srl`, `sra`, `sllv`, `srlv`, `srav`, `rotr`, `rotrv`

INSTRUCTION-REF "R-type shifts"/"R-type variable shifts"/"R-type rotate" sections,
`docs/spec/MIPS-COVERAGE-GAPS.md` §3.4. -/

/-- **`sll` shifts `$rt` left by the fixed `shamt` field, zero-filling the
vacated low bits.** `shamt` comes straight from the instruction encoding
(INSTRUCTION-REF "sll"), not a register. -/
theorem sll_spec_raw (s : State) (w rd rt shamt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sll rd rt shamt))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< shamt.toNat)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< shamt.toNat)).pc + 4#32 }) := by
  -- `step` shifts by the 5-bit field (`shamt.toNat % 32`); `decode` produces `shamt < 32`
  have h : shamt.toNat < 32 := by
    have := decode_wellFormed w _ hdecode; simp only [Instruction.WellFormed] at this; omega
  rw [← Nat.mod_eq_of_lt h]
  step_spec

/-- **`srl` shifts `$rt` right by the fixed `shamt` field, zero-filling the
vacated high bits (logical shift).** Mirrors `sll_spec_raw`; see `sra_spec_raw`
for the sign-filling counterpart. -/
theorem srl_spec_raw (s : State) (w rd rt shamt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.srl rd rt shamt))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) >>> shamt.toNat)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) >>> shamt.toNat)).pc + 4#32 }) := by
  -- `step` shifts by the 5-bit field (`shamt.toNat % 32`); `decode` produces `shamt < 32`
  have h : shamt.toNat < 32 := by
    have := decode_wellFormed w _ hdecode; simp only [Instruction.WellFormed] at this; omega
  rw [← Nat.mod_eq_of_lt h]
  step_spec

/-- **`sra` shifts `$rt` right by the fixed `shamt` field, sign-filling the
vacated high bits (arithmetic shift).** Uses `BitVec.sshiftRight`, the same
helper `step` itself uses, so a negative `$rt` keeps its sign after the
shift (INSTRUCTION-REF "sra"). -/
theorem sra_spec_raw (s : State) (w rd rt shamt : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sra rd rt shamt))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).sshiftRight shamt.toNat)) with
          pc := (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).sshiftRight shamt.toNat)).pc + 4#32 }) := by
  -- `step` shifts by the 5-bit field (`shamt.toNat % 32`); `decode` produces `shamt < 32`
  have h : shamt.toNat < 32 := by
    have := decode_wellFormed w _ hdecode; simp only [Instruction.WellFormed] at this; omega
  rw [← Nat.mod_eq_of_lt h]
  step_spec

/-- **`sllv` shifts `$rt` left by `$rs`'s low 5 bits**, not a fixed `shamt`
field — so a shift-amount register holding e.g. `33` (`0b100001`) behaves
identically to one holding `1` (INSTRUCTION-REF "sllv",
docs/spec/MIPS-COVERAGE-GAPS.md §3.4). `extractLsb 4 0` is the exact masking
expression `step` itself uses. -/
theorem sllv_spec_raw (s : State) (w rd rt rs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sllv rd rt rs))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let amt := ((readReg s (regIdxSpec rs)).extractLsb 4 0).toNat
      { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< amt)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) <<< amt)).pc + 4#32 }) := by
  step_spec

/-- **`srlv` shifts `$rt` right (zero-filling) by `$rs`'s low 5 bits.**
Mirrors `sllv_spec_raw`'s masking; logical (not arithmetic) shift, same as
`srl`. -/
theorem srlv_spec_raw (s : State) (w rd rt rs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.srlv rd rt rs))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let amt := ((readReg s (regIdxSpec rs)).extractLsb 4 0).toNat
      { (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) >>> amt)) with
          pc := (writeReg s (regIdxSpec rd) (readReg s (regIdxSpec rt) >>> amt)).pc + 4#32 }) := by
  step_spec

/-- **`srav` shifts `$rt` right (sign-filling) by `$rs`'s low 5 bits.**
Mirrors `sllv_spec_raw`'s masking and `sra_spec_raw`'s sign-fill. -/
theorem srav_spec_raw (s : State) (w rd rt rs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.srav rd rt rs))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let amt := ((readReg s (regIdxSpec rs)).extractLsb 4 0).toNat
      { (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).sshiftRight amt)) with
          pc := (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).sshiftRight amt)).pc + 4#32 }) := by
  step_spec

/-- **`rotr` rotates `$rt` right by the fixed `sa` field, wrapping bits
shifted off the bottom around to the top** (MIPS32r2; INSTRUCTION-REF "rotr",
docs/spec/MIPS-COVERAGE-GAPS.md §3.4) — unlike `srl`'s zero-fill on the same
input. `BitVec.rotateRight` is the exact operation `step` itself uses. -/
theorem rotr_spec_raw (s : State) (w rd rt sa : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rotr rd rt sa))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      { (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).rotateRight sa.toNat)) with
          pc := (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).rotateRight sa.toNat)).pc + 4#32 }) := by
  -- `step` shifts by the 5-bit field (`sa.toNat % 32`); `decode` produces `sa < 32`
  have h : sa.toNat < 32 := by
    have := decode_wellFormed w _ hdecode; simp only [Instruction.WellFormed] at this; omega
  rw [← Nat.mod_eq_of_lt h]
  step_spec

/-- **`rotrv` rotates `$rt` right by `$rs`'s low 5 bits, wrapping around**
(MIPS32r2; INSTRUCTION-REF "rotrv"). Same masking as `sllv`/`srlv`/`srav`,
same wrap-around as `rotr`. -/
theorem rotrv_spec_raw (s : State) (w rd rt rs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rotrv rd rt rs))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let amt := ((readReg s (regIdxSpec rs)).extractLsb 4 0).toNat
      { (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).rotateRight amt)) with
          pc := (writeReg s (regIdxSpec rd) ((readReg s (regIdxSpec rt)).rotateRight amt)).pc + 4#32 }) := by
  step_spec

-- Satisfiable examples: `sll`/`srl`/`sra` at shamt 0 and 31 (sign-fill vs.
-- zero-fill at the boundary), mirroring `Step.lean`'s own `#guard`s.
#guard (let s := stepIn (prog1Spec (.sll 10#32 8#32 0#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)])
        readReg s 10 == 0x12345678#32) = true

#guard (let s := stepIn (prog1Spec (.sll 10#32 8#32 31#32))
          (setRegsSpec (initialState textBase) [(8, 1#32)])
        readReg s 10 == 0x80000000#32) = true

#guard (let s := stepIn (prog1Spec (.srl 10#32 8#32 31#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32)])
        readReg s 10 == 1#32) = true

#guard (let s := stepIn (prog1Spec (.sra 10#32 8#32 31#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32)])
        readReg s 10 == 0xffffffff#32) = true

-- Satisfiable examples: `sllv`/`srlv`/`srav` masking a shift amount of 33
-- down to 1 (`33 & 0x1f = 1`).
#guard (let s := stepIn (prog1Spec (.sllv 10#32 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 1#32), (9, 33#32)])
        readReg s 10 == 2#32) = true

#guard (let s := stepIn (prog1Spec (.srlv 10#32 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32), (9, 33#32)])
        readReg s 10 == 0x40000000#32) = true

#guard (let s := stepIn (prog1Spec (.srav 10#32 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32), (9, 33#32)])
        readReg s 10 == 0xc0000000#32) = true

-- Satisfiable examples: `rotr`/`rotrv`, including the masked-amount case
-- (`36 & 0x1f = 4`).
#guard (let s := stepIn (prog1Spec (.rotr 10#32 8#32 4#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)])
        readReg s 10 == 0x81234567#32) = true

#guard (let s := stepIn (prog1Spec (.rotrv 10#32 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32), (9, 36#32)])
        readReg s 10 == 0x81234567#32) = true

/-! ### Bad-output rejection: `rotr` genuinely wraps, it is not `srl` in
disguise

A buggy `rotr` implementation might secretly reuse `srl`'s zero-fill (e.g.
by forgetting to reinsert the shifted-out bits). The two theorems below pin
down the exact register `rotr` and `srl` each write for the *same* `$rt`
value and shift amount (`0x12345678` shifted/rotated by `4`), and the
following `decide` shows those two outputs are provably different values —
so the spec captures genuine wrap-around, not just "a rightward shift of
some kind happened". -/

theorem rotr_wraps_not_zero_fill (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rotr 10#32 8#32 4#32))
    (hpb : s.pendingBranch = none)
    (hrt : readReg s (regIdxSpec 8#32) = 0x12345678#32) (hexec : executesInstr s = true) :
    step s = timerTick ({ (writeReg s (regIdxSpec 10#32) 0x81234567#32) with
        pc := (writeReg s (regIdxSpec 10#32) 0x81234567#32).pc + 4#32 }) := by
  rw [rotr_spec_raw s w 10#32 8#32 4#32 hfetch hdecode hpb hexec]
  dsimp only
  rw [hrt]
  rfl

theorem srl_zero_fills_same_input (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.srl 10#32 8#32 4#32))
    (hpb : s.pendingBranch = none)
    (hrt : readReg s (regIdxSpec 8#32) = 0x12345678#32) (hexec : executesInstr s = true) :
    step s = timerTick ({ (writeReg s (regIdxSpec 10#32) 0x01234567#32) with
        pc := (writeReg s (regIdxSpec 10#32) 0x01234567#32).pc + 4#32 }) := by
  rw [srl_spec_raw s w 10#32 8#32 4#32 hfetch hdecode hpb hexec]
  dsimp only
  rw [hrt]
  rfl

/-- **`rotr`'s wrap-around is not optional.** From the same state — the
same `$8 = 0x12345678`, the same shift amount 4 — `rotr` and `srl` step to
states whose `$10` provably differ: `0x81234567` (the low nibble wrapped to
the top) versus `0x01234567` (the low nibble discarded). The two states differ
only in memory (`m'` holds the `srl` at `pc`). -/
theorem rotr_output_ne_srl_output (s : State) (m' : Std.HashMap W32 UInt8) (w w' : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.rotr 10#32 8#32 4#32))
    (hfetch' : readMemWord { s with physMem := m' } s.pc = some w')
    (hdecode' : decode w' = some (.srl 10#32 8#32 4#32))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32)
    (hrt : readReg s (regIdxSpec 8#32) = 0x12345678#32) (hexec : executesInstr s = true) :
    ∃ s1 s2, step s = s1 ∧ step { s with physMem := m' } = s2 ∧
      readReg s1 10 = 0x81234567#32 ∧ readReg s2 10 = 0x01234567#32 ∧
      readReg s1 10 ≠ readReg s2 10 := by
  have h1 : readReg (writeReg s (regIdxSpec 10#32) 0x81234567#32) 10 = 0x81234567#32 :=
    writeReg_reads_back s 10 _ (by decide) hsize32
  have h2 : readReg (writeReg { s with physMem := m' } (regIdxSpec 10#32) 0x01234567#32) 10
      = 0x01234567#32 :=
    writeReg_reads_back { s with physMem := m' } 10 _ (by decide) hsize32
  refine ⟨_, _, rotr_wraps_not_zero_fill s w hfetch hdecode hpb hrt hexec,
    srl_zero_fills_same_input { s with physMem := m' } w' hfetch' hdecode' hpb hrt hexec, h1, h2, ?_⟩
  show readReg (writeReg s (regIdxSpec 10#32) 0x81234567#32) 10
    ≠ readReg (writeReg { s with physMem := m' } (regIdxSpec 10#32) 0x01234567#32) 10
  rw [h1, h2]
  decide

-- Concrete witness tying the two facts together: running `rotr` and `srl`
-- on the same register contents and shift amount produces different
-- results in `$rd`.
#guard readReg (stepIn (prog1Spec (.rotr 10#32 8#32 4#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)])) 10 !=
        readReg (stepIn (prog1Spec (.srl 10#32 8#32 4#32))
          (setRegsSpec (initialState textBase) [(8, 0x12345678#32)])) 10
