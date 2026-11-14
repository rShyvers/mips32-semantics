import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures
import Semantics.Specs.DecodeSpec

/-!
# Jump — jumps and calls (`j`/`jal`/`jr`/`jalr`)

Constructors: `j` `jal` `jr` `jalr`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  J p.194; JAL p.195; JR p.206-207; JALR p.196-197.

Reference: `docs/spec/INSTRUCTION-REF.md`, sections "Control flow"; "Register-indirect jump/call (real MIPS32 ISA)".

## Theorems in this file (8)

  `target_mask_of_lt` `jal_spec_raw` `jal_sets_ra` `j_spec_raw` `jr_spec_raw` `jalr_spec_raw` `jalr_sets_rd`
  `jalr_rd_eq_rs_targets_original_value`
-/

set_option maxRecDepth 4000

/-- A decoded jump's `target` fits the 26-bit `instr_index` field, so the model's mask of it is the
identity (`decode_wellFormed`). -/
theorem target_mask_of_lt (target : W32) (h : target.toNat < 2 ^ 26) :
    target &&& 0x3FFFFFF#32 = target := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x3FFFFFF#32).toNat = 2 ^ 26 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

/-- **`jal` links `$ra` to `pc + 8` — past the delay slot, not `PC_next`
(`pc + 4`) — and schedules a jump to a target whose top 4 bits come from
`PC_next`, not from `jal`'s own address** (INSTRUCTION-REF Global rule 3:
real MIPS32's `jal` link value is the address of the instruction *after*
the delay slot, since the delay-slot instruction itself still executes
before control can return to `$ra`). Like `beq`/`bne`, `jal` schedules the
jump via `pendingBranch` and itself falls through to `PC_next`; it never
jumps in the same step. -/
theorem jal_spec_raw (s : State) (w target : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jal target))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let pcNext := s.pc + 4#32
      { (writeReg s 31 (pcNext + 4#32)) with
          pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) }) := by
  have hm := target_mask_of_lt target (decode_wellFormed w _ hdecode)
  rw [← hm]
  step_spec

/-- Corollary of `jal_spec_raw`: `$ra` (register 31) reads back exactly
`pc + 8`, i.e. the address of the instruction *after* the delay slot
(`jal`'s own address plus 8), not `pc + 4`. -/
theorem jal_sets_ra (s : State) (w target : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jal target))
    (hpb : s.pendingBranch = none)
    (hsize32 : s.regs.size = 32) (hexec : executesInstr s = true) :
    ∃ s', step s = s' ∧ readReg s' (regIdxSpec 31#32) = s.pc + 8#32 := by
  refine ⟨_, jal_spec_raw s w target hfetch hdecode hpb hexec, ?_⟩
  show readReg (writeReg s 31 ((s.pc + 4#32) + 4#32)) (regIdxSpec 31#32) = s.pc + 8#32
  have h31 : regIdxSpec 31#32 = (31 : Fin 32) := by decide
  rw [h31, writeReg_reads_back s 31 ((s.pc + 4#32) + 4#32) (by decide) hsize32,
    BitVec.add_assoc]
  congr 1

/-! ### Satisfiable examples -/

-- `jal_sets_ra`: `$ra` ends up exactly `pc + 8` (past the delay slot), and
-- the jump is scheduled (not immediate) with its target's top 4 bits
-- coming from `pc + 4`, not from `jal`'s own address.
#guard (let s := stepIn (prog1Spec (.jal 0x1000#32)) (initialState textBase)
        readReg s 31 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some 0x4000#32) = true

/-- **`j` unconditionally schedules a jump whose top 4 bits come from
`PC_next`, not from `j`'s own address** — the same pseudo-direct target
composition as `jal`, minus the link-register write (INSTRUCTION-REF "j"
section). Like every other jump/branch here, `j` itself falls through to
`PC_next` and never jumps in the same step; the delay-slot instruction
always executes first. -/
theorem j_spec_raw (s : State) (w target : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.j target))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let pcNext := s.pc + 4#32
      { s with pc := pcNext, pendingBranch := some ((pcNext &&& 0xf0000000#32) ||| (target <<< 2)) }) := by
  have hm := target_mask_of_lt target (decode_wellFormed w _ hdecode)
  rw [← hm]
  step_spec

/-- **`jr` schedules a jump to the raw 32-bit value held in `$rs`** — not a
26-bit composed target like `j`, the full register value (INSTRUCTION-REF
"jr" section). A misaligned target is not special-cased here: it surfaces
as an Address Error (AdEL) exception the next time `step` tries to fetch from it.
Same one-delay-slot discipline as every other jump/branch: `jr` itself
falls through to `PC_next`. -/
theorem jr_spec_raw (s : State) (w rs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jr rs))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      { s with pc := s.pc + 4#32, pendingBranch := some (readReg s (regIdxSpec rs)) }) := by
  step_spec

/-- **`jalr` links `$rd` to `pc + 8` (the same `jal`/`jalr` link-value
convention — past the delay slot) and schedules a jump to the raw value
held in `$rs`, read *before* `$rd` is overwritten** — so `rd == rs`
aliasing is always safe (INSTRUCTION-REF "jalr" section). This is `step`'s
own code restated: the target expression reads `$rs` from the original `s`,
not from the just-written state, exactly matching the "If `rd == rs`..."
paragraph in the spec. -/
theorem jalr_spec_raw (s : State) (w rs rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jalr rs rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let pcNext := s.pc + 4#32
      { (writeReg s (regIdxSpec rd) (pcNext + 4#32)) with
          pc := pcNext, pendingBranch := some (readReg s (regIdxSpec rs)) }) := by
  step_spec

/-- Corollary of `jalr_spec_raw`: `$rd` reads back exactly `pc + 8` — past
the delay slot, the same link-value convention as `jal`'s `$ra`. Requires
`$rd` to not itself be `$zero` (a write to `$zero` is always a no-op, see
`writeReg_preserves_zero_slot`). -/
theorem jalr_sets_rd (s : State) (w rs rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jalr rs rd))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32)
    (hrdnz : regIdxSpec rd ≠ (0 : Fin 32)) (hexec : executesInstr s = true) :
    ∃ s', step s = s' ∧ readReg s' (regIdxSpec rd) = s.pc + 8#32 := by
  refine ⟨_, jalr_spec_raw s w rs rd hfetch hdecode hpb hexec, ?_⟩
  show readReg (writeReg s (regIdxSpec rd) ((s.pc + 4#32) + 4#32)) (regIdxSpec rd) = s.pc + 8#32
  rw [writeReg_reads_back s (regIdxSpec rd) ((s.pc + 4#32) + 4#32) hrdnz hsize32, BitVec.add_assoc]
  congr 1

/-- **`jalr $rs, $rs` (`rd == rs`) jumps to the *original* `$rs` value, not
the just-written link value** — the one subtlety specific to `jalr`
(INSTRUCTION-REF "jalr" section, "If `rd == rs`..." paragraph). Both halves
are named explicitly: the scheduled jump target is the pre-write `$rs`
value (`s`, not the post-write state), and the register itself afterward
holds the link value `pc + 8` — in general a different value, so aliasing
`rd`/`rs` (the common real-MIPS32 `jalr $t9` idiom with an implicit
`rd = $ra`, or an explicit `jalr $t9, $t9`) never loses the jump target. -/
theorem jalr_rd_eq_rs_targets_original_value (s : State) (w rs : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.jalr rs rs))
    (hpb : s.pendingBranch = none) (hsize32 : s.regs.size = 32)
    (hrsnz : regIdxSpec rs ≠ (0 : Fin 32)) (hexec : executesInstr s = true) :
    ∃ s', step s = s' ∧
      s'.pendingBranch = some (readReg s (regIdxSpec rs)) ∧
      readReg s' (regIdxSpec rs) = s.pc + 8#32 := by
  refine ⟨_, jalr_spec_raw s w rs rs hfetch hdecode hpb hexec, rfl, ?_⟩
  show readReg (writeReg s (regIdxSpec rs) ((s.pc + 4#32) + 4#32)) (regIdxSpec rs) = s.pc + 8#32
  rw [writeReg_reads_back s (regIdxSpec rs) ((s.pc + 4#32) + 4#32) hrsnz hsize32, BitVec.add_assoc]
  congr 1

-- `j_spec_raw`: an unconditional jump schedules the composed target and
-- falls through to the delay slot first, same target-composition formula
-- as `jal`'s own example above.
#guard (let s := stepIn (prog1Spec (.j 0x1000#32)) (initialState textBase)
        s.pc == textBase + 4#32 && s.pendingBranch == some 0x4000#32) = true

-- `jr_spec_raw`: schedules the raw register value, not a composed target.
#guard (let s := stepIn (prog1Spec (.jr 8#32))
          (setRegsSpec (initialState textBase) [(8, 0x80020000#32)])
        s.pc == textBase + 4#32 && s.pendingBranch == some 0x80020000#32) = true

-- `jalr_sets_rd`: `$t1` ends up exactly `pc + 8`, and the jump target is
-- the raw value read out of `$t0`.
#guard (let s := stepIn (prog1Spec (.jalr 8#32 9#32))
          (setRegsSpec (initialState textBase) [(8, 0x80020000#32)])
        readReg s 9 == textBase + 8#32 && s.pc == textBase + 4#32 &&
            s.pendingBranch == some 0x80020000#32) = true

-- `jalr_rd_eq_rs_targets_original_value`: `jalr $t1, $t1` still schedules
-- the *original* `$t1` value as the jump target, even though `$t1` itself
-- is overwritten with the link value `pc + 8` in the same step.
#guard (let s := stepIn (prog1Spec (.jalr 9#32 9#32))
          (setRegsSpec (initialState textBase) [(9, 0x80020000#32)])
        s.pendingBranch == some 0x80020000#32 && readReg s 9 == textBase + 8#32 &&
            s.pendingBranch ≠ some (readReg s 9)) = true
