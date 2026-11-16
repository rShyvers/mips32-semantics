import Semantics.Specs.Tactics
import Semantics.Specs.Fixtures
import Semantics.Specs.Invariants

/-!
# Arith — R-type arithmetic, logic and compare

Constructors: `add` `addu` `sub` `subu` `and` `or` `xor` `nor` `slt` `sltu`.

Manual pages (MD00086 Vol II-A Rev 6.06, printed page, as listed per constructor in `docs/TRACE.md`):
  ADD p.33; ADDU p.38-39; SUB p.388; SUBU p.390; AND p.44; OR p.314; XOR p.446; NOR p.313;
  SLT p.378; SLTU p.381.

Reference: `docs/spec/INSTRUCTION-REF.md`, sections "R-type arithmetic / logic"; "MIPS32 / MIPS32r2 additions (beyond the MARS-matched v1 baseline)".

## Theorems in this file (14)

  `add_spec_raw` `step_add_preserves_zero_register` `sub_spec_raw` `add_overflow_raises_ov`
  `sub_overflow_raises_ov` `add_overflow_not_wrapped` `addu_spec_raw` `subu_spec_raw`
  `and_spec_raw` `or_spec_raw` `xor_spec_raw` `nor_spec_raw` `slt_spec_raw` `sltu_spec_raw`
-/

set_option maxRecDepth 4000

/-- **`add` computes the exact sum, or traps exactly on signed overflow.**
This is `step`'s own code, restated with public names: the raw sum is
formed, `addOverflowsSpec` is INSTRUCTION-REF's Java-derived overflow test
("add" section), and the instruction either raises
Integer Overflow (`takeException s excCodeOv`) or writes the sum and advances the program counter by
4. Every other `add`-related theorem is a corollary of this one. -/
theorem add_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.add rs rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let av := readReg s (regIdxSpec rs)
      let bv := readReg s (regIdxSpec rt)
      let sumBV := av + bv
      if addOverflowsSpec (asSigned av) (asSigned bv) (asSigned sumBV) then
        takeException s excCodeOv
      else
        { (writeReg s (regIdxSpec rd) sumBV) with
            pc := (writeReg s (regIdxSpec rd) sumBV).pc + 4#32 }) := by
  step_spec

/-- Closed weaker version of `step_preserves_zero_register`, for the
representative case of `add` (the trickiest arithmetic instruction, since it
has both an exception branch and a register-writing branch): whichever branch
`step` takes, register `0` reads the same value before and after. -/
theorem step_add_preserves_zero_register (s s' : State) (w rs rt rd : W32)
    (hfw : readMemWord s s.pc = some w) (hdw : decode w = some (.add rs rt rd))
    (hpb : s.pendingBranch = none)
    (hstep : step s = s') : readReg s' 0 = readReg s 0 := by
  cases hexec : executesInstr s
  · rw [← hstep]; exact step_preserves_zero_register s
  rw [add_spec_raw s w rs rt rd hfw hdw hpb hexec] at hstep
  dsimp only at hstep
  split at hstep
  · cases hstep; rfl
  · have hs := hstep
    rw [← hs]
    exact writeReg_preserves_zero_slot s _ _

/-- **`sub` computes the exact difference, or traps exactly on signed
overflow.** Mirrors `add_spec_raw`; `subOverflowsSpec` is INSTRUCTION-REF's
"sub" overflow test. -/
theorem sub_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sub rs rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let av := readReg s (regIdxSpec rs)
      let bv := readReg s (regIdxSpec rt)
      let diffBV := av - bv
      if subOverflowsSpec (asSigned av) (asSigned bv) (asSigned diffBV) then
        takeException s excCodeOv
      else
        { (writeReg s (regIdxSpec rd) diffBV) with
            pc := (writeReg s (regIdxSpec rd) diffBV).pc + 4#32 }) := by
  step_spec

/-- **`add` overflow raises Integer Overflow (ExcCode 12), in or out of a
delay slot** — no `pendingBranch` hypothesis. `$rd` is not written
(`exceptionEntry_always`: exception entry changes no general register);
`EPC`/`Cause.BD` follow `exceptionEntry_*`. -/
theorem add_overflow_raises_ov (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.add rs rt rd))
    (hov : addOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (readReg s (regIdxSpec rt)))
      (asSigned (readReg s (regIdxSpec rs) + readReg s (regIdxSpec rt))) = true) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeOv) := by
  rw [step_of_executesInstr s hexec]; unfold execute
  rw [hfetch]
  dsimp only
  rw [hdecode]
  show timerTick (if addOverflows _ _ _ = true then takeException s excCodeOv else _) = _
  rw [ite_of_pos hov]

/-- **`sub` overflow raises Integer Overflow**, in or out of a delay slot. -/
theorem sub_overflow_raises_ov (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sub rs rt rd))
    (hov : subOverflowsSpec (asSigned (readReg s (regIdxSpec rs))) (asSigned (readReg s (regIdxSpec rt)))
      (asSigned (readReg s (regIdxSpec rs) - readReg s (regIdxSpec rt))) = true) (hexec : executesInstr s = true) :
    step s = timerTick (takeException s excCodeOv) := by
  rw [step_of_executesInstr s hexec]; unfold execute
  rw [hfetch]
  dsimp only
  rw [hdecode]
  show timerTick (if subOverflows _ _ _ = true then takeException s excCodeOv else _) = _
  rw [ite_of_pos hov]

/-! ### Satisfiable examples -/

-- `add_spec_raw`: 5 + 7 does not overflow, giving a `.next` state with
-- `$t2 = 12` and `pc` advanced by 4.
example : decode (encode (Instruction.add 8#32 9#32 10#32)) = some (.add 8#32 9#32 10#32) := by decide

#guard (let s := stepIn (prog1Spec (.add 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)])
        readReg s 10 == 12#32 && s.pc == textBase + 4#32) = true

-- `step_add_preserves_zero_register`: a concrete non-overflowing `add`
-- leaves register `0` at `0`.
#guard (let s := stepIn (prog1Spec (.add 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 5#32), (9, 7#32)])
        readReg s 0 == 0#32) = true

-- `sub_spec_raw`: `0x80000000 - 1` overflows (INT_MIN minus a positive is
-- itself non-negative after wraparound), so `sub` raises Integer Overflow.
#guard (let s' := stepIn (prog1Spec (.sub 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x80000000#32), (9, 1#32)])
        causeExcCode s' == excCodeOv && s'.pc == exceptionVectorAddr) = true

/-! ### Bad-output rejection -/

/-- **Overflow does not silently wrap.** A buggy `add` might wrap
`0x7fffffff + 1` to `0x80000000`, write it to `$10` and continue; the real
`add` raises the Integer Overflow exception (ExcCode 12) instead: the step
is exactly exception entry, and exception entry changes no general
register — in particular the destination `$10` is not written. -/
theorem add_overflow_not_wrapped (s : State) (w : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.add 8#32 9#32 10#32))
    (hpb : s.pendingBranch = none)
    (ha : readReg s (regIdxSpec 8#32) = 0x7fffffff#32)
    (hb : readReg s (regIdxSpec 9#32) = 1#32) (hexec : executesInstr s = true) :
    step s = timerTick (exceptionEntry s excCodeOv) ∧
      (exceptionEntry s excCodeOv).regs = s.regs := by
  refine ⟨?_, rfl⟩
  rw [add_spec_raw s w 8#32 9#32 10#32 hfetch hdecode hpb hexec]
  dsimp only
  rw [ha, hb]
  rfl

-- Concrete witness: `0x7fffffff + 1` raises Integer Overflow (ExcCode 12 at
-- the exception vector, `EPC` = the `add`), and `$10` keeps its old value.
#guard (let s' := stepIn (prog1Spec (.add 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0x7fffffff#32), (9, 1#32), (10, 0x55#32)])
        causeExcCode s' == excCodeOv && s'.pc == exceptionVectorAddr
            && s'.cp0Epc == textBase && readReg s' 10 == 0x55#32) = true

/-! ## `addu`, `subu`, `and`, `or`, `xor`, `nor`, `slt`, `sltu`

`addu`/`subu` are `add`/`sub` without the overflow trap: plain two's-complement wraparound,
never an exception (INSTRUCTION-REF "addu"/"subu"). `and`/`or`/`xor`/`nor` are bitwise
(INSTRUCTION-REF "and"/"or"/"xor"/"nor"). `slt`/`sltu` write a `0`/`1` comparison result, signed
vs. unsigned (INSTRUCTION-REF "slt"/"sltu"). `movn`/`movz` leave `$rd` untouched (not zeroed)
when the condition fails: `movn_not_taken_unchanged`/`movz_not_taken_unchanged` reject an
always-overwrite implementation. -/

/-- **`addu` computes `$rs + $rt` with plain wraparound and never traps** —
same formula as `add_spec_raw` minus the overflow check entirely
(INSTRUCTION-REF "addu" section). -/
theorem addu_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.addu rs rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let sumBV := readReg s (regIdxSpec rs) + readReg s (regIdxSpec rt)
      { (writeReg s (regIdxSpec rd) sumBV) with
          pc := (writeReg s (regIdxSpec rd) sumBV).pc + 4#32 }) := by
  step_spec

/-- **`subu` computes `$rs - $rt` with plain wraparound and never traps**
(INSTRUCTION-REF "subu" section). -/
theorem subu_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.subu rs rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let diffBV := readReg s (regIdxSpec rs) - readReg s (regIdxSpec rt)
      { (writeReg s (regIdxSpec rd) diffBV) with
          pc := (writeReg s (regIdxSpec rd) diffBV).pc + 4#32 }) := by
  step_spec

/-- **`and` computes the bitwise AND of `$rs`/`$rt`** — no overflow concept
at all (INSTRUCTION-REF "and" section). -/
theorem and_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.and rs rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let v := readReg s (regIdxSpec rs) &&& readReg s (regIdxSpec rt)
      { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 }) := by
  step_spec

/-- **`or` computes the bitwise OR of `$rs`/`$rt`** (INSTRUCTION-REF "or"
section). -/
theorem or_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.or rs rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let v := readReg s (regIdxSpec rs) ||| readReg s (regIdxSpec rt)
      { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 }) := by
  step_spec

/-- **`xor` computes the bitwise XOR of `$rs`/`$rt`** (INSTRUCTION-REF "xor"
section). -/
theorem xor_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.xor rs rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let v := readReg s (regIdxSpec rs) ^^^ readReg s (regIdxSpec rt)
      { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 }) := by
  step_spec

/-- **`nor` computes the bitwise NOR (`~($rs | $rt)`) of `$rs`/`$rt`**
(INSTRUCTION-REF "nor" section). -/
theorem nor_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.nor rs rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let v := ~~~(readReg s (regIdxSpec rs) ||| readReg s (regIdxSpec rt))
      { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 }) := by
  step_spec

/-- **`slt` writes `1` to `$rd` iff `$rs < $rt` as a signed comparison, else
`0`** (INSTRUCTION-REF "slt" section). -/
theorem slt_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.slt rs rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let v := if asSigned (readReg s (regIdxSpec rs)) < asSigned (readReg s (regIdxSpec rt))
               then 1#32 else 0#32
      { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 }) := by
  step_spec

/-- **`sltu` writes `1` to `$rd` iff `$rs < $rt` as an unsigned comparison,
else `0`** (INSTRUCTION-REF "sltu" section). -/
theorem sltu_spec_raw (s : State) (w rs rt rd : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sltu rs rt rd))
    (hpb : s.pendingBranch = none) (hexec : executesInstr s = true) :
    step s = timerTick (
      let v := if (readReg s (regIdxSpec rs)).toNat < (readReg s (regIdxSpec rt)).toNat
               then 1#32 else 0#32
      { (writeReg s (regIdxSpec rd) v) with pc := (writeReg s (regIdxSpec rd) v).pc + 4#32 }) := by
  step_spec

/-! ### Satisfiable examples (`addu` … `sltu`) -/

-- `addu_spec_raw`: `0xffffffff + 2` wraps to `1`, with no trap (unlike
-- `add`, which would trap on this operand pair's signed overflow reading).
#guard (let s := stepIn (prog1Spec (.addu 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 2#32)])
        readReg s 10 == 1#32) = true

-- `subu_spec_raw`: `0 - 1` wraps to `0xffffffff`, with no trap.
#guard (let s := stepIn (prog1Spec (.subu 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0#32), (9, 1#32)])
        readReg s 10 == 0xffffffff#32) = true

-- `and_spec_raw`/`or_spec_raw`/`xor_spec_raw`/`nor_spec_raw`.
#guard (let s := stepIn (prog1Spec (.and 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)])
        readReg s 10 == 0x0f000f00#32) = true

#guard (let s := stepIn (prog1Spec (.or 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)])
        readReg s 10 == 0xff0fff0f#32) = true

#guard (let s := stepIn (prog1Spec (.xor 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xff00ff00#32), (9, 0x0f0f0f0f#32)])
        readReg s 10 == 0xf00ff00f#32) = true

#guard (let s := stepIn (prog1Spec (.nor 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0#32), (9, 0#32)])
        readReg s 10 == 0xffffffff#32) = true

-- `slt_spec_raw`/`sltu_spec_raw`: the same bit pattern (`0xffffffff`, i.e.
-- `-1` signed) compares differently against `1` under signed vs. unsigned
-- interpretation.
#guard (let s := stepIn (prog1Spec (.slt 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)])
        readReg s 10 == 1#32) = true

#guard (let s := stepIn (prog1Spec (.sltu 8#32 9#32 10#32))
          (setRegsSpec (initialState textBase) [(8, 0xffffffff#32), (9, 1#32)])
        readReg s 10 == 0#32) = true
