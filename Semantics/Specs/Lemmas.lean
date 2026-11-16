import Semantics.FpOpsFacts
import Semantics.Specs.Defs

/-!
# Lemmas — helper lemmas used by the spec proofs

Nothing here is a headline statement: these are small facts about `if`, bit masks, `writeReg`,
`readCString`, `mkNext` and the `fpFinish*` helpers, used by the proofs in the family files.

## Theorems in this file (86)

  `ite_of_pos` `ite_of_neg` `mask_field_written` `mask_field_kept` `two_fields_first`
  `two_fields_second` `two_fields_kept` `bit_of_31` `bit_of_124` `excCode_field_roundtrip`
  `readCString_mem` `readCString_eq_ofMem` `writeReg_proj_pc` `writeReg_proj_hi` `writeReg_proj_lo`
  `writeReg_proj_fpRegs` `writeReg_proj_fcsr` `writeReg_proj_mem` `writeReg_proj_pendingBranch`
  `writeReg_proj_llBit` `writeReg_proj_cp0Status` `writeReg_proj_cp0Cause` `writeReg_proj_cp0Epc`
  `writeReg_proj_cp0BadVAddr` `writeReg_proj_cp0ErrorEpc` `writeReg_proj_llAddr`
  `writeReg_proj_cp0EBase` `writeReg_proj_cp0ConfigK0` `writeReg_proj_cp0ConfigK23`
  `writeReg_proj_cp0ConfigKU` `writeReg_proj_regs` `writeReg_pc` `writeReg_hi` `writeReg_lo`
  `writeReg_reads_back` `readReg_zero_of_regs_eq` `writeMemWord_regs` `writeMemHalf_regs`
  `writeMemByte_regs` `writeFpReg_reads_back` `mkNext_of_none` `execInstr_eq_body` `fpFinishS_eq`
  `fpFinishD_eq` `fpFinishCmp_eq` `readMemWord_misaligned` `writeMemWord_misaligned`
  `readMemWord_isSome_of_aligned` `writeMemWord_isSome_of_aligned` `translate_congr`
  `readMemByte_congr` `translate_of_allowed` `translate_of_not_allowed` `writeReg_proj_cp0Count`
  `writeReg_proj_cp0Compare` `writeReg_proj_cp0TimerInt` `writeReg_proj_cp0HWREna`
  `writeReg_proj_hwInt` `writeReg_proj_standby` `writeReg_proj_nullified` `timerTick_pc`
  `timerTick_regs` `timerTick_hi` `timerTick_lo` `timerTick_fpRegs` `timerTick_fcsr`
  `timerTick_physMem` `timerTick_pendingBranch` `timerTick_llBit` `timerTick_cp0Status`
  `timerTick_cp0Cause` `timerTick_cp0Epc` `timerTick_cp0BadVAddr` `timerTick_cp0ErrorEpc`
  `timerTick_llAddr` `timerTick_cp0EBase` `timerTick_cp0ConfigK0` `timerTick_cp0ConfigK23`
  `timerTick_cp0ConfigKU` `timerTick_cp0Compare` `timerTick_cp0HWREna` `timerTick_hwInt`
  `timerTick_standby` `timerTick_nullified` `step_of_executesInstr` `step_nullified`
  `cp0WriteAt_regs` `cp0WriteAt_fpRegs` `cp0WriteAt_hwInt` `cp0WriteAt_pc` `cp0WriteAt_pendingBranch` `cp0WriteAt_pb`
  `cp0ReadAt_pb` `writeReg_proj_cp0UserLocal` `writeReg_proj_cp0BadInstr` `writeReg_proj_cp0BadInstrP`
  `writeReg_proj_cp0KScratch` `writeReg_proj_cp0Config5SBRI`
-/

set_option maxRecDepth 4000

/-- `if c then t else e = t` when `c` holds. -/
theorem ite_of_pos {c : Prop} [Decidable c] {α : Sort _} {t e : α} (h : c) :
    (if c then t else e) = t := by simp [h]

/-- `if c then t else e = e` when `c` fails. -/
theorem ite_of_neg {c : Prop} [Decidable c] {α : Sort _} {t e : α} (h : ¬ c) :
    (if c then t else e) = e := by simp [h]

/-- Bit-mask fact: writing field `m` of `x` from `y` gives back `y`'s field. -/
theorem mask_field_written (x y m : W32) : ((x &&& ~~~m) ||| (y &&& m)) &&& m = y &&& m := by
  ext i hi; simp; grind

/-- Bit-mask fact: writing field `m` of `x` leaves any disjoint field `k`
of `x` alone. -/
theorem mask_field_kept (x y m k : W32) (h : k &&& m = 0#32) :
    ((x &&& ~~~m) ||| (y &&& m)) &&& k = x &&& k := by
  have hb : ∀ i (hi : i < 32), (k[i] && m[i]) = false := by
    intro i hi; have := congrArg (·[i]) h; simpa using this
  ext i hi; have := hb i hi; simp at this ⊢; grind

/-- Bit-mask fact for the two fields exception entry writes (`m` from `y`,
`c` from `z`, disjoint): reading `m` back gives `y`'s field. -/
theorem two_fields_first (x y z m c : W32) (h : m &&& c = 0#32) :
    (((x &&& ~~~(m ||| c)) ||| (y &&& m)) ||| (z &&& c)) &&& m = y &&& m := by
  have hb : ∀ i (hi : i < 32), (m[i] && c[i]) = false := by
    intro i hi; have := congrArg (·[i]) h; simpa using this
  ext i hi; have := hb i hi; simp at this ⊢; grind

/-- … reading `c` back gives `z`'s field. -/
theorem two_fields_second (x y z m c : W32) (h : m &&& c = 0#32) :
    (((x &&& ~~~(m ||| c)) ||| (y &&& m)) ||| (z &&& c)) &&& c = z &&& c := by
  have hb : ∀ i (hi : i < 32), (m[i] && c[i]) = false := by
    intro i hi; have := congrArg (·[i]) h; simpa using this
  ext i hi; have := hb i hi; simp at this ⊢; grind

/-- … and any field `k` disjoint from both is `x`'s. -/
theorem two_fields_kept (x y z m c k : W32) (hm : k &&& m = 0#32) (hc : k &&& c = 0#32) :
    (((x &&& ~~~(m ||| c)) ||| (y &&& m)) ||| (z &&& c)) &&& k = x &&& k := by
  have hb : ∀ i (hi : i < 32), (k[i] && m[i]) = false := by
    intro i hi; have := congrArg (·[i]) hm; simpa using this
  have hb' : ∀ i (hi : i < 32), (k[i] && c[i]) = false := by
    intro i hi; have := congrArg (·[i]) hc; simpa using this
  ext i hi; have := hb i hi; have := hb' i hi; simp at * ; grind

theorem bit_of_31 : ∀ i : Fin 32, (31#32).getLsbD i.val = decide (i.val < 5) := by decide

theorem bit_of_124 : ∀ i : Fin 32, (124#32).getLsbD (2 + i.val) = decide (i.val < 5) := by decide

/-- Placing a value in bits 6..2 and reading those bits back gives its low
five bits. -/
theorem excCode_field_roundtrip (c : W32) : ((c <<< 2) &&& 124#32) >>> 2 = c &&& 31#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h31 := bit_of_31 ⟨i, hi⟩
  have h124 := bit_of_124 ⟨i, hi⟩
  simp only at h31 h124
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, h31, h124]
  by_cases h5 : i < 5
  · have : 2 + i < 32 := by omega
    have h2 : ¬ (2 + i < 2) := by omega
    simp [h5, this, h2]
  · simp [h5]

/-- Translation depends on `Status` alone (the mode and `ERL`). -/
theorem translate_congr (s s' : State) (h : s.cp0Status = s'.cp0Status) (va : W32) :
    translate s va = translate s' va := by
  unfold translate accessAllowed kernelMode erlSet; rw [h]

/-- A byte read depends only on physical memory and `Status`. -/
theorem readMemByte_congr (s s' : State) (hm : s.physMem = s'.physMem)
    (h : s.cp0Status = s'.cp0Status) (va : W32) : readMemByte s va = readMemByte s' va := by
  unfold readMemByte; rw [translate_congr s s' h, hm]

/-- `readCString` only looks at memory, through the MMU (so also at `Status`). -/
theorem readCString_mem (s s' : State) (h : s.physMem = s'.physMem)
    (hst : s.cp0Status = s'.cp0Status) (a : W32) (f : Nat) :
    readCString s a f = readCString s' a f := by
  induction f generalizing a with
  | zero => rfl
  | succ n ih => unfold readCString; rw [readMemByte_congr s s' h hst, ih]

/-- `readCString` as a function of the physical memory and `Status` alone (proof device). -/
def readCStringOfMem (m : Std.HashMap W32 UInt8) (st : W32) (a : W32) (f : Nat) : String :=
  readCString { initialState 0#32 with physMem := m, cp0Status := st } a f

theorem readCString_eq_ofMem (pc : W32) (regs : Array W32) (fpRegs : Array W32)
    (fcsr : W32) (mem : Std.HashMap W32 UInt8) (pb : Option W32) (llBit : Bool)
    (st ca epc bva eepc lla eb a : W32) (k0 k23 ku : BitVec 3) (cnt cmp : W32) (ti : Bool)
    (hwre : W32) (hw : BitVec 6) (sb : Bool) (ul bi bip : W32) (ks : Fin 6 → W32) (sbri : Bool)
    (f : Nat) :
    readCString ⟨pc, regs, fpRegs, fcsr, mem, pb, llBit, st, ca, epc, bva, eepc, lla, eb, k0,
        k23, ku, cnt, cmp, ti, hwre, hw, sb, ul, bi, bip, ks, sbri⟩ a f
      = readCStringOfMem mem st a f :=
  readCString_mem ⟨pc, regs, fpRegs, fcsr, mem, pb, llBit, st, ca, epc, bva, eepc, lla, eb, k0,
      k23, ku, cnt, cmp, ti, hwre, hw, sb, ul, bi, bip, ks, sbri⟩
    { initialState 0#32 with physMem := mem, cp0Status := st } rfl rfl a f

theorem writeReg_proj_pc (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).pc = s.pc := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_fpRegs (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).fpRegs = s.fpRegs := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_fcsr (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).fcsr = s.fcsr := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_mem (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).physMem = s.physMem := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_pendingBranch (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).pendingBranch = s.pendingBranch := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_llBit (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).llBit = s.llBit := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0Status (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0Status = s.cp0Status := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0Cause (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0Cause = s.cp0Cause := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0Epc (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0Epc = s.cp0Epc := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0BadVAddr (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0BadVAddr = s.cp0BadVAddr := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0ErrorEpc (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0ErrorEpc = s.cp0ErrorEpc := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_llAddr (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).llAddr = s.llAddr := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0EBase (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0EBase = s.cp0EBase := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0ConfigK0 (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0ConfigK0 = s.cp0ConfigK0 := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0ConfigK23 (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0ConfigK23 = s.cp0ConfigK23 := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0ConfigKU (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0ConfigKU = s.cp0ConfigKU := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0Count (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0Count = s.cp0Count := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0Compare (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0Compare = s.cp0Compare := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0TimerInt (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0TimerInt = s.cp0TimerInt := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0HWREna (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).cp0HWREna = s.cp0HWREna := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_hwInt (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).hwInt = s.hwInt := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_standby (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).standby = s.standby := by
  unfold writeReg; split <;> rfl

-- BEGIN R6-2
theorem writeReg_proj_cp0UserLocal (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).cp0UserLocal = s.cp0UserLocal := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0BadInstr (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).cp0BadInstr = s.cp0BadInstr := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0BadInstrP (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).cp0BadInstrP = s.cp0BadInstrP := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0KScratch (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).cp0KScratch = s.cp0KScratch := by
  unfold writeReg; split <;> rfl

theorem writeReg_proj_cp0Config5SBRI (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).cp0Config5SBRI = s.cp0Config5SBRI := by
  unfold writeReg; split <;> rfl
-- END R6-2

/-! ### `timerTick` touches only `Count` and `Cause.TI`

Every other field of `timerTick s` is the field of `s` (by definition: `timerTick` is a record
update of `cp0Count` and `cp0TimerInt`). Tagged `simp` so that a proof about `step s` can see
through the timer to the instruction's own effect. -/

@[simp] theorem timerTick_pc (s : State) : (timerTick s).pc = s.pc := rfl
@[simp] theorem timerTick_regs (s : State) : (timerTick s).regs = s.regs := rfl
@[simp] theorem timerTick_fpRegs (s : State) : (timerTick s).fpRegs = s.fpRegs := rfl
@[simp] theorem timerTick_fcsr (s : State) : (timerTick s).fcsr = s.fcsr := rfl
@[simp] theorem timerTick_physMem (s : State) : (timerTick s).physMem = s.physMem := rfl
@[simp] theorem timerTick_pendingBranch (s : State) : (timerTick s).pendingBranch = s.pendingBranch := rfl
@[simp] theorem timerTick_llBit (s : State) : (timerTick s).llBit = s.llBit := rfl
@[simp] theorem timerTick_cp0Status (s : State) : (timerTick s).cp0Status = s.cp0Status := rfl
@[simp] theorem timerTick_cp0Cause (s : State) : (timerTick s).cp0Cause = s.cp0Cause := rfl
@[simp] theorem timerTick_cp0Epc (s : State) : (timerTick s).cp0Epc = s.cp0Epc := rfl
@[simp] theorem timerTick_cp0BadVAddr (s : State) : (timerTick s).cp0BadVAddr = s.cp0BadVAddr := rfl
@[simp] theorem timerTick_cp0ErrorEpc (s : State) : (timerTick s).cp0ErrorEpc = s.cp0ErrorEpc := rfl
@[simp] theorem timerTick_llAddr (s : State) : (timerTick s).llAddr = s.llAddr := rfl
@[simp] theorem timerTick_cp0EBase (s : State) : (timerTick s).cp0EBase = s.cp0EBase := rfl
@[simp] theorem timerTick_cp0ConfigK0 (s : State) : (timerTick s).cp0ConfigK0 = s.cp0ConfigK0 := rfl
@[simp] theorem timerTick_cp0ConfigK23 (s : State) : (timerTick s).cp0ConfigK23 = s.cp0ConfigK23 := rfl
@[simp] theorem timerTick_cp0ConfigKU (s : State) : (timerTick s).cp0ConfigKU = s.cp0ConfigKU := rfl
@[simp] theorem timerTick_cp0Compare (s : State) : (timerTick s).cp0Compare = s.cp0Compare := rfl
@[simp] theorem timerTick_cp0HWREna (s : State) : (timerTick s).cp0HWREna = s.cp0HWREna := rfl
@[simp] theorem timerTick_hwInt (s : State) : (timerTick s).hwInt = s.hwInt := rfl
@[simp] theorem timerTick_standby (s : State) : (timerTick s).standby = s.standby := rfl
/-- **When the step executes the instruction** (`executesInstr`: no interrupt is taken, the
processor is not in standby), `step` is the instruction followed by the timer. Every
per-instruction theorem about `step` goes through this. -/
theorem step_of_executesInstr (s : State) (h : executesInstr s = true) :
    step s = timerTick (execute s) := by
  unfold executesInstr at h
  have hi : interruptTaken s = false := by
    cases hh : interruptTaken s <;> simp_all
  have hs : s.standby = false := by
    cases hh : s.standby <;> simp_all
  unfold step stepCore
  rw [hi, hs]
  rfl

theorem writeReg_proj_regs (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).regs = if i == 0 then s.regs else s.regs.set! i.val v := by
  unfold writeReg; split <;> rfl

/-- A `writeReg` call never moves the program counter: it only ever touches
the register file. Used throughout to simplify the "next state" shape that
`step` produces after an instruction writes a register. -/
theorem writeReg_pc (s : State) (i : Fin 32) (v : W32) : (writeReg s i v).pc = s.pc := by
  unfold writeReg; split <;> rfl

/-- Writing `v` to a nonzero register `i` and immediately reading `i` back
gives exactly `v` (the one register `writeReg` actually changes). -/
theorem writeReg_reads_back (s : State) (i : Fin 32) (v : W32) (hne : i ≠ 0)
    (hsize : s.regs.size = 32) :
    readReg (writeReg s i v) i = v := by
  unfold writeReg readReg
  rw [ite_of_neg (by simpa using hne)]
  simp [Array.set!, Array.getD_eq_getD_getElem?, hsize, i.isLt]

/-- Two states with the same `regs` field read `$zero` the same —
the register-file-only half of `readReg`: any state change that leaves
`regs` alone (`pc`/`pendingBranch`/`hi`/`lo`/`physMem`/…) cannot disturb
`$zero`. -/
theorem readReg_zero_of_regs_eq {s1 s2 : State} (h : s1.regs = s2.regs) :
    readReg s1 0 = readReg s2 0 := by
  unfold readReg
  rw [h]

/-- `writeMemWord` never changes `regs` when it succeeds — it only ever
touches `physMem` (INSTRUCTION-REF "sw"/"sc" sections' effective-address write).
-/
theorem writeMemWord_regs (s stored : State) (addr v : W32)
    (h : writeMemWord s addr v = some stored) : stored.regs = s.regs := by
  unfold writeMemWord at h
  split at h
  · cases h
  · split at h
    · cases h
    · injection h with h'
      rw [← h']

/-- `writeMemHalf` never changes `regs` when it succeeds — the halfword
counterpart of `writeMemWord_regs` (INSTRUCTION-REF "sh" section). -/
theorem writeMemHalf_regs (s stored : State) (addr v : W32)
    (h : writeMemHalf s addr v = some stored) : stored.regs = s.regs := by
  unfold writeMemHalf at h
  split at h
  · cases h
  · split at h
    · cases h
    · injection h with h'
      rw [← h']

/-- `writeMemByte` never changes `regs` — the byte-write counterpart of
`writeMemWord_regs`/`writeMemHalf_regs`, completing the trio. It has no
alignment check; it fails only on the MMU's address-error check. -/
theorem writeMemByte_regs (s stored : State) (addr : W32) (v : UInt8)
    (h : writeMemByte s addr v = some stored) : stored.regs = s.regs := by
  unfold writeMemByte at h
  split at h
  · cases h
  · injection h with h'
    rw [← h']

/-- Writing `v` to FP register `i` and immediately reading `i` back gives
exactly `v` (`writeFpReg` has no hardwired-zero slot, unlike `writeReg`). -/
theorem writeFpReg_reads_back (s : State) (i : Fin 32) (v : W32)
    (hsize : s.fpRegs.size = 32) : readFpReg (writeFpReg s i v) i = v := by
  unfold writeFpReg readFpReg
  simp [Array.set!, Array.getD_eq_getD_getElem?, hsize, i.isLt]

/-- Outside a delay slot, completing normally means `pc ← pc + 4`. -/
theorem mkNext_of_none (s x : State) (h : s.pendingBranch = none) :
    mkNext s x = { x with pc := x.pc + 4#32 } := by
  unfold mkNext advance; rw [h]

/-- `execInstr` is `execBody` once its three guards are passed: the instruction
is not a control transfer in a delay slot, it does not need an unusable
coprocessor 1, and it does not need an unusable coprocessor 0. -/
theorem execInstr_eq_body (s : State) (instr : Instruction)
    (hnb : isBranchLike instr = false ∨ s.pendingBranch = none)
    (hcu : usesCop1 instr = false ∨ cu1Enabled s = true)
    (hcp0 : usesCop0 instr = false ∨ cp0Usable s = true) :
    execInstr s instr = execBody s instr := by
  have h1 : (isBranchLike instr && s.pendingBranch.isSome) = false := by
    rcases hnb with h | h <;> simp [h]
  have h2 : (usesCop1 instr && !cu1Enabled s) = false := by
    rcases hcu with h | h <;> simp [h]
  have h3 : (usesCop0 instr && !cp0Usable s) = false := by
    rcases hcp0 with h | h <;> simp [h]
  unfold execInstr
  rw [h1, h2, h3]
  rfl

theorem fpFinishS_eq (s : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags)
    (hpb : s.pendingBranch = none) : fpFinishS s fd r = fpCompletesS s fd r := by
  unfold fpFinishS fpCompletesS
  dsimp only
  rw [Mips.Fp.fpUpdate_snd]
  by_cases h : Mips.Fp.fpeEnabled s.fcsr r.2 = true
  · rw [ite_of_pos h, ite_of_pos h, Mips.Fp.fpUpdate_fst_of_enabled _ _ h]; rfl
  · have h' : Mips.Fp.fpeEnabled s.fcsr r.2 = false := by simpa using h
    rw [ite_of_neg h, ite_of_neg h, Mips.Fp.fpUpdate_fst_of_not_enabled _ _ h',
      mkNext_of_none _ _ hpb]
    rfl

theorem fpFinishD_eq (s : State) (fd : W32) (r : BitVec 64 × Mips.Fp.Flags)
    (hpb : s.pendingBranch = none) : fpFinishD s fd r = fpCompletesD s fd r := by
  unfold fpFinishD fpCompletesD
  dsimp only
  rw [Mips.Fp.fpUpdate_snd]
  by_cases h : Mips.Fp.fpeEnabled s.fcsr r.2 = true
  · rw [ite_of_pos h, ite_of_pos h, Mips.Fp.fpUpdate_fst_of_enabled _ _ h]; rfl
  · have h' : Mips.Fp.fpeEnabled s.fcsr r.2 = false := by simpa using h
    rw [ite_of_neg h, ite_of_neg h, Mips.Fp.fpUpdate_fst_of_not_enabled _ _ h',
      mkNext_of_none _ _ hpb]
    rfl

/-- `readMemWord` fails exactly on a non-word-aligned address (`State.lean`): the `none` arm of
every word load is the misaligned case. -/
theorem readMemWord_misaligned (s : State) (a : W32) (h : a.toNat % 4 ≠ 0) :
    readMemWord s a = none := by
  unfold readMemWord
  rw [ite_of_pos h]

/-- `writeMemWord` fails exactly on a non-word-aligned address (`State.lean`). -/
theorem writeMemWord_misaligned (s : State) (a v : W32) (h : a.toNat % 4 ≠ 0) :
    writeMemWord s a v = none := by
  unfold writeMemWord
  rw [ite_of_pos h]

/-- An accessible address translates by the fixed mapping (`State.lean`, `translate`). -/
theorem translate_of_allowed (s : State) (a : W32) (h : accessAllowed s a = true) :
    translate s a = some (fixedMappingPA (erlSet s) a) := by
  unfold translate; rw [ite_of_pos h]

/-- An inaccessible address (a kernel address from User Mode) does not translate. -/
theorem translate_of_not_allowed (s : State) (a : W32) (h : accessAllowed s a = false) :
    translate s a = none := by
  unfold translate; rw [ite_of_neg (by simp [h])]

/-- Conversely, an aligned `readMemWord` of an accessible address always succeeds. -/
theorem readMemWord_isSome_of_aligned (s : State) (a : W32) (h : a.toNat % 4 = 0)
    (hacc : accessAllowed s a = true) :
    (readMemWord s a).isSome = true := by
  unfold readMemWord
  rw [ite_of_neg (by omega), translate_of_allowed s a hacc]
  rfl

/-- Conversely, an aligned `writeMemWord` of an accessible address always succeeds. -/
theorem writeMemWord_isSome_of_aligned (s : State) (a v : W32) (h : a.toNat % 4 = 0)
    (hacc : accessAllowed s a = true) :
    (writeMemWord s a v).isSome = true := by
  unfold writeMemWord
  rw [ite_of_neg (by omega), translate_of_allowed s a hacc]
  rfl

-- BEGIN R6-2
/-! ## `cp0WriteAt` (the `mtc0` effect) touches only coprocessor 0 state -/

/-- `mtc0` (`cp0WriteAt`) never changes the GPRs. -/
theorem cp0WriteAt_regs (s : State) (rd sel v : W32) : (cp0WriteAt s rd sel v).regs = s.regs := by
  unfold cp0WriteAt; split
  · rename_i r _; cases r <;> rfl
  · rfl

/-- `mtc0` (`cp0WriteAt`) never changes the FPRs. -/
theorem cp0WriteAt_fpRegs (s : State) (rd sel v : W32) :
    (cp0WriteAt s rd sel v).fpRegs = s.fpRegs := by
  unfold cp0WriteAt; split
  · rename_i r _; cases r <;> rfl
  · rfl

/-- `mtc0` (`cp0WriteAt`) never changes the hardware interrupt lines. -/
theorem cp0WriteAt_hwInt (s : State) (rd sel v : W32) : (cp0WriteAt s rd sel v).hwInt = s.hwInt := by
  unfold cp0WriteAt; split
  · rename_i r _; cases r <;> rfl
  · rfl

/-- `mtc0` (`cp0WriteAt`) never changes `pc`. -/
theorem cp0WriteAt_pc (s : State) (rd sel v : W32) : (cp0WriteAt s rd sel v).pc = s.pc := by
  unfold cp0WriteAt; split
  · rename_i r _; cases r <;> rfl
  · rfl

/-- `mtc0` (`cp0WriteAt`) never changes the pending branch. -/
theorem cp0WriteAt_pendingBranch (s : State) (rd sel v : W32) :
    (cp0WriteAt s rd sel v).pendingBranch = s.pendingBranch := by
  unfold cp0WriteAt; split
  · rename_i r _; cases r <;> rfl
  · rfl

/-- `mtc0` (`cp0WriteAt`) commutes with setting the pending branch. -/
theorem cp0WriteAt_pb (s : State) (x : Option W32) (rd sel v : W32) :
    cp0WriteAt { s with pendingBranch := x } rd sel v =
      { cp0WriteAt s rd sel v with pendingBranch := x } := by
  unfold cp0WriteAt; split
  · rename_i r _; cases r <;> rfl
  · rfl

/-- `mfc0` (`cp0ReadAt`) does not look at the pending branch. -/
theorem cp0ReadAt_pb (s : State) (x : Option W32) (rd sel : W32) :
    cp0ReadAt { s with pendingBranch := x } rd sel = cp0ReadAt s rd sel := by
  unfold cp0ReadAt; split
  · rename_i r _; cases r <;> rfl
  · rfl
-- END R6-2
