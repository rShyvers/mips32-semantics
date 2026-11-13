import Std.Data.HashMap.Lemmas
import Semantics.Specs.Memory
import Semantics.Specs.Fetch

/-!
# SelfModifying — instruction fetch sees stores

`step` fetches from `State.physMem`, the same memory loads and stores use, so writing the instruction
stream is visible to the next fetch. The manual defines this (it is what SYNCI exists for:
"This instruction is used after a new instruction stream is written to make the new instructions
effective relative to an instruction fetch", MD00086 Vol II-A Rev 6.06, SYNCI, p.412); the model
has no caches, so no SYNCI is needed for the store to take effect (`synci` is a no-op, `Step.lean`).

## Theorems in this file (7)

  `getLsbD_255` `word_of_bytes` `byte_toUInt8_toNat` `readMemWord_writeMemWord_alias`
  `readMemWord_writeMemWord_same`
  `sw_next_instruction_is_fetched` `store_changes_next_instruction`
-/

set_option maxRecDepth 4000

theorem getLsbD_255 (k : Nat) : (255#32).getLsbD k = decide (k < 8) := by
  by_cases hk : k < 32
  · exact (by decide : ∀ k : Fin 32, (255#32).getLsbD k.val = decide (k.val < 8)) ⟨k, hk⟩
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp; omega

/-- A word is the OR of its four bytes shifted back into place (proof device). -/
theorem word_of_bytes (v : W32) :
    ((v >>> 24 &&& 0xff#32) <<< 24 ||| (v >>> 16 &&& 0xff#32) <<< 16 |||
      (v >>> 8 &&& 0xff#32) <<< 8 ||| (v &&& 0xff#32)) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, getLsbD_255]
  by_cases h1 : i < 8
  · simp [h1, show i < 16 by omega, show i < 24 by omega]
  · by_cases h2 : i < 16
    · rw [show 8 + (i - 8) = i by omega]
      simp [h1, h2, show i < 24 by omega, show i - 8 < 8 by omega, hi]
    · by_cases h3 : i < 24
      · rw [show 16 + (i - 16) = i by omega]
        simp [h1, h2, h3, show i - 16 < 8 by omega, show ¬ (i - 8 < 8) by omega, hi]
      · rw [show 24 + (i - 24) = i by omega]
        simp [h1, h2, h3, show i - 24 < 8 by omega, show ¬ (i - 8 < 8) by omega,
          show ¬ (i - 16 < 8) by omega, hi]

/-- A byte stored as `UInt8` and read back as a word is the same byte (proof device). -/
theorem byte_toUInt8_toNat (x : W32) :
    (BitVec.ofNat 32 ((x &&& 0xff#32).toNat.toUInt8.toNat) : W32) = x &&& 0xff#32 := by
  have hlt : (x &&& 0xff#32).toNat < 256 := by
    rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have h : (x &&& 0xff#32).toNat.toUInt8.toNat = (x &&& 0xff#32).toNat := by
    simp only [Nat.toUInt8]
    exact Nat.mod_eq_of_lt hlt
  rw [h]
  exact BitVec.ofNat_toNat _ _ |>.trans (by simp)

/-- **A word written through one virtual address is read through any other virtual address that
translates to the same physical address** (the store changes `physMem` only, so the translation
of the second address is unchanged). -/
theorem readMemWord_writeMemWord_alias (s s' : State) (a b v : W32)
    (h : writeMemWord s a v = some s') (hb : b.toNat % 4 = 0)
    (htr : translate s b = translate s a) : readMemWord s' b = some v := by
  unfold writeMemWord at h
  split at h
  · cases h
  · rename_i hal
    cases hta : translate s a with
    | none => rw [hta] at h; cases h
    | some pa =>
      rw [hta] at h
      injection h with h
      have hst : s'.cp0Status = s.cp0Status := by rw [← h]
      unfold readMemWord
      rw [ite_of_neg (by omega), translate_congr s' s hst b, htr, hta, ← h]
      have d1 : (pa + 1#32 == pa) = false := by simp
      have d2 : (pa + 2#32 == pa) = false := by simp
      have d3 : (pa + 3#32 == pa) = false := by simp
      have d21 : (pa + 2#32 == pa + 1#32) = false := by simp
      have d31 : (pa + 3#32 == pa + 1#32) = false := by simp
      have d32 : (pa + 3#32 == pa + 2#32) = false := by simp
      simp only [Std.HashMap.get?_insert, d1, d2, d3, d21, d31, d32, beq_self_eq_true, ↓reduceIte,
        Bool.false_eq_true, Option.getD_some, byte_toUInt8_toNat]
      rw [word_of_bytes]

/-- **A word read returns the word just written there** (big-endian, both ways). -/
theorem readMemWord_writeMemWord_same (s s' : State) (a v : W32)
    (h : writeMemWord s a v = some s') : readMemWord s' a = some v := by
  have hal : a.toNat % 4 = 0 := by
    refine Classical.byContradiction fun hn => ?_
    rw [writeMemWord_misaligned s a v hn] at h; cases h
  exact readMemWord_writeMemWord_alias s s' a a v h hal rfl

/-- **Self-modifying code: a store to the next instruction is what the next fetch returns.** If
the instruction at `pc` (not in a delay slot) is `sw $rt, imm($rs)` and its effective address is
`pc + 4`, the address of the next instruction, then after the step `pc = pc + 4` and the fetch
there returns the stored value `$rt`, whatever memory held before. -/
theorem sw_next_instruction_is_fetched (s : State) (w rs rt imm : W32)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none)
    (haddr : readReg s (regIdxSpec rs) + signExt16 imm = s.pc + 4#32)
    (hacc : accessAllowed s (s.pc + 4#32) = true) :
    (step s).pc = s.pc + 4#32 ∧
      readMemWord (step s) (step s).pc = some (readReg s (regIdxSpec rt)) := by
  have hal : s.pc.toNat % 4 = 0 := by
    refine Classical.byContradiction fun h => ?_
    rw [readMemWord_misaligned s s.pc h] at hfetch; cases hfetch
  have hal4 : (s.pc + 4#32).toNat % 4 = 0 := by
    rw [BitVec.toNat_add]; simp; omega
  rw [sw_spec_raw s w rs rt imm hfetch hdecode hpb]
  dsimp only
  rw [haddr]
  obtain ⟨s', hs'⟩ : ∃ s', writeMemWord s (s.pc + 4#32) (readReg s (regIdxSpec rt)) = some s' :=
    Option.isSome_iff_exists.mp (writeMemWord_isSome_of_aligned s _ _ hal4 hacc)
  rw [hs']
  have hpc : s'.pc = s.pc := by
    unfold writeMemWord at hs'; rw [ite_of_neg (by omega), translate_of_allowed s _ hacc] at hs'
    injection hs' with h; rw [← h]
  refine ⟨by simp [hpc], ?_⟩
  show readMemWord s' (s'.pc + 4#32) = _
  rw [hpc]
  exact readMemWord_writeMemWord_same s s' _ _ hs'

/-- **A store to the address of the next instruction changes what is executed.** Under the
hypotheses of `sw_next_instruction_is_fetched`, if the stored value `$rt` decodes to `instr'`,
the next step executes `instr'` — not the instruction that was in memory at `pc + 4` before. -/
theorem store_changes_next_instruction (s : State) (w rs rt imm : W32) (instr' : Instruction)
    (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.sw rs rt imm))
    (hpb : s.pendingBranch = none)
    (haddr : readReg s (regIdxSpec rs) + signExt16 imm = s.pc + 4#32)
    (hacc : accessAllowed s (s.pc + 4#32) = true)
    (hnew : decode (readReg s (regIdxSpec rt)) = some instr') :
    step (step s) = execInstr (step s) instr' :=
  step_fetches_from_memory (step s) _ instr'
    (sw_next_instruction_is_fetched s w rs rt imm hfetch hdecode hpb haddr hacc).2 hnew

/-! ### Satisfiable example

`sw $t1, 4($t0)` with `$t0 = textBase` overwrites the `nop` that follows it with
`addiu $t2, $zero, 7`; the next step executes the stored `addiu`. -/
#guard
  let prog := buildProgSpec textBase [.sw 8#32 9#32 4#32, .sll 0#32 0#32 0#32]
  let s0 := setRegsSpec (initialState textBase)
    [(8, textBase), (9, encode (.addiu 0#32 10#32 7#32))]
  let s2 := step (stepIn prog s0)
  readReg s2 10 == 7#32 && s2.pc == textBase + 8#32
