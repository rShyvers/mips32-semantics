import Semantics.Refine.Bridge
import Std.Data.HashMap.Lemmas

/-!
# Refine.Fetch — address translation and memory against the model's MMU

The manual's `AddressTranslation` (Fixed Mapping MMU, Table 4.2 address check) against the model's
`translate`, and `LoadMemory` of an aligned word against `readMemWord`'s bytes. Instruction fetch
(`Manual.InstructionFetch`) against `readMemWord s s.pc`.
-/

namespace Refine

open Manual

theorem erl_abs (s : State) : StatusERL (abs s) = erlSet s := by
  rw [erlSet, show statusErlMask = BitVec.twoPow 32 2 by decide, and_twoPow_ne _ 2 (by omega)]; rfl

theorem userMode_abs (s : State) : UserMode (abs s) = !kernelMode s := by
  rw [← kernel_abs]; simp only [UserMode, KernelMode]; cases StatusUM (abs s) <;> simp

/-- The address check of the manual's translation is the model's `accessAllowed`. -/
theorem denied_eq (s : State) (va : W32) :
    (UserMode (abs s) && bit va 31) = !accessAllowed s va := by
  rw [userMode_abs, accessAllowed, isUseg, bit31_iff]
  cases kernelMode s <;> simp only [Bool.not_false, Bool.true_and, Bool.not_true, Bool.false_and,
    Bool.false_or, Bool.true_or]
  rw [Bool.eq_iff_iff]; simp

theorem kseg01 (va : W32) : (0#3 ++ va.extractLsb' 0 29 : W32) = va &&& 0x1FFFFFFF#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- The Fixed Mapping translation, the manual's segment table against the model's
`fixedMappingPA`. -/
theorem fixedMapping_eq (erl : Bool) (va : W32) : FixedMapping erl va = fixedMappingPA erl va := by
  have hk : (va.extractLsb' 29 3).toNat = va.toNat / 2^29 := by
    rw [BitVec.extractLsb'_toNat]; have := va.isLt; omega
  unfold FixedMapping fixedMappingPA
  generalize hb : va.extractLsb' 29 3 = b at hk
  rcases b with ⟨⟨n, hn⟩⟩
  simp only [BitVec.toNat_ofFin] at hk
  have hv := va.isLt
  rcases n with _|_|_|_|_|_|_|_|n
  all_goals first
    | omega
    | (simp only [show va.toNat < 0x80000000 by omega, ↓reduceIte]; rfl)
    | (simp only [show ¬ va.toNat < 0x80000000 by omega, show va.toNat < 0xC0000000 by omega,
        ↓reduceIte, ← kseg01]; rfl)
    | (simp only [show ¬ va.toNat < 0x80000000 by omega, show ¬ va.toNat < 0xC0000000 by omega,
        ↓reduceIte]; rfl)

/-- **`AddressTranslation` against `translate`**, run from any frame over `abs s`. -/
theorem addrTrans_run (s : State) (va : W32) (iord : IorD) (lors : LorS) (c : Ctx) (f : Frame)
    (hf : f.arch = abs s) :
    AddressTranslation va iord lors c f =
      match translate s va with
      | some pa => (.ok (pa, CCAOf (abs s) va), f)
      | none =>
        (.signal (match lors with | .LOAD => .AddressErrorLoad va | .STORE => .AddressErrorStore va), f) := by
  obtain ⟨a, p, d⟩ := f
  simp only at hf
  subst hf
  simp only [AddressTranslation, bind, Pseudo.get, memory_address]
  have hd := denied_eq s va
  simp only [translate]
  by_cases h : (UserMode (abs s) && bit va 31) = true
  · have ha : accessAllowed s va = false := by rw [hd] at h; simpa using h
    simp only [h, ha, Bool.false_eq_true, ↓reduceIte]
    cases lors <;> rfl
  · have ha : accessAllowed s va = true := by rw [hd] at h; simpa using h
    simp only [h, ha, ↓reduceIte, pure, erl_abs, fixedMapping_eq, Bool.false_eq_true]

theorem getLsbD_ofNat_byte (b : UInt8) (k : Nat) :
    (BitVec.ofNat 32 b.toNat).getLsbD k = (decide (k < 8) && b.toBitVec.getLsbD k) := by
  rw [BitVec.getLsbD_ofNat]
  by_cases hk : k < 8
  · simp only [hk, decide_true, Bool.true_and, show k < 32 by omega]; rfl
  · have : b.toNat < 2 ^ k :=
      Nat.lt_of_lt_of_le b.toBitVec.isLt (Nat.pow_le_pow_right (by omega) (by omega))
    simp [hk, Nat.testBit_lt_two_pow this]

/-- A byte at bit position `n` as the manual writes it (`toBitVec`, widened) and as the model does. -/
theorem byte_setWidth (b : UInt8) : b.toBitVec.setWidth 32 = BitVec.ofNat 32 b.toNat := by
  rw [show b.toNat = b.toBitVec.toNat from rfl, BitVec.ofNat_toNat]

/-- The manual's byte-lane position is the model's `byteShift` for a word, in the profile's byte
order (both read `BigEndianMem`, `profile.bigEndianMem`). -/
theorem laneShift_eq (k : Nat) (hk : k < 4) : laneShift k = byteShift profile.bigEndianMem 4 k := by
  simp [laneShift, byteShift, BigEndianMem, profile, Nat.mod_eq_of_lt hk]

/-- Four bytes as the manual's memory element and as the model's word (`join4`). -/
theorem word_of_bytes (b0 b1 b2 b3 : UInt8) :
    ((b0.toBitVec.setWidth 32 <<< laneShift 0) ||| (b1.toBitVec.setWidth 32 <<< laneShift 1) |||
      (b2.toBitVec.setWidth 32 <<< laneShift 2) ||| (b3.toBitVec.setWidth 32 <<< laneShift 3) : W32) =
      join4 profile.bigEndianMem b0 b1 b2 b3 := by
  simp only [join4, byteInValue, byte_setWidth, laneShift_eq 0 (by omega), laneShift_eq 1 (by omega),
    laneShift_eq 2 (by omega), laneShift_eq 3 (by omega)]

/-- An aligned physical address is its own aligned word base. -/
theorem base_of_aligned (pa : W32) (h : pa.toNat % 4 = 0) : pa &&& ~~~3#32 = pa := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_not]
  have hv := pa.isLt
  have : pa.toNat = 4 * (pa.toNat / 4) := by omega
  rw [this]
  generalize pa.toNat / 4 = q at *
  simp only [BitVec.toNat_ofNat]
  rw [Nat.and_comm, show 2 ^ 32 - 1 - 3 % 2 ^ 32 = 4 * (2 ^ 30 - 1) by rfl,
    show 4 * (2 ^ 30 - 1) = (2 ^ 30 - 1) <<< 2 by rfl, show 4 * q = q <<< 2 by
      rw [Nat.shiftLeft_eq]; omega, ← Nat.shiftLeft_and_distrib]
  rw [Nat.and_comm, Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)]

/-- The model's translation of an aligned address is aligned. -/
theorem fixedMappingPA_aligned (erl : Bool) (va : W32) (h : va.toNat % 4 = 0) :
    (fixedMappingPA erl va).toNat % 4 = 0 := by
  unfold fixedMappingPA
  split
  · split
    · exact h
    · rw [BitVec.toNat_add]; simp; omega
  · split
    · rw [BitVec.toNat_and, show (4:Nat) = 2 ^ 2 by rfl, Nat.and_mod_two_pow, show (2:Nat) ^ 2 = 4 by rfl, h]
      simp
    · exact h

/-- `LoadMemory` under the model's oracle (no load clears `LLbit`, `Oracle.loadClearsLL`): the
aligned memory element, state unchanged. -/
theorem loadMemory_model (cca : BitVec 3) (n : Nat) (pa : PAddr) (va : W32) (iord : IorD)
    (f : Frame) :
    LoadMemory cca n pa va iord modelCtx f = (.ok (MemElemAt f.arch.Mem pa), f) := by
  simp only [LoadMemory, bind, Pseudo.get, Pseudo.oracle, pure]
  cases iord <;> rfl

/-- **`LoadMemory` of a word against `readMemWord`**: the aligned memory element at the
translated address is the model's word (`join4`, in the profile's byte order). -/
theorem memElem_eq (s : State) (pa : PAddr) (h : pa.toNat % 4 = 0) :
    MemElemAt (memOf s.physMem) pa =
      join4 profile.bigEndianMem ((s.physMem.get? pa).getD 0) ((s.physMem.get? (pa + 1#32)).getD 0)
        ((s.physMem.get? (pa + 2#32)).getD 0) ((s.physMem.get? (pa + 3#32)).getD 0) := by
  rw [MemElemAt]; simp only [base_of_aligned pa h, memOf]; exact word_of_bytes _ _ _ _

/-- The manual's word-alignment test is the model's `% 4`. -/
theorem misaligned_eq (va : W32) : (bits va 1 0 != 0#2) = decide (va.toNat % 4 ≠ 0) := by
  have : (bits va 1 0).toNat = va.toNat % 4 := by
    simp only [bits, BitVec.extractLsb'_toNat]; omega
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · intro h h'; apply h; apply BitVec.eq_of_toNat_eq; rw [this, h']; rfl
  · intro h h'; apply h; rw [← this, h']; rfl

/-- **`readMemWord` of an aligned address** is the manual's memory element at the translated
address. -/
theorem readMemWord_eq (s : State) (va : W32) (h : va.toNat % 4 = 0) :
    readMemWord s va = (translate s va).map (MemElemAt (memOf s.physMem)) := by
  unfold readMemWord translate
  simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]
  cases accessAllowed s va
  · rfl
  · simp only [↓reduceIte, Option.map_some]
    rw [memElem_eq _ _ (fixedMappingPA_aligned _ _ h)]

/-- An insertion into the model's physical memory is the manual's byte update. -/
theorem memOf_insert (m : Std.HashMap PAddr UInt8) (p : PAddr) (b : UInt8) :
    memOf (m.insert p b) = updMem (memOf m) p b := by
  funext q; simp only [memOf, updMem, Std.HashMap.get?_insert]; split <;> rfl

/-- The manual's byte lane `k` of a memory element is the model's byte `k` of a word
(`byteOfValue`, in the profile's byte order). -/
theorem laneByte_eq (v : W32) (k : Nat) (hk : k < 4) :
    laneByte v k = byteOfValue profile.bigEndianMem 4 v k := by
  apply UInt8.toBitVec_inj.mp
  have e : (byteOfValue profile.bigEndianMem 4 v k).toBitVec =
      BitVec.ofNat 8 ((v >>> byteShift profile.bigEndianMem 4 k) &&& 0xff#32).toNat := rfl
  rw [e, BitVec.ofNat_toNat, ← laneShift_eq k hk]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [laneByte, laneShift, BigEndianMem, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  rcases k with _|_|_|_|k <;> rcases i with _|_|_|_|_|_|_|_|i <;> simp_all
  all_goals omega

end Refine
