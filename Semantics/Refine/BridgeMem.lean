import Semantics.Refine.Fetch
import Semantics.Refine.BridgeIntAlu
import Semantics.Refine.BridgeControl

/-!
# Refine.BridgeMem — shared lemmas of the memory, atomic, trap and system-call refinements (7C S2)

The model's `execInstr` of an instruction that is no CTI and uses no coprocessor is its `execBody`;
the manual's completion of an Operation that wrote at most one GPR is the model's `mkNext`; the
encodings of the trap and `SYSCALL`/`BREAK` pages lie outside the coprocessor spaces; the common end
of a conditional trap.
-/

namespace Refine

open Manual

theorem writeReg_pb (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).pendingBranch = s.pendingBranch := by
  unfold writeReg; split <;> rfl

/-- The completion of an Operation that changed nothing. -/
theorem complete_nop (s : State) : Complete (abs s) { arch := abs s } = abs (mkNext s s) := by
  rw [complete_plain, mkNext, abs_advance _ _ rfl]; rfl

/-- The completion of an Operation that wrote one GPR (`complete_writeReg` of `Refine/BridgeControl.lean`
without the `some`). -/
theorem complete_writeReg_eq (s : State) (hsz : s.regs.size = 32) (i : Fin 32) (v : W32) :
    Complete (abs s) { arch := writeGPR (abs s) i v } = abs (mkNext s (writeReg s i v)) := by
  rw [complete_plain, mkNext, abs_advance _ _ (writeReg_pb s i v), abs_writeReg _ _ _ hsz,
    writeReg_pc]; rfl

/-! ## Encodings -/

theorem opcode_trapFormat (rs rt code fn : W32) : opcode (trapFormat rs rt code fn) = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [opcode, trapFormat, fld, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem funct_trapFormat (rs rt code fn : W32) :
    trapFormat rs rt code fn &&& 0x3F#32 = fn &&& 0x3F#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [trapFormat, fld, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem opcode_codeFormat (code fn : W32) : opcode (codeFormat code fn) = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [opcode, codeFormat, fld, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem funct_codeFormat (code fn : W32) : codeFormat code fn &&& 0x3F#32 = fn &&& 0x3F#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [codeFormat, fld, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-! ## Exceptions -/

/-- The common end of a conditional trap: the manual's `if c then SignalException(Trap)` against the
model's `if P then takeException s excCodeTr else mkNext s s`. -/
theorem trap_finish (s : State) (c : Bool) (P : Prop) [Decidable P] (h : c = decide P) :
    (match (if c then (SignalException .Trap : Pseudo Unit) else pure ()) modelCtx { arch := abs s } with
     | (.ok (), f) => some (Complete (abs s) f)
     | (.signal e, f) => some (GeneralExceptionProcessing modelCtx.impl modelCtx.oracle e f.arch))
    = some (abs (if P then takeException s excCodeTr else mkNext s s)) := by
  subst h
  by_cases hP : P
  · simp only [hP, decide_true, ↓reduceIte, SignalException]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl,
      gep_take s .Trap rfl excCodeTr (by decide)]
  · simp only [hP, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact congrArg some (complete_nop s)

/-! ## Address Error -/

theorem gep_adel (s : State) (va : W32) :
    GeneralExceptionProcessing modelImpl modelOracle (.AddressErrorLoad va) (abs s) =
      abs (takeAddressException s excCodeAdEL va) := by
  rw [gep_eq s _ (by intro h; cases h) (by intro u h; cases h)]; rfl

theorem gep_ades (s : State) (va : W32) :
    GeneralExceptionProcessing modelImpl modelOracle (.AddressErrorStore va) (abs s) =
      abs (takeAddressException s excCodeAdES va) := by
  rw [gep_eq s _ (by intro h; cases h) (by intro u h; cases h)]; rfl

/-! ## Addresses within a word -/

/-- A virtual address `va + k` inside the aligned word of `va` translates to `pa + k`. -/
theorem translate_add (s : State) (va : W32) (k : Nat) (hk : va.toNat % 4 + k < 4) :
    translate s (va + BitVec.ofNat 32 k) = (translate s va).map (· + BitVec.ofNat 32 k) := by
  have hv := va.isLt
  have hsum : (va + BitVec.ofNat 32 k).toNat = va.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hacc : accessAllowed s (va + BitVec.ofNat 32 k) = accessAllowed s va := by
    simp only [accessAllowed, isUseg, hsum]
    have : (va.toNat + k < 0x80000000) = (va.toNat < 0x80000000) := by
      apply propext; omega
    simp only [this]
  unfold translate
  rw [hacc]
  cases accessAllowed s va
  · rfl
  · simp only [↓reduceIte, Option.map_some, Option.some.injEq]
    unfold fixedMappingPA
    rw [hsum]
    by_cases h1 : va.toNat < 0x80000000
    · have h1' : va.toNat + k < 0x80000000 := by omega
      simp only [h1, h1', ↓reduceIte]
      split
      · rfl
      · rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 32 k), ← BitVec.add_assoc]
    · by_cases h2 : va.toNat < 0xC0000000
      · have h1' : ¬ va.toNat + k < 0x80000000 := by omega
        have h2' : va.toNat + k < 0xC0000000 := by omega
        simp only [h1, h2, h1', h2', ↓reduceIte]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_and, hsum, BitVec.toNat_ofNat]
        simp only [show (536870911 : Nat) % 2 ^ 32 = 2 ^ 29 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]
        omega
      · have h1' : ¬ va.toNat + k < 0x80000000 := by omega
        have h2' : ¬ va.toNat + k < 0xC0000000 := by omega
        simp only [h1, h2, h1', h2', ↓reduceIte]

/-- The Fixed Mapping keeps the byte offset within the word. -/
theorem fixedMappingPA_low (erl : Bool) (va : W32) :
    (fixedMappingPA erl va).toNat % 4 = va.toNat % 4 := by
  unfold fixedMappingPA
  split
  · split
    · rfl
    · rw [BitVec.toNat_add]; simp; omega
  · split
    · rw [BitVec.toNat_and, show (4:Nat) = 2 ^ 2 by rfl, Nat.and_mod_two_pow,
        show (2:Nat) ^ 2 = 4 by rfl, show (0x1FFFFFFF#32).toNat % 4 = 3 by rfl]
      have : va.toNat % 4 < 4 := Nat.mod_lt _ (by omega)
      rw [show (3:Nat) = 2 ^ 2 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
    · rfl

/-- An address is its aligned word base plus its offset. -/
theorem base_add_off (P : W32) : P = (P &&& ~~~3#32) + BitVec.ofNat 32 (P.toNat % 4) := by
  have hor : (P &&& ~~~3#32) ||| (P &&& 3#32) = P := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not]
    cases P.getLsbD i <;> cases (3#32).getLsbD i <;> simp [hi]
  have hand : (P &&& ~~~3#32) &&& (P &&& 3#32) = 0#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    cases P.getLsbD i <;> cases (3#32).getLsbD i <;> simp
  have hlow : P &&& 3#32 = BitVec.ofNat 32 (P.toNat % 4) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (3#32).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_ofNat]
    omega
  rw [← hlow, BitVec.add_eq_or_of_and_eq_zero _ _ hand, hor]

theorem addr_recombine (P : W32) :
    (P &&& ~~~3#32) ||| ((P &&& 3#32) ^^^ (BitVec.fill 2 false).setWidth 32) = P := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
    BitVec.getLsbD_setWidth, BitVec.fill_false, BitVec.getLsbD_zero]
  cases P.getLsbD i <;> cases (3#32).getLsbD i <;> simp [hi]

theorem readMemByte_eq (s : State) (va : W32) :
    readMemByte s va = (translate s va).map (memOf s.physMem) := by
  unfold readMemByte; cases translate s va <;> rfl

/-! ## Byte lanes of loads and stores -/

theorem byte_idx (va : W32) : (bits va 1 0 ^^^ BitVec.fill 2 true).toNat = 3 - va.toNat % 4 := by
  have hlow : (bits va 1 0).toNat = va.toNat % 4 := by
    simp only [bits, BitVec.extractLsb'_toNat]; omega
  rw [← hlow]
  generalize bits va 1 0 = x
  obtain ⟨n, rfl, hn⟩ : ∃ n, x = BitVec.ofNat 2 n ∧ n < 4 := ⟨x.toNat, by simp, x.isLt⟩
  rcases n with _|_|_|_|n
  all_goals first | decide | omega | (simp at h2)

theorem half_idx (va : W32) (h : va.toNat % 2 = 0) :
    (bits va 1 0 ^^^ (BitVec.ofBool true ++ 0#1)).toNat = 2 - va.toNat % 4 := by
  have hlow : (bits va 1 0).toNat = va.toNat % 4 := by
    simp only [bits, BitVec.extractLsb'_toNat]; omega
  have h2 : va.toNat % 4 = 0 ∨ va.toNat % 4 = 2 := by omega
  rw [← hlow] at h2 ⊢
  generalize bits va 1 0 = x at h2 ⊢
  obtain ⟨n, rfl, hn⟩ : ∃ n, x = BitVec.ofNat 2 n ∧ n < 4 := ⟨x.toNat, by simp, x.isLt⟩
  rcases n with _|_|_|_|n
  all_goals first | decide | omega | (simp at h2)

theorem misaligned2_eq (va : W32) : bit va 0 = decide (va.toNat % 2 ≠ 0) := by
  simp only [bit, BitVec.getLsbD, Nat.testBit_zero]
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega

theorem memElem_byte (M : PAddr → UInt8) (P : W32) :
    (MemElemAt M P).extractLsb' (8 * (3 - P.toNat % 4)) 8 = (M P).toBitVec := by
  unfold MemElemAt
  have hP := base_add_off P
  generalize P &&& ~~~3#32 = B at hP ⊢
  rcases (show P.toNat % 4 = 0 ∨ P.toNat % 4 = 1 ∨ P.toNat % 4 = 2 ∨ P.toNat % 4 = 3 by omega)
    with h | h | h | h <;> rw [h] at hP ⊢ <;> rw [hP] <;> (try simp only [BitVec.add_zero]) <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    rcases i with _|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem memElem_half (M : PAddr → UInt8) (P : W32) (h2 : P.toNat % 2 = 0) :
    (MemElemAt M P).extractLsb' (8 * (2 - P.toNat % 4)) 16 = (M P).toBitVec ++ (M (P + 1#32)).toBitVec := by
  unfold MemElemAt
  have hP := base_add_off P
  generalize P &&& ~~~3#32 = B at hP ⊢
  rcases (show P.toNat % 4 = 0 ∨ P.toNat % 4 = 2 by omega)
    with h | h <;> rw [h] at hP ⊢ <;> rw [hP] <;>
    simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem addr_recombine_half (P : W32) :
    (P &&& ~~~3#32) ||| ((P &&& 3#32) ^^^ (BitVec.ofBool false ++ 0#1).setWidth 32) = P := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_ofBool, BitVec.getLsbD_zero]
  rcases i with _|_|i <;> cases P.getLsbD _ <;> simp [hi]

theorem toBitVec_eq_ofNat (b : UInt8) : b.toBitVec = BitVec.ofNat 8 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt b.toBitVec.isLt).symm

theorem signExtByte_eq (b : UInt8) : signExtByte b = sign_extend b.toBitVec := by
  rw [signExtByte, sign_extend, toBitVec_eq_ofNat]

theorem zeroExtByte_eq (b : UInt8) : zeroExtByte b = zero_extend b.toBitVec := by
  rw [zeroExtByte, zero_extend, toBitVec_eq_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have : b.toNat < 2 ^ 8 := b.toBitVec.isLt
  omega

theorem half_bits (hi lo : UInt8) :
    (BitVec.ofNat 32 hi.toNat <<< 8) ||| BitVec.ofNat 32 lo.toNat = zero_extend (hi.toBitVec ++ lo.toBitVec) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [zero_extend, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, getLsbD_ofNat_byte,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem signExt16_half (hi lo : UInt8) :
    signExt16 ((BitVec.ofNat 32 hi.toNat <<< 8) ||| BitVec.ofNat 32 lo.toNat) =
      sign_extend (hi.toBitVec ++ lo.toBitVec) := by
  rw [half_bits]
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [signExt16, zero_extend, sign_extend, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb,
    BitVec.getLsbD_setWidth, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_append]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem and3_toNat (P : W32) : (P &&& 3#32).toNat = P.toNat % 4 := by
  rw [BitVec.toNat_and, show (3#32).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem store_byte_fold (M : PAddr → UInt8) (P v : W32) :
    (storedLanes (P &&& 3#32).toNat BYTE).foldl
        (fun mm l => updMem mm ((P &&& ~~~3#32) + BitVec.ofNat 32 l) (laneByte v l)) M =
      updMem M P (laneByte v (P.toNat % 4)) := by
  rw [and3_toNat]
  have hP := base_add_off P
  generalize P &&& ~~~3#32 = B at hP ⊢
  rcases (show P.toNat % 4 = 0 ∨ P.toNat % 4 = 1 ∨ P.toNat % 4 = 2 ∨ P.toNat % 4 = 3 by omega)
    with h | h | h | h <;> rw [h] at hP ⊢ <;> rw [hP] <;> rfl

theorem store_half_fold (M : PAddr → UInt8) (P v : W32) (h2 : P.toNat % 2 = 0) :
    (storedLanes (P &&& 3#32).toNat HALFWORD).foldl
        (fun mm l => updMem mm ((P &&& ~~~3#32) + BitVec.ofNat 32 l) (laneByte v l)) M =
      updMem (updMem M P (laneByte v (P.toNat % 4))) (P + 1#32) (laneByte v (P.toNat % 4 + 1)) := by
  rw [and3_toNat]
  have hP := base_add_off P
  generalize P &&& ~~~3#32 = B at hP ⊢
  rcases (show P.toNat % 4 = 0 ∨ P.toNat % 4 = 2 by omega)
    with h | h <;> rw [h] at hP ⊢ <;> rw [hP] <;>
    simp only [storedLanes, HALFWORD, List.range, List.range.loop, List.map,
      BitVec.add_assoc, BitVec.reduceAdd] <;> rfl

theorem lane_sb (v : W32) (N : Nat) (hN : N < 4) :
    laneByte ((low v (32 - 8 * (3 - N)) ++ BitVec.zero (8 * (3 - N))).setWidth 32) N =
      (v &&& 0xff#32).toNat.toUInt8 := by
  rw [laneByte_eq _ _ hN]
  congr 2
  rcases N with _|_|_|_|N
  all_goals first
    | omega
    | (apply BitVec.eq_of_getLsbD_eq; intro i hi
       simp only [low, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
         BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
       rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega)

theorem lane_sh (v : W32) (N : Nat) (hN : N = 0 ∨ N = 2) :
    laneByte ((low v (32 - 8 * (2 - N)) ++ BitVec.zero (8 * (2 - N))).setWidth 32) N =
      ((v >>> 8) &&& 0xff#32).toNat.toUInt8 ∧
    laneByte ((low v (32 - 8 * (2 - N)) ++ BitVec.zero (8 * (2 - N))).setWidth 32) (N + 1) =
      (v &&& 0xff#32).toNat.toUInt8 := by
  rw [laneByte_eq _ _ (by omega), laneByte_eq _ _ (by omega)]
  rcases hN with rfl | rfl <;> constructor <;> congr 2 <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [low, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
    rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-! ## The opening of a proof -/

set_option hygiene false in
/-- The common opening of a 7C S2 refinement theorem (hypotheses named `hg : Good s` and
`hw : enc i = some w`): the word of the encoding, the coprocessor-space checks, `execInstr` =
`execBody`, and the Operation `opn` (applied: `op`) run up to its first GPR reads. Binds
`h0 : readReg s 0 = 0#32`. -/
macro "s2_open" opn:ident op:term : tactic => `(tactic| (
  have h0 := hg.2.2
  cases hw
  rw [execInstr_body s _ rfl rfl rfl, execute_run modelCtx _ _ _ $op rfl
    (by simp [InCop1Space, opcode_iFormat, opcode_trapFormat, funct_trapFormat, opcode_codeFormat,
      funct_codeFormat, opcode_rFormat, funct_rFormat])
    (by simp [InCop0Space, opcode_iFormat, opcode_trapFormat, opcode_codeFormat, opcode_rFormat]) rfl]
  simp only [Pseudo.run, $opn:ident, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, offset16]))

end Refine
