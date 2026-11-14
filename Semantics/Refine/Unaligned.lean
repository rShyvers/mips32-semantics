import Semantics.Refine.Fetch

/-!
# Refine.Unaligned — the load/store left/right family against `execInstr`

Sub-wave 7A proves the pilot `lwl`: the manual's formula
`temp ← memword7+8*byte..0 || GPR[rt]23-8*byte..0` on the aligned memory element (MD00086 Vol II-A
Rev 6.06, LWL, p.241) against the model's byte-by-byte `setByteSlot` merge, for each of the four
offsets of the address within its word.
-/

namespace Refine

open Manual

/-- The spec's result for one offset, as a function of the four bytes of the aligned word and the
old register value. -/
def lwlSpec (c0 c1 c2 c3 : UInt8) (old : W32) (byte : Nat) : W32 :=
  (low (c0.toBitVec ++ c1.toBitVec ++ c2.toBitVec ++ c3.toBitVec : W32) (8 + 8 * byte) ++
    low old (24 - 8 * byte)).setWidth 32

theorem getLsbD_zeroExtByte (b : UInt8) (k : Nat) :
    (zeroExtByte b).getLsbD k = (decide (k < 8) && b.toBitVec.getLsbD k) := by
  unfold zeroExtByte; exact getLsbD_ofNat_byte b k

theorem lwl_off0 (c0 c1 c2 c3 : UInt8) (old : W32) :
    lwlSpec c0 c1 c2 c3 old 3 =
      setByteSlot (setByteSlot (setByteSlot (setByteSlot old 0 c0) 1 c1) 2 c2) 3 c3 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lwlSpec, low, setByteSlot, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, getLsbD_zeroExtByte]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem lwl_off1 (c0 c1 c2 c3 : UInt8) (old : W32) :
    lwlSpec c0 c1 c2 c3 old 2 = setByteSlot (setByteSlot (setByteSlot old 0 c1) 1 c2) 2 c3 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lwlSpec, low, setByteSlot, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, getLsbD_zeroExtByte]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem lwl_off2 (c0 c1 c2 c3 : UInt8) (old : W32) :
    lwlSpec c0 c1 c2 c3 old 1 = setByteSlot (setByteSlot old 0 c2) 1 c3 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lwlSpec, low, setByteSlot, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, getLsbD_zeroExtByte]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem lwl_off3 (c0 c1 c2 c3 : UInt8) (old : W32) :
    lwlSpec c0 c1 c2 c3 old 0 = setByteSlot old 0 c3 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lwlSpec, low, setByteSlot, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, getLsbD_zeroExtByte]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

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

/-- The memory element read by `LWL` at an unaligned physical address `P`, merged with `old`, for
each offset `N = P mod 4` (`byte = 3 - N` on a big-endian processor). -/
theorem lwl_merge (M : PAddr → UInt8) (P old : W32) :
    (P.toNat % 4 = 0 → (low (MemElemAt M P) (8 + 8 * (3 - 0)) ++ low old (24 - 8 * (3 - 0))).setWidth 32 =
      setByteSlot (setByteSlot (setByteSlot (setByteSlot old 0 (M P)) 1 (M (P + 1#32))) 2
        (M (P + 2#32))) 3 (M (P + 3#32))) ∧
    (P.toNat % 4 = 1 → (low (MemElemAt M P) (8 + 8 * (3 - 1)) ++ low old (24 - 8 * (3 - 1))).setWidth 32 =
      setByteSlot (setByteSlot (setByteSlot old 0 (M P)) 1 (M (P + 1#32))) 2 (M (P + 2#32))) ∧
    (P.toNat % 4 = 2 → (low (MemElemAt M P) (8 + 8 * (3 - 2)) ++ low old (24 - 8 * (3 - 2))).setWidth 32 =
      setByteSlot (setByteSlot old 0 (M P)) 1 (M (P + 1#32))) ∧
    (P.toNat % 4 = 3 → (low (MemElemAt M P) (8 + 8 * (3 - 3)) ++ low old (24 - 8 * (3 - 3))).setWidth 32 =
      setByteSlot old 0 (M P)) := by
  unfold MemElemAt
  have hP := base_add_off P
  generalize P &&& ~~~3#32 = B at hP ⊢
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [h] at hP <;> rw [hP] <;>
    simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
  · exact lwl_off0 _ _ _ _ _
  · exact lwl_off1 _ _ _ _ _
  · exact lwl_off2 _ _ _ _ _
  · exact lwl_off3 _ _ _ _ _

theorem readMemByte_eq (s : State) (va : W32) :
    readMemByte s va = (translate s va).map (memOf s.physMem) := by
  unfold readMemByte; cases translate s va <;> rfl

/-- **LWL refines.** -/
theorem lwl_refines (s : State) (hg : Good s) (base rt off w : W32)
    (hw : enc (.lwl base rt off) = some w) :
    Execute modelCtx w (.lwl base rt off) (abs s) = some (abs (execInstr s (.lwl base rt off))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = iFormat 0x22#32 base rt off := by
    have : enc (.lwl base rt off) = some (iFormat 0x22#32 base rt off) := rfl
    rw [this] at hw; exact (Option.some.inj hw).symm
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_iFormat]
  have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_iFormat]
  have hex : execInstr s (.lwl base rt off) = execBody s (.lwl base rt off) := by
    have h1 : isBranchLike (.lwl base rt off) = false := rfl
    have h2 : usesCop1 (.lwl base rt off) = false := rfl
    have h3 : usesCop0 (.lwl base rt off) = false := rfl
    unfold execInstr; rw [h1, h2, h3]; rfl
  rw [hex, execute_run modelCtx w _ _ (Ops.LWL base rt off) rfl hc1 hc0 rfl]
  have hbody : execBody s (.lwl base rt off) =
    (let addr := readReg s (regIdx base) + signExt16 off
     match readMemByte s addr with
     | none => takeAddressException s excCodeAdEL addr
     | some b0 =>
       let off := addr.toNat % 4
       let old := readReg s (regIdx rt)
       let v :=
         match off with
         | 0 =>
           let b1 := (readMemByte s (addr + 1#32)).getD 0
           let b2 := (readMemByte s (addr + 2#32)).getD 0
           let b3 := (readMemByte s (addr + 3#32)).getD 0
           setByteSlot (setByteSlot (setByteSlot (setByteSlot old 0 b0) 1 b1) 2 b2) 3 b3
         | 1 =>
           let b1 := (readMemByte s (addr + 1#32)).getD 0
           let b2 := (readMemByte s (addr + 2#32)).getD 0
           setByteSlot (setByteSlot (setByteSlot old 0 b0) 1 b1) 2 b2
         | 2 =>
           let b1 := (readMemByte s (addr + 1#32)).getD 0
           setByteSlot (setByteSlot old 0 b0) 1 b1
         | _ => setByteSlot old 0 b0
       mkNext s (writeReg s (regIdx rt) v)) := rfl
  rw [hbody]
  have hcomm : signExt16 off + readReg s (regIdx base) = readReg s (regIdx base) + signExt16 off :=
    BitVec.add_comm _ _
  simp only [Pseudo.run, Ops.LWL, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, offset16, hcomm]
  generalize hva : readReg s (regIdx base) + signExt16 off = va
  rw [addrTrans_run s va .DATA .LOAD _ _ rfl, readMemByte_eq]
  have hbyte : ∀ k, k < 4 - va.toNat % 4 →
      (readMemByte s (va + BitVec.ofNat 32 k)).getD 0 =
        ((translate s va).map (fun pa => memOf s.physMem (pa + BitVec.ofNat 32 k))).getD 0 := by
    intro k hk
    rw [readMemByte_eq, translate_add s va k (by omega)]
    cases translate s va <;> rfl
  unfold translate at hbyte ⊢
  cases ha : accessAllowed s va
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
    rw [show modelCtx.oracle = modelOracle from rfl]
    rw [gep_eq s _ (by intro h; cases h) (by intro u h; cases h)]; rfl
  · simp only [↓reduceIte, Option.map_some, Option.getD_some, ha] at hbyte ⊢
    simp only [Pseudo.get, LoadMemory, bind, pure, ReverseEndian, StatusRE, BigEndianMem,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_true, abs_Mem, setGPR, readGPR_abs s h0,
      addr_recombine]
    have hBE : BigEndianCPU (abs s) = true := rfl
    generalize hB : (bits (sign_extend (imm16 off) + readReg s (regIdx base)) 1 0 ^^^
      BitVec.fill 2 (BigEndianCPU (abs s))).toNat = byte
    rw [offset16, hcomm, hva, hBE] at hB
    have hlow : (bits va 1 0).toNat = va.toNat % 4 := by
      simp only [bits, BitVec.extractLsb'_toNat]; omega
    have hbyte3 : byte = 3 - va.toNat % 4 := by
      rw [← hB, ← hlow]
      generalize bits va 1 0 = x
      obtain ⟨n, rfl, hn⟩ : ∃ n, x = BitVec.ofNat 2 n ∧ n < 4 :=
        ⟨x.toNat, by simp, x.isLt⟩
      rcases n with _|_|_|_|n
      all_goals first | decide | omega
    have hPl := fixedMappingPA_low (erlSet s) va
    generalize fixedMappingPA (erlSet s) va = P at hPl hbyte ⊢
    have hm := lwl_merge (memOf s.physMem) P (readReg s (regIdx rt))
    have hpc : ∀ v, (writeReg s (regIdx rt) v).pc = s.pc := by
      intro v; unfold writeReg; split <;> rfl
    have hv4 : va.toNat % 4 < 4 := Nat.mod_lt _ (by omega)
    rcases (show va.toNat % 4 = 0 ∨ va.toNat % 4 = 1 ∨ va.toNat % 4 = 2 ∨ va.toNat % 4 = 3 by omega)
      with hN | hN | hN | hN <;>
    · rw [hN] at hbyte3 hPl
      subst hbyte3
      simp only [hN]
      first
        | rw [hm.1 hPl]
        | rw [hm.2.1 hPl]
        | rw [hm.2.2.1 hPl]
        | rw [hm.2.2.2 hPl]
      first
        | rw [hbyte 1 (by omega), hbyte 2 (by omega), hbyte 3 (by omega)]
        | rw [hbyte 1 (by omega), hbyte 2 (by omega)]
        | rw [hbyte 1 (by omega)]
        | skip
      rw [complete_plain, mkNext, abs_advance _ _ (by unfold writeReg; split <;> rfl),
        abs_writeReg _ _ _ hsz, hpc]
      rfl
end Refine
