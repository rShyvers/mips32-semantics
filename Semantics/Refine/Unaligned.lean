import Semantics.Refine.BridgeMem

/-!
# Refine.Unaligned — the load/store left/right family against `execInstr`

Sub-wave 7A proves the pilot `lwl`; 7C S2 adds `lwr`, `swl`, `swr`. The manual's formula
`temp ← memword7+8*byte..0 || GPR[rt]23-8*byte..0` on the aligned memory element (MD00086 Vol II-A
Rev 6.06, LWL, p.241) against the model's byte-by-byte `setByteSlot` merge, for each of the four
offsets of the address within its word. `LWR` likewise against the transcription's `temp` line
(`Manual.Ops.LWR`; SPEC-NOTES §11). For `SWL`/`SWR` the lanes `StoreMemory` writes
(`Manual.storedLanes`) of the shifted `dataword` are, lane by lane (`lane_swl`, `lane_swr`), the
register's byte slots the model writes with `getByteSlot` (`swl_fold`, `swr_fold`; `SWR` writes the
same bytes in another order, `updMem_comm`).
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
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl]
    rw [gep_eq s _ (by intro h; cases h) (by intro u h; cases h)]; rfl
  · simp only [↓reduceIte, Option.map_some, Option.getD_some, ha] at hbyte ⊢
    simp only [Pseudo.get, loadMemory_model, ReverseEndian, StatusRE, BigEndianMem,
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

/-! ## 7C S2: LWR, SWL, SWR -/

theorem sub_lane (B : W32) (i j : Nat) (h : j ≤ i) (hi : i < 4) :
    B + BitVec.ofNat 32 i - BitVec.ofNat 32 j = B + BitVec.ofNat 32 (i - j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := B.isLt
  rw [Nat.mod_eq_of_lt (show i < 2^32 by omega), Nat.mod_eq_of_lt (show j < 2^32 by omega),
    Nat.mod_eq_of_lt (show i - j < 2^32 by omega)]
  omega

theorem translate_sub (s : State) (va : W32) (k : Nat) (hk : k ≤ va.toNat % 4) :
    translate s (va - BitVec.ofNat 32 k) = (translate s va).map (· - BitVec.ofNat 32 k) := by
  have hv := va.isLt
  have hsub : (va - BitVec.ofNat 32 k).toNat = va.toNat - k := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2^32 by omega)]; omega
  have h' := translate_add s (va - BitVec.ofNat 32 k) k (by rw [hsub]; omega)
  rw [BitVec.sub_add_cancel] at h'
  rw [h']
  cases translate s (va - BitVec.ofNat 32 k) <;> simp [BitVec.add_sub_cancel]

/-- The spec's `LWR` result for one `byte`, from the four bytes of the aligned word. -/
def lwrSpec (c0 c1 c2 c3 : UInt8) (old : W32) (byte : Nat) : W32 :=
  (old.extractLsb' (32 - 8 * byte) (8 * byte) ++
    (c0.toBitVec ++ c1.toBitVec ++ c2.toBitVec ++ c3.toBitVec : W32).extractLsb' (8 * byte) (32 - 8 * byte)).setWidth 32

set_option hygiene false in
macro "lane_ext" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lwrSpec, low, setByteSlot, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, getLsbD_zeroExtByte]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega))

theorem lwr_off0 (c0 c1 c2 c3 : UInt8) (old : W32) :
    lwrSpec c0 c1 c2 c3 old 3 = setByteSlot old 3 c0 := by lane_ext

theorem lwr_off1 (c0 c1 c2 c3 : UInt8) (old : W32) :
    lwrSpec c0 c1 c2 c3 old 2 = setByteSlot (setByteSlot old 2 c0) 3 c1 := by lane_ext

theorem lwr_off2 (c0 c1 c2 c3 : UInt8) (old : W32) :
    lwrSpec c0 c1 c2 c3 old 1 = setByteSlot (setByteSlot (setByteSlot old 1 c0) 2 c1) 3 c2 := by lane_ext

theorem lwr_off3 (c0 c1 c2 c3 : UInt8) (old : W32) :
    lwrSpec c0 c1 c2 c3 old 0 =
      setByteSlot (setByteSlot (setByteSlot (setByteSlot old 0 c0) 1 c1) 2 c2) 3 c3 := by lane_ext


/-- The register `LWR` writes at a physical address `P`, for each offset `N = P mod 4`
(`byte = 3 - N`). -/
theorem lwr_merge (M : PAddr → UInt8) (P old : W32) :
    (P.toNat % 4 = 0 → (old.extractLsb' (32 - 8 * (3 - 0)) (8 * (3 - 0)) ++
        (MemElemAt M P).extractLsb' (8 * (3 - 0)) (32 - 8 * (3 - 0))).setWidth 32 =
      setByteSlot old 3 (M P)) ∧
    (P.toNat % 4 = 1 → (old.extractLsb' (32 - 8 * (3 - 1)) (8 * (3 - 1)) ++
        (MemElemAt M P).extractLsb' (8 * (3 - 1)) (32 - 8 * (3 - 1))).setWidth 32 =
      setByteSlot (setByteSlot old 2 (M (P - 1#32))) 3 (M P)) ∧
    (P.toNat % 4 = 2 → (old.extractLsb' (32 - 8 * (3 - 2)) (8 * (3 - 2)) ++
        (MemElemAt M P).extractLsb' (8 * (3 - 2)) (32 - 8 * (3 - 2))).setWidth 32 =
      setByteSlot (setByteSlot (setByteSlot old 1 (M (P - 2#32))) 2 (M (P - 1#32))) 3 (M P)) ∧
    (P.toNat % 4 = 3 → (old.extractLsb' (32 - 8 * (3 - 3)) (8 * (3 - 3)) ++
        (MemElemAt M P).extractLsb' (8 * (3 - 3)) (32 - 8 * (3 - 3))).setWidth 32 =
      setByteSlot (setByteSlot (setByteSlot (setByteSlot old 0 (M (P - 3#32))) 1 (M (P - 2#32))) 2
        (M (P - 1#32))) 3 (M P)) := by
  unfold MemElemAt
  have hP := base_add_off P
  generalize P &&& ~~~3#32 = B at hP ⊢
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [h] at hP <;> rw [hP] <;>
    simp only [sub_lane B 1 1 (by omega) (by omega), sub_lane B 2 1 (by omega) (by omega),
      sub_lane B 2 2 (by omega) (by omega), sub_lane B 3 1 (by omega) (by omega),
      sub_lane B 3 2 (by omega) (by omega), sub_lane B 3 3 (by omega) (by omega), Nat.reduceSub,
      BitVec.add_zero]
  · exact lwr_off0 _ _ _ _ _
  · exact lwr_off1 _ _ _ _ _
  · exact lwr_off2 _ _ _ _ _
  · exact lwr_off3 _ _ _ _ _

/-- **LWR refines.** -/
theorem lwr_refines (s : State) (hg : Good s) (base rt off w : W32)
    (hw : enc (.lwr base rt off) = some w) :
    Execute modelCtx w (.lwr base rt off) (abs s) = some (abs (execInstr s (.lwr base rt off))) := by
  s2_open Ops.LWR (Ops.LWR base rt off)
  simp only [execBody]
  have hcomm : signExt16 off + readReg s (regIdx base) = readReg s (regIdx base) + signExt16 off :=
    BitVec.add_comm _ _
  rw [hcomm]
  generalize hva : readReg s (regIdx base) + signExt16 off = va
  rw [addrTrans_run s va .DATA .LOAD _ _ rfl, readMemByte_eq]
  have hbyte : ∀ k, k ≤ va.toNat % 4 →
      (readMemByte s (va - BitVec.ofNat 32 k)).getD 0 =
        ((translate s va).map (fun pa => memOf s.physMem (pa - BitVec.ofNat 32 k))).getD 0 := by
    intro k hk
    rw [readMemByte_eq, translate_sub s va k hk]
    cases translate s va <;> rfl
  unfold translate at hbyte ⊢
  cases ha : accessAllowed s va
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_adel]
  · simp only [↓reduceIte, Option.map_some, Option.getD_some, ha] at hbyte ⊢
    simp only [Pseudo.get, loadMemory_model, ReverseEndian, StatusRE, BigEndianMem,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_true, abs_Mem, setGPR, readGPR_abs s h0,
      addr_recombine]
    generalize hB' : (bits (sign_extend (imm16 off) + readReg s (regIdx base)) 1 0 ^^^
      BitVec.fill 2 (BigEndianCPU (abs s))).toNat = byte'
    rw [offset16, hcomm, hva, show BigEndianCPU (abs s) = true from rfl, byte_idx] at hB'
    generalize hB : (bits va 1 0 ^^^ BitVec.fill 2 (BigEndianCPU (abs s))).toNat = byte
    rw [show BigEndianCPU (abs s) = true from rfl, byte_idx] at hB
    have hPl := fixedMappingPA_low (erlSet s) va
    generalize fixedMappingPA (erlSet s) va = P at hPl hbyte ⊢
    have hm := lwr_merge (memOf s.physMem) P (readReg s (regIdx rt))
    rcases (show va.toNat % 4 = 0 ∨ va.toNat % 4 = 1 ∨ va.toNat % 4 = 2 ∨ va.toNat % 4 = 3 by omega)
      with hN | hN | hN | hN <;>
    · rw [hN] at hB hB' hPl
      subst hB hB'
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
      rw [complete_writeReg_eq s hg.1] <;> rfl


theorem translate_status (s t : State) (h : t.cp0Status = s.cp0Status) (va : W32) :
    translate t va = translate s va := by
  unfold translate accessAllowed kernelMode erlSet; rw [h]

theorem writeMemByte_some (t : State) (a p : W32) (b : UInt8) (h : translate t a = some p) :
    writeMemByte t a b = some { t with physMem := t.physMem.insert p b } := by
  unfold writeMemByte; rw [h]

set_option hygiene false in
macro "slot_ext" : tactic => `(tactic| (
  rw [laneByte_eq _ _ (by omega)]; unfold getByteSlot; congr 2
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [low, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega))

/-- Byte lane `l` of `SWL`'s `dataword` (`0^(24-8*byte) || GPR[rt]31..24-8*byte`) at offset `N` (`byte = 3 - N`) is byte slot `l - N` of the
register. -/
theorem lane_swl (v : W32) (N l : Nat) (h1 : N ≤ l) (h2 : l < 4) :
    laneByte ((BitVec.zero (24 - 8 * (3 - N)) ++ v.extractLsb' (24 - 8 * (3 - N)) (8 + 8 * (3 - N))).setWidth 32) l =
      getByteSlot v (l - N) := by
  rcases l with _|_|_|_|l <;> rcases N with _|_|_|_|N <;> (try omega) <;> slot_ext

/-- Byte lane `l` of `SWR`'s `dataword` (`GPR[rt]31-8*byte..0 || 0^(8*byte)`) at offset `N` is byte slot `l + 3 - N` of the register. -/
theorem lane_swr (v : W32) (N l : Nat) (h1 : l ≤ N) (h2 : N < 4) :
    laneByte ((low v (32 - 8 * (3 - N)) ++ BitVec.zero (8 * (3 - N))).setWidth 32) l =
      getByteSlot v (l + 3 - N) := by
  rcases l with _|_|_|_|l <;> rcases N with _|_|_|_|N <;> (try omega) <;> slot_ext

theorem updMem_comm (M : PAddr → UInt8) (p q : PAddr) (a b : UInt8) (h : p ≠ q) :
    updMem (updMem M p a) q b = updMem (updMem M q b) p a := by
  funext x; simp only [updMem, beq_iff_eq]
  by_cases hq : q = x <;> by_cases hp : p = x <;> simp_all

/-- The model's `swl` byte writes at physical address `P` with offset `N`, on a memory function. -/
def swlBytes (M : PAddr → UInt8) (P v : W32) : Nat → PAddr → UInt8
  | 0 => updMem (updMem (updMem (updMem M P (getByteSlot v 0)) (P + 1#32) (getByteSlot v 1))
      (P + 2#32) (getByteSlot v 2)) (P + 3#32) (getByteSlot v 3)
  | 1 => updMem (updMem (updMem M P (getByteSlot v 0)) (P + 1#32) (getByteSlot v 1))
      (P + 2#32) (getByteSlot v 2)
  | 2 => updMem (updMem M P (getByteSlot v 0)) (P + 1#32) (getByteSlot v 1)
  | _ => updMem M P (getByteSlot v 0)

/-- `SWL`'s `StoreMemory` (lanes `N..3` of the word, `N = pAddr1..0`) as the model's byte writes at
`P, P+1, ...`. -/
theorem swl_fold (M : PAddr → UInt8) (P v : W32) (N : Nat) (hN : P.toNat % 4 = N) :
    (storedLanes (P &&& 3#32).toNat (3 - N)).foldl (fun m l => updMem m ((P &&& ~~~3#32) +
        BitVec.ofNat 32 l) (laneByte ((BitVec.zero (24 - 8 * (3 - N)) ++
          v.extractLsb' (24 - 8 * (3 - N)) (8 + 8 * (3 - N))).setWidth 32) l)) M =
      swlBytes M P v N := by
  rw [and3_toNat, hN]
  have hP := base_add_off P
  rw [hN] at hP
  generalize P &&& ~~~3#32 = B at hP ⊢
  subst hP
  rcases (show N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [show storedLanes 0 (3 - 0) = [0, 1, 2, 3] from rfl]
    simp only [swlBytes, List.foldl, lane_swl v 0 0 (by omega) (by omega), lane_swl v 0 1 (by omega) (by omega),
      lane_swl v 0 2 (by omega) (by omega), lane_swl v 0 3 (by omega) (by omega), Nat.reduceSub,
      BitVec.add_zero]
  · rw [show storedLanes 1 (3 - 1) = [1, 2, 3] from rfl]
    simp only [swlBytes, List.foldl, lane_swl v 1 1 (by omega) (by omega), lane_swl v 1 2 (by omega) (by omega),
      lane_swl v 1 3 (by omega) (by omega), Nat.reduceSub, BitVec.add_assoc, BitVec.reduceAdd]
  · rw [show storedLanes 2 (3 - 2) = [2, 3] from rfl]
    simp only [swlBytes, List.foldl, lane_swl v 2 2 (by omega) (by omega), lane_swl v 2 3 (by omega) (by omega),
      Nat.reduceSub, BitVec.add_assoc, BitVec.reduceAdd]
  · rw [show storedLanes 3 (3 - 3) = [3] from rfl]
    simp only [swlBytes, List.foldl, lane_swl v 3 3 (by omega) (by omega), Nat.reduceSub]

theorem swl_refines (s : State) (hg : Good s) (base rt off w : W32)
    (hw : enc (.swl base rt off) = some w) :
    Execute modelCtx w (.swl base rt off) (abs s) = some (abs (execInstr s (.swl base rt off))) := by
  s2_open Ops.SWL (Ops.SWL base rt off)
  simp only [execBody]
  have hcomm : signExt16 off + readReg s (regIdx base) = readReg s (regIdx base) + signExt16 off :=
    BitVec.add_comm _ _
  rw [hcomm]
  generalize hva : readReg s (regIdx base) + signExt16 off = va
  rw [addrTrans_run s va .DATA .STORE _ _ rfl]
  cases hT : translate s va with
  | none =>
    simp only [writeMemByte, hT]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_ades]
  | some P =>
    have htr : ∀ (t : State) (k : Nat), t.cp0Status = s.cp0Status → k < 4 - va.toNat % 4 →
        translate t (va + BitVec.ofNat 32 k) = some (P + BitVec.ofNat 32 k) := by
      intro t k ht hk
      rw [translate_status s t ht, translate_add s va k (by omega), hT]; rfl
    have hwr : ∀ (t : State) (k : Nat) (b : UInt8), t.cp0Status = s.cp0Status →
        k < 4 - va.toNat % 4 → writeMemByte t (va + BitVec.ofNat 32 k) b =
          some { t with physMem := t.physMem.insert (P + BitVec.ofNat 32 k) b } := by
      intro t k b ht hk; exact writeMemByte_some _ _ _ _ (htr t k ht hk)
    have hPl : P.toNat % 4 = va.toNat % 4 := by
      unfold translate at hT; split at hT
      · cases hT; exact fixedMappingPA_low _ _
      · cases hT
    simp only [writeMemByte_some s va P _ hT]
    simp only [Pseudo.get, ReverseEndian, StatusRE, BigEndianMem, StoreMemory, bind, Pseudo.oracle,
      Pseudo.modify, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_true, abs_Mem,
      readGPR_abs s h0, addr_recombine, show modelCtx.oracle.storeClearsLL (abs s) = true from rfl]
    generalize hB' : (bits (sign_extend (imm16 off) + readReg s (regIdx base)) 1 0 ^^^
      BitVec.fill 2 (BigEndianCPU (abs s))).toNat = byte'
    rw [offset16, hcomm, hva, show BigEndianCPU (abs s) = true from rfl, byte_idx] at hB'
    generalize hB : (bits va 1 0 ^^^ BitVec.fill 2 (BigEndianCPU (abs s))).toNat = byte
    rw [show BigEndianCPU (abs s) = true from rfl, byte_idx] at hB
    rcases (show va.toNat % 4 = 0 ∨ va.toNat % 4 = 1 ∨ va.toNat % 4 = 2 ∨ va.toNat % 4 = 3 by omega)
      with hN | hN | hN | hN <;>
    · rw [hN] at hB hB' hPl
      subst hB hB'
      simp only [hN]
      try simp (disch := first | rfl | omega) only [hwr, Option.getD_some]
      rw [swl_fold _ P _ _ hPl, complete_plain, mkNext, abs_advance _ _ (by rfl)]
      simp only [abs, memOf_insert, swlBytes]
      rfl


/-- The model's `swr` byte writes at physical address `P` with offset `N`, on a memory function. -/
def swrBytes (M : PAddr → UInt8) (P v : W32) : Nat → PAddr → UInt8
  | 0 => updMem M P (getByteSlot v 3)
  | 1 => updMem (updMem M P (getByteSlot v 3)) (P - 1#32) (getByteSlot v 2)
  | 2 => updMem (updMem (updMem M P (getByteSlot v 3)) (P - 2#32) (getByteSlot v 1)) (P - 1#32)
      (getByteSlot v 2)
  | _ => updMem (updMem (updMem (updMem M P (getByteSlot v 3)) (P - 3#32) (getByteSlot v 0))
      (P - 2#32) (getByteSlot v 1)) (P - 1#32) (getByteSlot v 2)

/-- `SWR`'s `StoreMemory` (lanes `0..N` of the word, `N = pAddr1..0`) as the model's byte writes at
`P, P-N, ..., P-1`: the same bytes at distinct addresses, in another order. -/
theorem swr_fold (M : PAddr → UInt8) (P v : W32) (N : Nat) (hN : P.toNat % 4 = N) :
    (storedLanes (P &&& 3#32).toNat (WORD - (3 - N))).foldl (fun m l => updMem m ((P &&& ~~~3#32) +
        BitVec.ofNat 32 l) (laneByte ((low v (32 - 8 * (3 - N)) ++ BitVec.zero (8 * (3 - N))).setWidth 32) l))
        M =
      swrBytes M P v N := by
  rw [and3_toNat, hN]
  have hP := base_add_off P
  rw [hN] at hP
  generalize P &&& ~~~3#32 = B at hP ⊢
  subst hP
  rcases (show N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [show storedLanes 0 (WORD - (3 - 0)) = [0] from rfl]
    simp only [swrBytes, List.foldl, lane_swr v 0 0 (by omega) (by omega), Nat.reduceSub, Nat.reduceAdd]
  · rw [show storedLanes 1 (WORD - (3 - 1)) = [0, 1] from rfl]
    simp only [swrBytes, List.foldl, lane_swr v 1 0 (by omega) (by omega),
      lane_swr v 1 1 (by omega) (by omega), Nat.reduceSub, Nat.reduceAdd, BitVec.add_zero,
      sub_lane B 1 1 (by omega) (by omega)]
    rw [updMem_comm _ (B + 1#32) B _ _ (by bv_omega)]
  · rw [show storedLanes 2 (WORD - (3 - 2)) = [0, 1, 2] from rfl]
    simp only [swrBytes, List.foldl, lane_swr v 2 0 (by omega) (by omega),
      lane_swr v 2 1 (by omega) (by omega), lane_swr v 2 2 (by omega) (by omega), Nat.reduceSub,
      Nat.reduceAdd, BitVec.add_zero, sub_lane B 2 1 (by omega) (by omega),
      sub_lane B 2 2 (by omega) (by omega)]
    rw [updMem_comm _ (B + 2#32) B _ _ (by bv_omega), updMem_comm _ (B + 2#32) (B + 1#32) _ _ (by bv_omega)]
  · rw [show storedLanes 3 (WORD - (3 - 3)) = [0, 1, 2, 3] from rfl]
    simp only [swrBytes, List.foldl, lane_swr v 3 0 (by omega) (by omega),
      lane_swr v 3 1 (by omega) (by omega), lane_swr v 3 2 (by omega) (by omega),
      lane_swr v 3 3 (by omega) (by omega), Nat.reduceSub, Nat.reduceAdd, BitVec.add_zero,
      sub_lane B 3 1 (by omega) (by omega), sub_lane B 3 2 (by omega) (by omega),
      sub_lane B 3 3 (by omega) (by omega)]
    rw [updMem_comm _ (B + 3#32) B _ _ (by bv_omega), updMem_comm _ (B + 3#32) (B + 1#32) _ _ (by bv_omega),
      updMem_comm _ (B + 3#32) (B + 2#32) _ _ (by bv_omega)]

/-- **SWR refines.** -/
theorem swr_refines (s : State) (hg : Good s) (base rt off w : W32)
    (hw : enc (.swr base rt off) = some w) :
    Execute modelCtx w (.swr base rt off) (abs s) = some (abs (execInstr s (.swr base rt off))) := by
  s2_open Ops.SWR (Ops.SWR base rt off)
  simp only [execBody]
  have hcomm : signExt16 off + readReg s (regIdx base) = readReg s (regIdx base) + signExt16 off :=
    BitVec.add_comm _ _
  rw [hcomm]
  generalize hva : readReg s (regIdx base) + signExt16 off = va
  rw [addrTrans_run s va .DATA .STORE _ _ rfl]
  cases hT : translate s va with
  | none =>
    simp only [writeMemByte, hT]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl, gep_ades]
  | some P =>
    have hwr : ∀ (t : State) (k : Nat) (b : UInt8), t.cp0Status = s.cp0Status →
        k ≤ va.toNat % 4 → writeMemByte t (va - BitVec.ofNat 32 k) b =
          some { t with physMem := t.physMem.insert (P - BitVec.ofNat 32 k) b } := by
      intro t k b ht hk
      apply writeMemByte_some
      rw [translate_status s t ht, translate_sub s va k hk, hT]; rfl
    have hPl : P.toNat % 4 = va.toNat % 4 := by
      unfold translate at hT; split at hT
      · cases hT; exact fixedMappingPA_low _ _
      · cases hT
    simp only [writeMemByte_some s va P _ hT]
    simp only [Pseudo.get, ReverseEndian, StatusRE, BigEndianMem, StoreMemory, bind, Pseudo.oracle,
      Pseudo.modify, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_true, abs_Mem,
      readGPR_abs s h0, addr_recombine, show modelCtx.oracle.storeClearsLL (abs s) = true from rfl]
    generalize hB' : (bits (sign_extend (imm16 off) + readReg s (regIdx base)) 1 0 ^^^
      BitVec.fill 2 (BigEndianCPU (abs s))).toNat = byte'
    rw [offset16, hcomm, hva, show BigEndianCPU (abs s) = true from rfl, byte_idx] at hB'
    generalize hB : (bits va 1 0 ^^^ BitVec.fill 2 (BigEndianCPU (abs s))).toNat = byte
    rw [show BigEndianCPU (abs s) = true from rfl, byte_idx] at hB
    rcases (show va.toNat % 4 = 0 ∨ va.toNat % 4 = 1 ∨ va.toNat % 4 = 2 ∨ va.toNat % 4 = 3 by omega)
      with hN | hN | hN | hN <;>
    · rw [hN] at hB hB' hPl
      subst hB hB'
      simp only [hN]
      try simp (disch := first | rfl | omega) only [hwr, Option.getD_some]
      rw [swr_fold _ P _ _ hPl, complete_plain, mkNext, abs_advance _ _ (by rfl)]
      simp only [abs, memOf_insert, swrBytes]
      rfl

end Refine
