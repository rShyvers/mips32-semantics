import Semantics.Refine.Memory
import Semantics.Refine.BridgeFpu
import Semantics.Refine.Invariant

/-!
# Refine.BridgeFpuMove — bridge lemmas of the FPU memory/move/control/branch group

Proved once for the refinement theorems of `Refine/FpuMemory.lean`, `FpuMove.lean`,
`FpuControl.lean`:

* `cop1_execute`: `Execute` of an instruction of the COP1 encoding space against
  `execInstr`'s Coprocessor Unusable check (`Cause.CE = 1`, MD00090 Vol III Rev 6.02 §6.2.22, p.100),
  so that each refinement only compares the Operation with the model's `execBody` arm;
* the 64-bit FPRs (`ValueFPR64`/`StoreFPR64`, `FR = 1`) against `readFpD`/`writeFpD`, and the 32-bit
  stores (upper half kept, the model oracle's `fprUpper`) against `writeFpReg`;
* the doubleword accesses (`LDC1`, `SDC1`): translation of `vAddr + 4` and the `pAddr xor 0b100`
  of the second word (the first is at `pAddr` on this little-endian CPU, `endian_xor`);
* the FP control registers (`CFC1`/`CTC1`) against `Mips.Fp.readControl`/`writeControl`, and
  `CheckFPException` against `Mips.Fp.fcsrTrapPending`.
-/

namespace Refine

open Manual

/-! ## The COP1 usability check -/

/-- **A non-CTI instruction of the COP1 encoding space.** If CU1 = 0 both sides take Coprocessor
Unusable (unit 1); otherwise the Operation must match the model's `execBody` arm. -/
theorem cop1_execute (s : State) (w : W32) (i : Instruction) (op : Pseudo Unit)
    (hcti : IsCTI i = false) (h1 : InCop1Space w = true) (h0 : InCop0Space w = false)
    (hop : Operation i = some op) (hbl : isBranchLike i = false) (hc1 : usesCop1 i = true)
    (hc0 : usesCop0 i = false)
    (hbody : cu1Enabled s = true →
      (match op.run modelCtx { arch := abs s } with
       | (.ok (), f) => some (Complete (abs s) f)
       | (.signal e, f) => some (GeneralExceptionProcessing modelImpl modelOracle e f.arch))
        = some (abs (execBody s i))) :
    Execute modelCtx w i (abs s) = some (abs (execInstr s i)) := by
  have hex : execInstr s i =
      if (!cu1Enabled s) = true then takeCoprocessorUnusable s else execBody s i := by
    unfold execInstr; rw [hbl, hc1, hc0]; simp
  rw [hex]
  simp only [Execute, Execute.runOperation, hcti, h1, h0, Bool.false_and, Bool.false_eq_true,
    ite_false, Bool.true_and, cu1_abs]
  cases hu : cu1Enabled s
  · simp only [Bool.not_false, ↓reduceIte]
    rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl,
      gep_eq s (.CoprocessorUnusable 1) (by intro h; cases h) (by intro u h; cases h; omega)]
    rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hop]
    exact hbody hu

/-! ## Registers -/

theorem low_32 (x : W32) : low x 32 = x := by
  unfold low; apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem append_lo (hi lo : W32) : (hi ++ lo).extractLsb' 0 32 = lo := by
  ext i hi'
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]; simp [hi', BitVec.getLsbD_eq_getElem]

theorem append_hi (hi lo : W32) : (hi ++ lo).extractLsb' 32 32 = hi := by
  ext i hi'
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]; simp [hi', BitVec.getLsbD_eq_getElem]

/-! ## Completion of the model's arms -/

theorem abs_mkNext_writeReg (s : State) (i : Fin 32) (v : W32) (hsz : s.regs.size = 32) :
    abs (mkNext s (writeReg s i v)) =
      { writeGPR (abs s) i v with
        PC := (abs s).BranchDelay.getD ((abs s).PC + 4#32)
        BranchDelay := none } := by
  rw [mkNext, abs_advance _ _ (by unfold writeReg; split <;> rfl), abs_writeReg _ _ _ hsz]
  have hpc : (writeReg s i v).pc = s.pc := by unfold writeReg; split <;> rfl
  rw [hpc]; rfl

theorem abs_mkNext_writeFpReg (s : State) (i : Fin 32) (v : W32) (hsz : s.fpRegs.size = 32) :
    abs (mkNext s (writeFpReg s i v)) =
      { abs s with
        FPR := update (abs s).FPR i ((readFpReg64 s i).extractLsb' 32 32 ++ v)
        PC := (abs s).BranchDelay.getD ((abs s).PC + 4#32)
        BranchDelay := none } := by
  rw [mkNext, abs_advance _ _ (by rfl), abs_writeFpReg _ _ _ hsz]; rfl

theorem abs_mkNext_writeFpD (s : State) (fd : W32) (v : BitVec 64) (hsz : s.fpRegs.size = 32) :
    abs (mkNext s (writeFpD s fd v)) =
      { abs s with
        FPR := update (abs s).FPR (reg fd) v
        PC := (abs s).BranchDelay.getD ((abs s).PC + 4#32)
        BranchDelay := none } := by
  rw [mkNext, abs_advance _ _ (by rfl), abs_writeFpD _ hsz]; rfl

/-! ## Instruction words -/

/-- Bit-level equality of two words built from fields (`fld`): compare bit by bit. -/
macro "word_bits" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [opcode, fld, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega))

/-! ## FP control registers -/

/-- Bit-level equality of FCSR expressions: compare bit by bit. -/
macro "bits32" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool, BitVec.getLsbD_not,
    Mips.Fp.readFCCR, Mips.Fp.readFEXR, Mips.Fp.readFENR, Mips.Fp.writeFEXR,
    Mips.Fp.writeFENR, Mips.Fp.writeFCSR, Mips.Fp.readFCSR, FCSRWrite, FCSRWritable, Mips.Fp.fcsrCauseMask,
    Mips.Fp.fcsrFlagsMask, Mips.Fp.fcsrEnablesMask, Mips.Fp.fcsrRMMask, Mips.Fp.fcsrFSMask,
    Mips.Fp.fcsrWritableMask, Mips.Fp.fcsr2008Bits, bits, bit]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega))

/-- `FCSRRead` (the R/W fields and `ABS2008 = NAN2008 = 1`) is the model's `readFCSR`. -/
theorem fcsrRead_abs (s : State) : FCSRRead (abs s) = Mips.Fp.readFCSR s.fcsr := rfl

theorem cfc1_fccr (F : W32) :
    (0#24 ++ (Mips.Fp.readFCSR F).extractLsb' 25 7 ++ BitVec.ofBool (bit (Mips.Fp.readFCSR F) 23) :
      BitVec 32) = Mips.Fp.readFCCR F := by
  bits32

theorem cfc1_fexr (F : W32) :
    (0#14 ++ (Mips.Fp.readFCSR F).extractLsb' 12 6 ++ 0#5 ++ (Mips.Fp.readFCSR F).extractLsb' 2 5 ++ 0#2 :
      BitVec 32) = Mips.Fp.readFEXR F := by
  bits32

theorem cfc1_fenr (F : W32) :
    (0#20 ++ (Mips.Fp.readFCSR F).extractLsb' 7 5 ++ 0#4 ++ BitVec.ofBool (bit (Mips.Fp.readFCSR F) 24) ++
      (Mips.Fp.readFCSR F).extractLsb' 0 2 : BitVec 32) = Mips.Fp.readFENR F := by
  bits32

/-- A word whose non-R/W FCSR bits are 0 is unchanged by `FCSRWrite`. -/
theorem fcsrWrite_of_rz (g : W32) (h : RZ g) : FCSRWrite g = g := by
  unfold RZ at h
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (·.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
  simp only [FCSRWrite, FCSRWritable, BitVec.getLsbD_and]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;>
    simp_all <;> omega

theorem ctc1_fccr (F t : W32) (h : RZ F) :
    FCSRWrite (bits t 7 1 ++ BitVec.ofBool (bit F 24) ++ BitVec.ofBool (bit t 0) ++ bits F 22 0 : BitVec 32) =
      F := by
  rw [← fcsrWrite_of_rz F h]
  bits32

theorem ctc1_fexr (F t : W32) (h : RZ F) :
    FCSRWrite (bits F 31 18 ++ bits t 17 12 ++ bits F 11 7 ++ bits t 6 2 ++ bits F 1 0 : BitVec 32) =
      Mips.Fp.writeFEXR F t := by
  rw [← fcsrWrite_of_rz _ (rz_writeControl F t _ 26 rfl h)]
  bits32

theorem ctc1_fexr' (F t : W32) (h : RZ F) :
    FCSRWrite (F.extractLsb' 18 14 ++ t.extractLsb' 12 6 ++ F.extractLsb' 7 5 ++ t.extractLsb' 2 5 ++
      F.extractLsb' 0 2 : BitVec 32) = Mips.Fp.writeFEXR F t := by
  rw [← fcsrWrite_of_rz _ (rz_writeControl F t _ 26 rfl h)]
  bits32

theorem ctc1_fenr (F t : W32) (h : RZ F) :
    FCSRWrite (bits F 31 25 ++ BitVec.ofBool (bit t 2) ++ bits F 23 12 ++ bits t 11 7 ++ bits F 6 2 ++
      bits t 1 0 : BitVec 32) = Mips.Fp.writeFENR F t := by
  rw [← fcsrWrite_of_rz _ (rz_writeControl F t _ 28 rfl h)]
  bits32

theorem ctc1_fenr' (F t : W32) (h : RZ F) :
    FCSRWrite (F.extractLsb' 25 7 ++ BitVec.ofBool (t.getLsbD 2) ++ F.extractLsb' 12 12 ++
      t.extractLsb' 7 5 ++ F.extractLsb' 2 5 ++ t.extractLsb' 0 2 : BitVec 32) = Mips.Fp.writeFENR F t := by
  rw [← fcsrWrite_of_rz _ (rz_writeControl F t _ 28 rfl h)]
  bits32

/-- `FCSR` bits 22..18 are 0 in the stored word (part of the invariant `FcsrReservedZero`,
`Refine/Defs.lean`). -/
theorem fcsrReservedZero_extract (s : State) (h : FcsrReservedZero s) :
    s.fcsr.extractLsb' 18 5 = 0#5 := by
  unfold FcsrReservedZero at h
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (·.getLsbD (18 + i)) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
  rcases i with _|_|_|_|_|i <;> simp_all <;> omega

/-- `CheckFPException()` (Figure 2.24, p.23) is the model's `Mips.Fp.fcsrTrapPending`. -/
theorem checkFP_run (c : Ctx) (f : Frame) :
    CheckFPException c f =
      if Mips.Fp.fcsrTrapPending f.arch.FCSR then (.signal .FloatingPoint, f) else (.ok (), f) := by
  simp only [CheckFPException, bind, Pseudo.get, Mips.Fp.fcsrTrapPending, Mips.Fp.getCauseE, bit]
  by_cases h : (f.arch.FCSR.getLsbD 17 ||
      (f.arch.FCSR.extractLsb' 12 5 &&& f.arch.FCSR.extractLsb' 7 5 != 0#5)) = true
  · simp only [h, ↓reduceIte]; rfl
  · simp only [h, Bool.false_eq_true, ↓reduceIte]; rfl

theorem toNat_ne_of_ne {fs : W32} {n : Nat} (h : fs ≠ BitVec.ofNat 32 n) (hn : n < 2 ^ 32) :
    fs.toNat ≠ n := by
  intro h'; apply h; apply BitVec.eq_of_toNat_eq; simp [h', Nat.mod_eq_of_lt hn]

/-! ## Doubleword accesses (`LDC1`, `SDC1`) -/

/-- The manual's doubleword alignment test is the model's `% 8`. -/
theorem misaligned8_eq (va : W32) : (bits va 2 0 != 0#3) = decide (va.toNat % 8 ≠ 0) := by
  have : (bits va 2 0).toNat = va.toNat % 8 := by
    simp only [bits, BitVec.extractLsb'_toNat]; omega
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · intro h h'; apply h; apply BitVec.eq_of_toNat_eq; rw [this, h']; rfl
  · intro h h'; apply h; rw [← this, h']; rfl

/-- A doubleword-aligned address is word-aligned. -/
theorem aligned4_of_8 {va : W32} (h : va.toNat % 8 = 0) : va.toNat % 4 = 0 := by omega

/-- `va + 4` of a doubleword-aligned `va` is word-aligned. -/
theorem aligned4_add4 {va : W32} (h : va.toNat % 8 = 0) : (va + 4#32).toNat % 4 = 0 := by
  have := va.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The second word of an aligned doubleword translates to the first word's address plus 4 (the
two words are in the same segment). A copy for `+ 4` with doubleword alignment of
`Refine.translate_add` (`Refine/Unaligned.lean`). -/
theorem translate_add4 (s : State) (va : W32) (h8 : va.toNat % 8 = 0) :
    translate s (va + 4#32) = (translate s va).map (· + 4#32) := by
  have hv := va.isLt
  have hsum : (va + 4#32).toNat = va.toNat + 4 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hacc : accessAllowed s (va + 4#32) = accessAllowed s va := by
    simp only [accessAllowed, isUseg, hsum]
    have : (va.toNat + 4 < 0x80000000) = (va.toNat < 0x80000000) := by
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
    · have h1' : va.toNat + 4 < 0x80000000 := by omega
      simp only [h1, h1', ↓reduceIte]
      split
      · rfl
      · rw [BitVec.add_assoc, BitVec.add_comm 4#32, ← BitVec.add_assoc]
    · by_cases h2 : va.toNat < 0xC0000000
      · have h1' : ¬ va.toNat + 4 < 0x80000000 := by omega
        have h2' : va.toNat + 4 < 0xC0000000 := by omega
        simp only [h1, h2, h1', h2', ↓reduceIte]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_and, hsum, BitVec.toNat_ofNat]
        simp only [show (536870911 : Nat) % 2 ^ 32 = 2 ^ 29 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]
        omega
      · have h1' : ¬ va.toNat + 4 < 0x80000000 := by omega
        have h2' : ¬ va.toNat + 4 < 0xC0000000 := by omega
        simp only [h1, h2, h1', h2', ↓reduceIte]

/-- The Fixed Mapping keeps doubleword alignment. -/
theorem fixedMappingPA_aligned8 (erl : Bool) (va : W32) (h : va.toNat % 8 = 0) :
    (fixedMappingPA erl va).toNat % 8 = 0 := by
  unfold fixedMappingPA
  split
  · split
    · exact h
    · rw [BitVec.toNat_add]; simp; omega
  · split
    · rw [BitVec.toNat_and, show (8:Nat) = 2 ^ 3 by rfl, Nat.and_mod_two_pow, show (2:Nat) ^ 3 = 8 by rfl, h]
      simp
    · exact h

/-- `BigEndianCPU xor ReverseEndian` is 0 on this profile (little-endian, `Status.RE` reads 0): the
`pAddr xor ((BigEndianCPU xor ReverseEndian) || 0^2)` of the doubleword pages leaves the address, so
the word at `pAddr` is the least-significant one. -/
theorem endian_xor (a : Arch) :
    ((BitVec.ofBool (BigEndianCPU a ^^ ReverseEndian a) ++ 0#2 : BitVec 3).setWidth 32) = 0#32 := by
  simp only [BigEndianCPU, ReverseEndian, StatusRE, BigEndianMem, Bool.false_and, Bool.xor_false]
  rfl

theorem getLsbD2_of_aligned8 (pa : W32) (h : pa.toNat % 8 = 0) : pa.getLsbD 2 = false := by
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_false_iff_not]; omega

theorem getLsbD_four (i : Nat) : (4#32).getLsbD i = decide (i = 2) := by
  rcases i with _|_|_|i
  · rfl
  · rfl
  · rfl
  · have : 4 / 2 ^ (i + 3) = 0 := Nat.div_eq_of_lt (by
      calc 4 < 2 ^ 3 := by decide
        _ ≤ 2 ^ (i + 3) := Nat.pow_le_pow_right (by omega) (by omega))
    simp only [BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq, Nat.add_assoc,
      Nat.reduceAdd, this]
    simp

theorem or4_eq_add (pa : W32) (h : pa.toNat % 8 = 0) : pa ||| 4#32 = pa + 4#32 := by
  have h2 := getLsbD2_of_aligned8 pa h
  rw [BitVec.add_eq_or_of_and_eq_zero]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, getLsbD_four]
  by_cases hi2 : i = 2
  · subst hi2; simp only [h2, Bool.false_and]
  · simp only [hi2, decide_false, Bool.and_false]

/-- The first `paddr xor 0b100` of a doubleword access at an aligned `pAddr`: the second word. -/
theorem xor4_eq (pa : W32) (h : pa.toNat % 8 = 0) : pa ^^^ 4#32 = pa + 4#32 := by
  rw [← or4_eq_add pa h]
  have h2 := getLsbD2_of_aligned8 pa h
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, getLsbD_four]
  by_cases hi2 : i = 2
  · subst hi2; simp only [h2, decide_true, Bool.false_xor, Bool.false_or]
  · simp only [hi2, decide_false, Bool.xor_false, Bool.or_false]

/-- The model's four byte inserts of a word store at `p` (`writeMemWord`, the profile's byte
order). -/
def ins4 (m : Std.HashMap PAddr UInt8) (p : PAddr) (v : W32) : Std.HashMap PAddr UInt8 :=
  (((m.insert p (byteOfValue profile.bigEndianMem 4 v 0)).insert (p + 1#32)
    (byteOfValue profile.bigEndianMem 4 v 1)).insert (p + 2#32)
    (byteOfValue profile.bigEndianMem 4 v 2)).insert (p + 3#32) (byteOfValue profile.bigEndianMem 4 v 3)

/-- `writeMemWord` of an aligned, translated address: the four inserts. -/
theorem writeMemWord_eq (s : State) (va : W32) (v : W32) (h : va.toNat % 4 = 0) :
    writeMemWord s va v = (translate s va).map (fun pa => { s with physMem := ins4 s.physMem pa v }) := by
  unfold writeMemWord
  simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]
  cases translate s va <;> rfl

theorem storeWord_ins4 (m : Std.HashMap PAddr UInt8) (pa : PAddr) (v : W32) (h : pa.toNat % 4 = 0) :
    (storedLanes (pa &&& 3#32).toNat WORD).foldl
        (fun mm l => updMem mm ((pa &&& ~~~3#32) + BitVec.ofNat 32 l) (laneByte v l)) (memOf m) =
      memOf (ins4 m pa v) :=
  storeWord_mem m pa v h

end Refine
