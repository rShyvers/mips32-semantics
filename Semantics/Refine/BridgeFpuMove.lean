import Semantics.Refine.Memory
import Semantics.Refine.BridgeFpu
import Semantics.Refine.Invariant

/-!
# Refine.BridgeFpuMove — bridge lemmas of the FPU memory/move/control/branch group (7C S4b)

Proved once for the refinement theorems of `Refine/FpuMemory.lean`, `FpuMove.lean`,
`FpuControl.lean` and `FpuBranch.lean`:

* `cop1_execute` / `cop1_cti_execute`: `Execute` of an instruction of the COP1 encoding space against
  `execInstr`'s Coprocessor Unusable check (`Cause.CE = 1`, MD00090 Vol III Rev 6.02 §6.2.22, p.100),
  so that each refinement only compares the Operation with the model's `execBody` arm;
* the FPR pair (`ValueFPR64`/`StoreFPR64` under `modelOracle`, whose odd-register outcomes are the
  even-register formula) against `readFpD`/`writeFpD`;
* `FPConditionCode` of the 3-bit `cc` field against `readFcc`;
* the doubleword accesses (`LDC1`, `SDC1`, `LDXC1`, `SDXC1`): translation of `vAddr + 4`, the
  `pAddr xor 0b100` of a big-endian CPU, and the order of the two word stores;
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

/-- **A CTI of the COP1 encoding space** (`BC1F` … `BC1TL`): in a delay slot both sides take
Reserved Instruction (`Oracle.ctiInSlot`, checked before the coprocessor), otherwise as
`cop1_execute`. -/
theorem cop1_cti_execute (s : State) (w : W32) (i : Instruction) (op : Pseudo Unit)
    (hcti : IsCTI i = true) (hp : IsPAUSE i = false) (h1 : InCop1Space w = true)
    (h0 : InCop0Space w = false) (hop : Operation i = some op) (hbl : isBranchLike i = true)
    (hc1 : usesCop1 i = true) (hc0 : usesCop0 i = false)
    (hbody : s.pendingBranch = none → cu1Enabled s = true →
      (match op.run modelCtx { arch := abs s } with
       | (.ok (), f) => some (Complete (abs s) f)
       | (.signal e, f) => some (GeneralExceptionProcessing modelImpl modelOracle e f.arch))
        = some (abs (execBody s i))) :
    Execute modelCtx w i (abs s) = some (abs (execInstr s i)) := by
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w i s t hcti hp hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    have hex : execInstr s i =
        if (!cu1Enabled s) = true then takeCoprocessorUnusable s else execBody s i := by
      unfold execInstr; rw [hbl, hc1, hc0, hpb]; simp
    have hb : (abs s).BranchDelay.isSome = false := by simp [abs, hpb]
    rw [hex]
    simp only [Execute, Execute.runOperation, hb, Bool.and_false, Bool.false_eq_true, ite_false,
      h1, h0, Bool.false_and, Bool.true_and, cu1_abs]
    cases hu : cu1Enabled s
    · simp only [Bool.not_false, ↓reduceIte]
      rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl,
        gep_eq s (.CoprocessorUnusable 1) (by intro h; cases h) (by intro u h; cases h; omega)]
      rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hop]
      exact hbody hpb hu

/-! ## Registers -/

theorem update_self (f : Fin 32 → W32) (i : Fin 32) : update f i (f i) = f := by
  funext j; unfold update; split <;> simp_all

theorem regIdx_succ (f : W32) : regIdx (f + 1#32) = reg f + 1 := by
  rw [regIdx_eq_reg]; unfold reg
  apply Fin.ext
  simp only [Fin.val_add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem reg_succ (f : W32) : reg (f + 1#32) = reg f + 1 := by
  rw [← regIdx_eq_reg]; exact regIdx_succ f

theorem low_32 (x : W32) : low x 32 = x := by
  unfold low; apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem append_lo (hi lo : W32) : (hi ++ lo).extractLsb' 0 32 = lo := by
  ext i hi'
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]; simp [hi', BitVec.getLsbD_eq_getElem]

theorem append_hi (hi lo : W32) : (hi ++ lo).extractLsb' 32 32 = hi := by
  ext i hi'
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]; simp [hi', BitVec.getLsbD_eq_getElem]

/-! ## Condition codes -/

/-- `FPConditionCode` of the 3-bit `cc` field is the model's condition-code read (`readFcc`). -/
theorem fpcc_run (c : Ctx) (f : Frame) (cc : W32) :
    FPConditionCode (low cc 3).toNat c f = (.ok (Mips.Fp.getCC f.arch.FCSR (ccIdx cc)), f) := by
  have hl : (low cc 3).toNat = cc.toNat % 8 := by
    simp only [low, BitVec.extractLsb'_toNat]; omega
  simp only [FPConditionCode, bind, Pseudo.get, hl, Mips.Fp.getCC, Mips.Fp.ccBit, ccIdx,
    Fin.val_ofNat, bit]
  by_cases h : cc.toNat % 8 = 0 <;> simp [h, pure]

/-! ## Completion of the model's arms -/

theorem abs_mkNext_self (s : State) :
    abs (mkNext s s) =
      { abs s with
        PC := (abs s).BranchDelay.getD ((abs s).PC + 4#32)
        BranchDelay := none } := by
  rw [mkNext, abs_advance _ _ (by rfl)]; rfl

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
        FPR := update (abs s).FPR i v
        PC := (abs s).BranchDelay.getD ((abs s).PC + 4#32)
        BranchDelay := none } := by
  rw [mkNext, abs_advance _ _ (by rfl), abs_writeFpReg _ _ _ hsz]; rfl

theorem abs_mkNext_writeFpD (s : State) (fd : W32) (v : BitVec 64) (hsz : s.fpRegs.size = 32) :
    abs (mkNext s (writeFpD s fd v)) =
      { abs s with
        FPR := update (update (abs s).FPR (reg fd) (v.extractLsb' 0 32)) (reg fd + 1)
          (v.extractLsb' 32 32)
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

/-- The `MOVF.fmt`/`MOVT.fmt` and `MOVF`/`MOVT` diagram (`... | cc | 0 | tf | ...`). -/
theorem opcode_movcf (op a cc tf b c fn : W32) :
    opcode (fld 6 26 op ||| fld 5 21 a ||| fld 3 18 cc ||| fld 1 16 tf ||| fld 5 11 b ||| fld 5 6 c |||
      fld 6 0 fn) = op &&& 0x3F#32 := by word_bits

theorem funct_movcf (op a cc tf b c fn : W32) :
    (fld 6 26 op ||| fld 5 21 a ||| fld 3 18 cc ||| fld 1 16 tf ||| fld 5 11 b ||| fld 5 6 c |||
      fld 6 0 fn) &&& 0x3F#32 = fn &&& 0x3F#32 := by word_bits

theorem opcode_movci (rs cc tf rd fn : W32) :
    opcode (fld 6 26 0#32 ||| fld 5 21 rs ||| fld 3 18 cc ||| fld 1 16 tf ||| fld 5 11 rd |||
      fld 6 0 fn) = 0#32 := by word_bits

theorem funct_movci (rs cc tf rd fn : W32) :
    (fld 6 26 0#32 ||| fld 5 21 rs ||| fld 3 18 cc ||| fld 1 16 tf ||| fld 5 11 rd |||
      fld 6 0 fn) &&& 0x3F#32 = fn &&& 0x3F#32 := by word_bits

/-- The `BC1F` … `BC1TL` diagram (`COP1 | BC | cc | nd | tf | offset`). -/
theorem opcode_bc1 (op a cc nd tf imm : W32) :
    opcode (fld 6 26 op ||| fld 5 21 a ||| fld 3 18 cc ||| fld 1 17 nd ||| fld 1 16 tf |||
      fld 16 0 imm) = op &&& 0x3F#32 := by word_bits

/-! ## FP control registers -/

/-- Bit-level equality of FCSR expressions: compare bit by bit. -/
macro "bits32" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool, BitVec.getLsbD_not,
    Mips.Fp.readFCCR, Mips.Fp.readFEXR, Mips.Fp.readFENR, Mips.Fp.writeFCCR, Mips.Fp.writeFEXR,
    Mips.Fp.writeFENR, Mips.Fp.writeFCSR, Mips.Fp.fcsrFCCMask, Mips.Fp.fcsrCauseMask,
    Mips.Fp.fcsrFlagsMask, Mips.Fp.fcsrEnablesMask, Mips.Fp.fcsrRMMask, Mips.Fp.fcsrFSMask,
    Mips.Fp.fcsrWritableMask, bits, bit]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega))

theorem cfc1_fccr (F : W32) :
    (0#24 ++ F.extractLsb' 25 7 ++ BitVec.ofBool (bit F 23) : BitVec 32) = Mips.Fp.readFCCR F := by
  bits32

theorem cfc1_fexr (F : W32) :
    (0#14 ++ F.extractLsb' 12 6 ++ 0#5 ++ F.extractLsb' 2 5 ++ 0#2 : BitVec 32) = Mips.Fp.readFEXR F := by
  bits32

theorem cfc1_fenr (F : W32) :
    (0#20 ++ F.extractLsb' 7 5 ++ 0#4 ++ BitVec.ofBool (bit F 24) ++ F.extractLsb' 0 2 : BitVec 32) =
      Mips.Fp.readFENR F := by
  bits32

theorem ctc1_fccr (F t : W32) :
    (bits t 7 1 ++ BitVec.ofBool (bit F 24) ++ BitVec.ofBool (bit t 0) ++ bits F 22 0 : BitVec 32) =
      Mips.Fp.writeFCCR F t := by
  bits32

theorem ctc1_fccr' (F t : W32) :
    (t.extractLsb' 1 7 ++ BitVec.ofBool (F.getLsbD 24) ++ BitVec.ofBool (t.getLsbD 0) ++
      F.extractLsb' 0 23 : BitVec 32) = Mips.Fp.writeFCCR F t := by
  bits32

theorem ctc1_fexr (F t : W32) :
    (bits F 31 18 ++ bits t 17 12 ++ bits F 11 7 ++ bits t 6 2 ++ bits F 1 0 : BitVec 32) =
      Mips.Fp.writeFEXR F t := by
  bits32

theorem ctc1_fexr' (F t : W32) :
    (F.extractLsb' 18 14 ++ t.extractLsb' 12 6 ++ F.extractLsb' 7 5 ++ t.extractLsb' 2 5 ++
      F.extractLsb' 0 2 : BitVec 32) = Mips.Fp.writeFEXR F t := by
  bits32

theorem ctc1_fenr (F t : W32) :
    (bits F 31 25 ++ BitVec.ofBool (bit t 2) ++ bits F 23 12 ++ bits t 11 7 ++ bits F 6 2 ++
      bits t 1 0 : BitVec 32) = Mips.Fp.writeFENR F t := by
  bits32

theorem ctc1_fenr' (F t : W32) :
    (F.extractLsb' 25 7 ++ BitVec.ofBool (t.getLsbD 2) ++ F.extractLsb' 12 12 ++ t.extractLsb' 7 5 ++
      F.extractLsb' 2 5 ++ t.extractLsb' 0 2 : BitVec 32) = Mips.Fp.writeFENR F t := by
  bits32

theorem ctc1_fcsr' (F t : W32) : t &&& ~~~(0x1F#32 <<< 18) = Mips.Fp.writeFCSR F t := by
  bits32


/-- `FCSR` bits 22..18 (`Impl`, reserved, `ABS2008`, `NAN2008`) "read as zero" on this profile
(MD00082 Vol I-A Rev 6.01, Table 6.8, p.93: `Impl` "If these bits are not implemented, they must be
ignored on write and read as zero"; bit 20 "Reserved for future use; reads as zero"; `ABS2008`/
`NAN2008` exist only if `FIR.Has2008` is set). The invariant `FcsrReservedZero`
(`Refine/Invariant.lean`, part of `Inv`) as the 5-bit field the refinement of `CFC1 rt, 31` uses. -/
theorem fcsrReservedZero_extract (s : State) (h : FcsrReservedZero s) :
    s.fcsr.extractLsb' 18 5 = 0#5 := by
  unfold FcsrReservedZero at h
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (·.getLsbD (18 + i)) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
  rcases i with _|_|_|_|_|i <;> simp_all <;> omega

theorem readFCSR_of_reserved (F : W32) (h : F.extractLsb' 18 5 = 0#5) : Mips.Fp.readFCSR F = F := by
  have hk : ∀ k, k < 5 → F.getLsbD (18 + k) = false := by
    intro k hk
    have := congrArg (fun x => x.getLsbD k) h
    simpa [BitVec.getLsbD_extractLsb', hk] using this
  have h18 := hk 0 (by omega); have h19 := hk 1 (by omega); have h20 := hk 2 (by omega)
  have h21 := hk 3 (by omega); have h22 := hk 4 (by omega)
  simp only [Nat.add_zero, Nat.reduceAdd] at h18 h19 h20 h21 h22
  rw [BitVec.getLsbD_eq_getElem (by omega)] at h18 h19 h20 h21 h22
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Mips.Fp.readFCSR, Mips.Fp.fcsrWritableMask, BitVec.getLsbD_and]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;>
    simp [h18, h19, h20, h21, h22] <;> omega

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

/-! ## Doubleword accesses (`LDC1`, `SDC1`, `LDXC1`, `SDXC1`) -/

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

/-- `BigEndianCPU xor ReverseEndian` is 1 on this profile (big-endian, `Status.RE` reads 0): the
`pAddr xor ((BigEndianCPU xor ReverseEndian) || 0^2)` of the doubleword pages flips bit 2. -/
theorem endian_xor (a : Arch) :
    ((BitVec.ofBool (BigEndianCPU a ^^ ReverseEndian a) ++ 0#2 : BitVec 3).setWidth 32) = 4#32 := by
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

/-- The second `paddr xor 0b100`: back to the first word. -/
theorem xor4_xor4 (pa : W32) (h : pa.toNat % 8 = 0) : (pa + 4#32) ^^^ 4#32 = pa := by
  rw [← xor4_eq pa h, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The model's four byte inserts of a big-endian word store at `p` (`writeMemWord`). -/
def ins4 (m : Std.HashMap PAddr UInt8) (p : PAddr) (v : W32) : Std.HashMap PAddr UInt8 :=
  (((m.insert p ((v >>> 24) &&& 0xff#32).toNat.toUInt8).insert (p + 1#32)
    ((v >>> 16) &&& 0xff#32).toNat.toUInt8).insert (p + 2#32) ((v >>> 8) &&& 0xff#32).toNat.toUInt8).insert
    (p + 3#32) (v &&& 0xff#32).toNat.toUInt8

/-- The two word stores of a doubleword commute (their bytes are disjoint): the manual stores the
word at `pAddr + 4` first (`paddr xor 0b100`), the model the word at `pAddr`. -/
theorem memOf_ins4_swap (m : Std.HashMap PAddr UInt8) (pa v w : W32) :
    memOf (ins4 (ins4 m (pa + 4#32) w) pa v) = memOf (ins4 (ins4 m pa v) (pa + 4#32) w) := by
  simp only [ins4, memOf_insert]
  funext x
  simp only [updMem, beq_iff_eq]
  repeat' split
  all_goals first | rfl | (exfalso; bv_omega)

/-- `writeMemWord` of an aligned, translated address: the four inserts. -/
theorem writeMemWord_eq (s : State) (va : W32) (v : W32) (h : va.toNat % 4 = 0) :
    writeMemWord s va v = (translate s va).map (fun pa => { s with physMem := ins4 s.physMem pa v }) := by
  unfold writeMemWord
  simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]
  cases translate s va <;> rfl

theorem writeFpReg2_eq (s : State) (ft lo hi : W32) :
    writeFpReg (writeFpReg s (regIdx ft) lo) (regIdx (ft + 1#32)) hi = writeFpD s ft (hi ++ lo) := by
  simp only [writeFpD, append_lo, append_hi]

theorem storeWord_ins4 (m : Std.HashMap PAddr UInt8) (pa : PAddr) (v : W32) (h : pa.toNat % 4 = 0) :
    (storedLanes (pa &&& 3#32).toNat WORD).foldl
        (fun mm l => updMem mm ((pa &&& ~~~3#32) + BitVec.ofNat 32 l) (laneByte v l)) (memOf m) =
      memOf (ins4 m pa v) :=
  storeWord_mem m pa v h

end Refine
