import Semantics.Refine.Abs

/-!
# Refine.Bridge — the model's helpers against the manual's functions

Bit-level and record-level facts, proved once: the CP0 field reads, `advance` against the manual's
completion, the general exception processing against `exceptionEntry`. The per-instruction
refinement theorems (`Refine/Pilots.lean`, later `Refine/<Family>.lean`) rewrite with these.
-/

namespace Refine

open Manual

/-! ## Constants -/

theorem fieldOnes_29_12 : fieldOnes 29 12 = ebaseWriteMask := by decide
theorem statusWritable_eq : StatusWritable = statusWriteMask := by decide
theorem causeWritable_eq : CauseWritable = causeWriteMask := by decide
theorem hwrenaWritable_eq : HWREnaWritable = hwrenaWriteMask := by decide

/-! ## Single bits -/

theorem and_twoPow_ne (x : W32) (i : Nat) (h : i < 32) :
    (x &&& BitVec.twoPow 32 i != 0#32) = x.getLsbD i := by
  rw [BitVec.and_twoPow]
  have hne : BitVec.twoPow 32 i ≠ 0#32 := by
    intro h'; have := congrArg (·.getLsbD i) h'; simp [h] at this
  split <;> simp_all

theorem and_twoPow_eq (x : W32) (i : Nat) (h : i < 32) :
    (x &&& BitVec.twoPow 32 i == 0#32) = !x.getLsbD i := by
  rw [← and_twoPow_ne x i h]; simp [bne]

theorem exl_abs (s : State) : StatusEXL (abs s) = (s.cp0Status &&& statusExlMask != 0#32) := by
  rw [show statusExlMask = BitVec.twoPow 32 1 by decide, and_twoPow_ne _ 1 (by omega)]; rfl

theorem bev_abs (s : State) : StatusBEV (abs s) = !(s.cp0Status &&& statusBevMask == 0#32) := by
  rw [show statusBevMask = BitVec.twoPow 32 22 by decide, and_twoPow_eq _ 22 (by omega)]
  simp [StatusBEV, abs, bit]

/-! ## Completion -/

/-- `advance` (the model's delay-slot exit) is the manual's completion of an instruction that
assigned no `PC` and scheduled no `I+1:` effect. -/
theorem abs_advance (s r : State) (hpb : r.pendingBranch = s.pendingBranch) :
    abs (advance s r) =
      { abs r with PC := s.pendingBranch.getD (r.pc + 4#32), BranchDelay := none } := by
  unfold advance
  cases h : s.pendingBranch <;> simp [abs, hpb, h, readReg, readFpReg]

theorem complete_plain (a : Arch) (x : Arch) :
    Complete a { arch := x } = { x with PC := a.BranchDelay.getD (a.PC + 4#32), BranchDelay := none } :=
  rfl

/-! ## Exception entry -/

/-- The `Cause` update of the general exception processing, the model's way and the manual's. -/
theorem cause_update (C : W32) (code : BitVec 5) (ce : BitVec 2) :
    ((C &&& ~~~(causeExcCodeMask ||| causeCeMask)) ||| ((code.setWidth 32 <<< 2) &&& causeExcCodeMask)) |||
        ((ce.setWidth 32 <<< 28) &&& causeCeMask)
      = (C &&& ~~~((3#32 <<< 28) ||| (0x1F#32 <<< 2))) ||| (ce.setWidth 32 <<< 28) |||
          (code.setWidth 32 <<< 2) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, causeExcCodeMask, causeCeMask, hi]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- The general exception vector, the manual's sum against the model's `exceptionVector`. -/
theorem vector_eq (s : State) :
    (vectorBase (abs s)).extractLsb' 30 2 ++
        ((vectorBase (abs s)).extractLsb' 0 30 + (0x180#32).extractLsb' 0 30) = exceptionVector s := by
  unfold vectorBase exceptionVector
  rw [bev_abs]
  cases hb : (s.cp0Status &&& statusBevMask == 0#32)
  · simp; decide
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true, EBaseRead, fieldOnes_29_12,
      ebaseValue, ebaseWriteMask, ebaseFixedBits, exceptionVectorOffset, abs]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.add_eq_or_of_and_eq_zero]
    · simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_append,
        BitVec.getLsbD_extractLsb']
      rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega
    · apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_extractLsb',
        BitVec.getLsbD_or, BitVec.getLsbD_zero]
      rcases j with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|j <;> simp <;> omega

/-- The model's `ce` argument for an exception (the unit number for Coprocessor Unusable, else 0). -/
def ceOf : Exception → W32
  | .CoprocessorUnusable u => BitVec.ofNat 32 u
  | _ => 0#32

/-- The model's state with the "Additional State Saved" of an exception (`BadVAddr` for Address
Error), as `takeAddressException` writes it before the entry. -/
def badv (e : Exception) (s : State) : State :=
  match e with
  | .AddressErrorLoad v | .AddressErrorStore v => { s with cp0BadVAddr := v }
  | _ => s

theorem additional_abs (e : Exception) (s : State) : AdditionalState e (abs s) = abs (badv e s) := by
  cases e <;> rfl

theorem ce_eq (e : Exception) (hu : ∀ u, e = .CoprocessorUnusable u → u < 4) :
    ceOf e = (FaultingCoprocessorNumber modelOracle (abs s) e).setWidth 32 := by
  cases e with
  | CoprocessorUnusable u =>
    have := hu u rfl
    simp only [ceOf, FaultingCoprocessorNumber]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]; omega
  | _ => rfl

/-- **General exception processing = `exceptionEntry`** for every exception but the Interrupt
(whose vector the model's `takeInterrupt` sets afterwards), with the model's `Cause.CE` choice. -/
theorem gep_eq (s : State) (e : Exception) (he : e ≠ .Interrupt)
    (hu : ∀ u, e = .CoprocessorUnusable u → u < 4) :
    GeneralExceptionProcessing modelOracle e (abs s) =
      abs (exceptionEntry (badv e s) ((ExcCode e).setWidth 32) (ceOf e)) := by
  have hoff : vectorOffset (abs s) e = 0x180#32 := by
    unfold vectorOffset; split
    · rfl
    · cases e <;> first | rfl | exact absurd rfl he
  have hvec : exceptionVector (badv e s) = exceptionVector s := by cases e <;> rfl
  have hexl : StatusEXL (abs (badv e s)) = StatusEXL (abs s) := by cases e <;> rfl
  have hbase : vectorBase (abs s) = vectorBase (abs (badv e s)) := by cases e <;> rfl
  have hce := ce_eq (s := s) e hu
  have hv := vector_eq s
  have hab : AdditionalState e (abs s) = abs (badv e s) := additional_abs e s
  simp only [GeneralExceptionProcessing, hoff, hab, hv]
  have hexl' : StatusEXL (abs (badv e s)) = ((badv e s).cp0Status &&& statusExlMask != 0#32) :=
    exl_abs _
  rw [hexl', ← hvec, ← cause_update, ← hce]
  rfl
/-! ## Integer arithmetic -/

theorem toNat_sx33 (x : W32) :
    (BitVec.ofBool (bit x 31) ++ x).toNat = (if bit x 31 then 2^32 else 0) + x.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]
  cases bit x 31 <;> simp

theorem bit31_iff (x : W32) : bit x 31 = decide (2^31 ≤ x.toNat) := by
  simp only [bit, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  have := x.isLt
  by_cases h : 2^31 ≤ x.toNat
  · have : x.toNat / 2^31 = 1 := by omega
    simp [this, h]
  · have : x.toNat / 2^31 = 0 := by omega
    simp [this, h]

theorem add33_low (x y : W32) :
    low ((BitVec.ofBool (bit x 31) ++ x) + (BitVec.ofBool (bit y 31) ++ y)) 32 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp only [low, BitVec.extractLsb'_toNat, BitVec.toNat_add, toNat_sx33]
  have hx := x.isLt; have hy := y.isLt
  cases bit x 31 <;> cases bit y 31 <;> simp <;> omega

theorem add_ovf (x y : W32) :
    decide (bit ((BitVec.ofBool (bit x 31) ++ x) + (BitVec.ofBool (bit y 31) ++ y)) 32 ≠
        bit ((BitVec.ofBool (bit x 31) ++ x) + (BitVec.ofBool (bit y 31) ++ y)) 31)
      = addOverflows (asSigned x) (asSigned y) (asSigned (x + y)) := by
  have hx := x.isLt; have hy := y.isLt
  have e1 : ∀ (t : BitVec 33) k, bit t k = decide (t.toNat / 2^k % 2 = 1) := by
    intro t k; simp [bit, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  rw [e1, e1]
  simp only [BitVec.toNat_add, toNat_sx33]
  simp only [bit31_iff]
  simp only [addOverflows, asSigned, BitVec.toInt_eq_toNat_cond, BitVec.toNat_add]
  by_cases h1 : 2^31 ≤ x.toNat <;> by_cases h2 : 2^31 ≤ y.toNat <;>
    by_cases h3 : 2 * ((x.toNat + y.toNat) % 4294967296) < 4294967296 <;>
    (rw [Bool.eq_iff_iff]; simp [h1, h2, h3]; omega)

/-! ## The model's context and the encoding spaces -/

/-- The context of the model's choices. -/
def modelCtx : Ctx := { impl := modelImpl, oracle := modelOracle }

theorem opcode_rFormat (op rs rt rd sa fn : W32) :
    opcode (rFormat op rs rt rd sa fn) = op &&& 0x3F#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [opcode, rFormat, fld, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem funct_rFormat (op rs rt rd sa fn : W32) :
    rFormat op rs rt rd sa fn &&& 0x3F#32 = fn &&& 0x3F#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [rFormat, fld, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem opcode_iFormat (op rs rt imm : W32) : opcode (iFormat op rs rt imm) = op &&& 0x3F#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [opcode, iFormat, fld, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- `sign_extend(offset || 0^2)` is the model's branch displacement `signExt16 imm <<< 2`. -/
theorem branch_offset (imm : W32) : sign_extend (imm16 imm ++ 0#2) = signExt16 imm <<< 2 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [sign_extend, imm16, signExt16, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb, BitVec.msb_append]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- `sign_extend(offset)` is the model's `signExt16`. -/
theorem offset16 (imm : W32) : sign_extend (imm16 imm) = signExt16 imm := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [sign_extend, imm16, signExt16, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_extractLsb, BitVec.msb_eq_getLsbD_last]

theorem cu1_abs (s : State) : StatusCU1 (abs s) = cu1Enabled s := by
  rw [cu1Enabled, show statusCu1Mask = BitVec.twoPow 32 29 by decide, and_twoPow_ne _ 29 (by omega)]; rfl

theorem kernel_abs (s : State) : KernelMode (abs s) = kernelMode s := by
  simp only [KernelMode, kernelMode, StatusUM, StatusEXL, StatusERL, abs, bit,
    show statusUmMask = BitVec.twoPow 32 4 by decide, show statusExlMask = BitVec.twoPow 32 1 by decide,
    show statusErlMask = BitVec.twoPow 32 2 by decide, and_twoPow_ne _ 1 (by omega),
    and_twoPow_ne _ 2 (by omega), and_twoPow_eq _ 4 (by omega)]

theorem cp0usable_abs (s : State) : CP0Usable (abs s) = cp0Usable s := by
  rw [CP0Usable, cp0Usable, kernel_abs, show statusCu0Mask = BitVec.twoPow 32 28 by decide,
    and_twoPow_ne _ 28 (by omega)]; rfl

/-- `Execute` when the instruction is not a CTI and its word is outside the unusable coprocessors'
spaces runs the Operation. -/
theorem execute_run (c : Ctx) (w : W32) (i : Instruction) (a : Arch) (op : Pseudo Unit)
    (hcti : IsCTI i = false) (h1 : InCop1Space w = false) (h0 : InCop0Space w = false)
    (hop : Operation i = some op) :
    Execute c w i a =
      match op.run c { arch := a } with
      | (.ok (), f) => some (Complete a f)
      | (.signal e, f) => some (GeneralExceptionProcessing c.oracle e f.arch) := by
  simp only [Execute, Execute.runOperation, hcti, h1, h0, hop, Bool.false_and, Bool.false_eq_true, ite_false]
  rfl

/-- The exceptions that save no extra state and load no `CE`. -/
def Simple : Exception → Bool
  | .SystemCall | .Breakpoint | .ReservedInstruction | .IntegerOverflow | .Trap | .FloatingPoint => true
  | _ => false

/-- The general exception processing for an exception that saves nothing more and has no `CE`:
the model's `takeException`. -/
theorem gep_take (s : State) (e : Exception) (hs : Simple e = true)
    (code : W32) (hc : code = (ExcCode e).setWidth 32) :
    GeneralExceptionProcessing modelOracle e (abs s) = abs (takeException s code) := by
  have he : e ≠ .Interrupt := by intro h; subst h; cases hs
  rw [gep_eq s e he (fun u h => by subst h; cases hs), hc]
  have hb : badv e s = s := by cases e <;> first | rfl | cases hs
  have hce : ceOf e = 0#32 := by cases e <;> first | rfl | cases hs
  rw [hb, hce]; rfl

/-- A CTI (other than `PAUSE`) in a delay slot: the model's choice is Reserved Instruction. -/
theorem execute_cti_slot (w : W32) (i : Instruction) (s : State) (t : W32)
    (hcti : IsCTI i = true) (hp : IsPAUSE i = false) (hpb : s.pendingBranch = some t) :
    Execute modelCtx w i (abs s) = some (abs (takeException s excCodeRI)) := by
  have hb : (abs s).BranchDelay.isSome = true := by simp [abs, hpb]
  have hc : modelCtx.oracle.ctiInSlot (abs s) i = .signal .ReservedInstruction := by
    simp [modelCtx, modelOracle, hp]
  simp only [Execute, hcti, hb, Bool.and_self, ↓reduceIte, hc]
  rw [show modelCtx.oracle = modelOracle from rfl,
    gep_take s .ReservedInstruction rfl excCodeRI (by decide)]

/-- A CTI outside a delay slot runs its Operation. -/
theorem execute_cti_run (w : W32) (i : Instruction) (s : State) (op : Pseudo Unit)
    (hpb : s.pendingBranch = none) (h1 : InCop1Space w = false) (h0 : InCop0Space w = false)
    (hop : Operation i = some op) :
    Execute modelCtx w i (abs s) =
      match op.run modelCtx { arch := abs s } with
      | (.ok (), f) => some (Complete (abs s) f)
      | (.signal e, f) => some (GeneralExceptionProcessing modelCtx.oracle e f.arch) := by
  have hb : (abs s).BranchDelay.isSome = false := by simp [abs, hpb]
  simp only [Execute, Execute.runOperation, hb, Bool.and_false, Bool.false_eq_true, ite_false, h1, h0, hop,
    Bool.false_and]
  rfl

end Refine
