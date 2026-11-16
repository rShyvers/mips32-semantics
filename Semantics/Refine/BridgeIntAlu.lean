import Semantics.Refine.Bridge

/-!
# Refine.BridgeIntAlu — the shared steps of the integer ALU refinement proofs

The integer ALU instructions (`Refine/{IntArith,Shift,BitOps,Immediate}.lean`) are neither
CTIs nor in a coprocessor encoding space, and their model arm is `execBody`. Each refinement theorem is
then three facts: the encoding space of the word, the run of the Operation on `abs s` (a register
or no write, or a signalled exception), and the value lemma tying the manual's formula to
the model's. This file proves the first two once (`refine_ok`, `refine_gpr`, `refine_exc`) and the
value lemmas shared by several families.
-/

namespace Refine

open Manual

/-! ## Execute for an instruction that is not a CTI -/

/-- `Execute` runs the Operation of an instruction that is not a CTI, outside the unusable
coprocessors' spaces. -/
theorem execute_plain (w : W32) (i : Instruction) (a : Arch) (op : Pseudo Unit)
    (hcti : IsCTI i = true → False) (h1 : InCop1Space w = false)
    (h0 : InCop0Space w = false) (hop : Operation i = some op) :
    Execute modelCtx w i a =
      match op.run modelCtx { arch := a } with
      | (.ok (), f) => some (Complete a f)
      | (.signal e, f) => some (GeneralExceptionProcessing modelCtx.impl modelCtx.oracle e f.arch) := by
  have hr : Execute.runOperation modelCtx w i a =
      match op.run modelCtx { arch := a } with
      | (.ok (), f) => some (Complete a f)
      | (.signal e, f) => some (GeneralExceptionProcessing modelCtx.impl modelCtx.oracle e f.arch) := by
    simp only [Execute.runOperation, h1, h0, hop, Bool.false_and, Bool.false_eq_true, ite_false]
    rfl
  have hc : IsCTI i = false := by cases h : IsCTI i; rfl; exact (hcti h).elim
  unfold Execute
  simp only [hc, Bool.false_and, Bool.false_eq_true, ite_false]
  exact hr

/-- The model's arm of an instruction that is no CTI and needs no coprocessor is `execBody`. -/
theorem execInstr_body (s : State) (i : Instruction) (h1 : isBranchLike i = false)
    (h2 : usesCop1 i = false) (h3 : usesCop0 i = false) : execInstr s i = execBody s i := by
  unfold execInstr; rw [h1, h2, h3]; rfl

/-! ## The three shapes of an ALU instruction -/

/-- **An Operation that completes normally** with the architectural state `abs t`, against a model
arm `mkNext s t` whose effect `t` keeps `pc` and `pendingBranch`. -/
theorem refine_ok (s t : State) (w : W32) (i : Instruction) (op : Pseudo Unit)
    (hcti : IsCTI i = true → False) (h1 : InCop1Space w = false)
    (h0 : InCop0Space w = false) (hop : Operation i = some op)
    (hrun : op.run modelCtx { arch := abs s } = (.ok (), { arch := abs t }))
    (hex : execInstr s i = mkNext s t) (hpc : t.pc = s.pc)
    (hpb : t.pendingBranch = s.pendingBranch) :
    Execute modelCtx w i (abs s) = some (abs (execInstr s i)) := by
  rw [execute_plain w i _ op hcti h1 h0 hop, hrun, hex]
  show some (Complete (abs s) { arch := abs t }) = _
  rw [complete_plain, mkNext, abs_advance _ _ hpb, hpc]
  rfl

/-- **An Operation that writes one GPR** (`GPR[r] ← v`), against the model's
`mkNext s (writeReg s (regIdx r) v)`. -/
theorem refine_gpr (s : State) (hg : Good s) (w : W32) (i : Instruction) (op : Pseudo Unit)
    (r v : W32) (hcti : IsCTI i = true → False) (h1 : InCop1Space w = false)
    (h0 : InCop0Space w = false) (hop : Operation i = some op)
    (hrun : op.run modelCtx { arch := abs s } = (.ok (), { arch := writeGPR (abs s) (reg r) v }))
    (hex : execInstr s i = mkNext s (writeReg s (regIdx r) v)) :
    Execute modelCtx w i (abs s) = some (abs (execInstr s i)) := by
  refine refine_ok s (writeReg s (regIdx r) v) w i op hcti h1 h0 hop ?_ hex
    (by unfold writeReg; split <;> rfl) (by unfold writeReg; split <;> rfl)
  rw [hrun, abs_writeReg _ _ _ hg.1, regIdx_eq_reg]

/-- **An Operation that signals an exception** that saves nothing more and has no `CE` (Integer
Overflow here), from the state it started with, against the model's `takeException`. -/
theorem refine_exc (s : State) (w : W32) (i : Instruction) (op : Pseudo Unit) (e : Exception)
    (code : W32) (hcti : IsCTI i = true → False) (h1 : InCop1Space w = false)
    (h0 : InCop0Space w = false) (hop : Operation i = some op)
    (hrun : op.run modelCtx { arch := abs s } = (.signal e, { arch := abs s }))
    (hs : Simple e = true) (hc : code = (ExcCode e).setWidth 32)
    (hex : execInstr s i = takeException s code) :
    Execute modelCtx w i (abs s) = some (abs (execInstr s i)) := by
  rw [execute_plain w i _ op hcti h1 h0 hop, hrun, hex]
  exact congrArg some (gep_take s e hs code hc)

/-! ## Encoding spaces -/

theorem inCop1_rFormat (op rs rt rd sa fn : W32) :
    InCop1Space (rFormat op rs rt rd sa fn) =
      ((op &&& 0x3F#32) == 0x11#32 || (op &&& 0x3F#32) == 0x31#32 ||
        (op &&& 0x3F#32) == 0x39#32 || (op &&& 0x3F#32) == 0x35#32 || (op &&& 0x3F#32) == 0x3D#32) := by
  simp only [InCop1Space, opcode_rFormat]

theorem inCop0_rFormat (op rs rt rd sa fn : W32) :
    InCop0Space (rFormat op rs rt rd sa fn) =
      ((op &&& 0x3F#32) == 0x10#32 || ((op &&& 0x3F#32) == 0x1F#32 && (fn &&& 0x3F#32) == 0x25#32)) := by
  simp only [InCop0Space, opcode_rFormat, funct_rFormat]

/-- `iFormat` ignores the function field only through its immediate; the low six bits of the
word are the immediate's. -/
theorem iFormat_funct (op rs rt imm : W32) :
    iFormat op rs rt imm &&& 0x3F#32 = imm &&& 0x3F#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [iFormat, fld, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

theorem inCop1_iFormat (op rs rt imm : W32) :
    InCop1Space (iFormat op rs rt imm) =
      ((op &&& 0x3F#32) == 0x11#32 || (op &&& 0x3F#32) == 0x31#32 ||
        (op &&& 0x3F#32) == 0x39#32 || (op &&& 0x3F#32) == 0x35#32 || (op &&& 0x3F#32) == 0x3D#32) := by
  simp only [InCop1Space, opcode_iFormat]

theorem inCop0_iFormat (op rs rt imm : W32) :
    InCop0Space (iFormat op rs rt imm) =
      ((op &&& 0x3F#32) == 0x10#32 || ((op &&& 0x3F#32) == 0x1F#32 && (imm &&& 0x3F#32) == 0x25#32)) := by
  simp only [InCop0Space, opcode_iFormat, iFormat_funct]

/-- The encoding-space side conditions of an R-format or I-format ALU word, closed by evaluation of
the constant opcode and function fields. -/
macro "alu_space" : tactic =>
  `(tactic| first
    | (rw [inCop1_rFormat]; rfl)
    | (rw [inCop0_rFormat]; rfl)
    | (rw [inCop1_iFormat]; rfl)
    | (rw [inCop0_iFormat]; rfl))

/-- Run an ALU Operation on `abs s`: unfold the pseudocode primitives and read the GPRs through
`abs` (the caller adds the Operation, `readGPR_abs s h0` and the value lemmas). -/
syntax "alu_run" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| alu_run [$ls,*]) => `(tactic| simp only [Pseudo.run, bind, GPR, setGPR, Pseudo.modify, Pseudo.oracle, Pseudo.get, ← regIdx_eq_reg, ↓reduceIte, Bool.false_eq_true,
      $ls,*])

/-! ## Value lemmas: integer arithmetic -/

theorem sub33_low (x y : W32) :
    low ((BitVec.ofBool (bit x 31) ++ x) - (BitVec.ofBool (bit y 31) ++ y)) 32 = x - y := by
  apply BitVec.eq_of_toNat_eq
  simp only [low, BitVec.extractLsb'_toNat, BitVec.toNat_sub, toNat_sx33]
  have hx := x.isLt; have hy := y.isLt
  cases bit x 31 <;> cases bit y 31 <;> simp <;> omega

theorem sub_ovf (x y : W32) :
    (bit ((BitVec.ofBool (bit x 31) ++ x) - (BitVec.ofBool (bit y 31) ++ y)) 32 !=
        bit ((BitVec.ofBool (bit x 31) ++ x) - (BitVec.ofBool (bit y 31) ++ y)) 31)
      = subOverflows (asSigned x) (asSigned y) (asSigned (x - y)) := by
  have hx := x.isLt; have hy := y.isLt
  have e1 : ∀ (t : BitVec 33) k, bit t k = decide (t.toNat / 2^k % 2 = 1) := by
    intro t k; simp [bit, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  rw [e1, e1]
  simp only [BitVec.toNat_sub, toNat_sx33]
  simp only [bit31_iff]
  simp only [subOverflows, asSigned, BitVec.toInt_eq_toNat_cond, BitVec.toNat_sub]
  by_cases h1 : 2^31 ≤ x.toNat <;> by_cases h2 : 2^31 ≤ y.toNat <;>
    by_cases h3 : 2 * ((4294967296 - y.toNat + x.toNat) % 4294967296) < 4294967296 <;>
    (rw [Bool.eq_iff_iff]; simp [h1, h2, h3]; omega)

theorem add_ovf_bne (x y : W32) :
    (bit ((BitVec.ofBool (bit x 31) ++ x) + (BitVec.ofBool (bit y 31) ++ y)) 32 !=
        bit ((BitVec.ofBool (bit x 31) ++ x) + (BitVec.ofBool (bit y 31) ++ y)) 31)
      = addOverflows (asSigned x) (asSigned y) (asSigned (x + y)) := by
  rw [← add_ovf]; cases bit _ 32 <;> cases bit _ 31 <;> rfl

theorem one_w : (0#31 ++ 1#1).setWidth 32 = 1#32 := rfl

theorem slt_w (x y : W32) : x.slt y = decide (asSigned x < asSigned y) := rfl

theorem ult_w (x y : W32) : (0#1 ++ x).ult (0#1 ++ y) = decide (x.toNat < y.toNat) := by
  rw [BitVec.ult_eq_decide]
  simp only [BitVec.toNat_append, BitVec.toNat_zero, Nat.zero_shiftLeft, Nat.zero_or]

theorem low5 (v : W32) : (low v 5).toNat = v.toNat % 32 := by
  simp [low, BitVec.extractLsb'_toNat]

theorem low5_lt (v : W32) : (low v 5).toNat < 32 := (low v 5).isLt

theorem sll_eq (x : W32) (n : Nat) (hn : n < 32) : (low x (32 - n) ++ 0#n).setWidth 32 = x <<< n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [low, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_zero]
  by_cases h : i < n <;> simp [h, hi] <;> omega

theorem srl_eq (x : W32) (n : Nat) (hn : n < 32) : (0#n ++ bits x 31 n).setWidth 32 = x >>> n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bits, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_zero]
  by_cases h : i < 31 + 1 - n <;> simp [h, hi]
  rw [BitVec.getLsbD_of_ge]; omega

theorem sra_eq (x : W32) (n : Nat) (hn : n < 32) :
    (BitVec.fill n (bit x 31) ++ bits x 31 n).setWidth 32 = x.sshiftRight n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bits, bit, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_sshiftRight,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_fill, BitVec.msb_eq_getLsbD_last]
  by_cases h : i < 31 + 1 - n
  · simp [h, hi, show n + i < 32 by omega]
  · simp [h, hi, show ¬ n + i < 32 by omega, show i - (32 - n) < n by omega]

theorem rotr_eq (x : W32) (n : Nat) (hn : n < 32) :
    (low x n ++ bits x 31 n).setWidth 32 = x.rotateRight n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bits, low, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_extractLsb']
  by_cases h : i < 31 + 1 - n <;> simp [h, hi, Nat.mod_eq_of_lt hn] <;> omega

/-! ## Value lemmas: shifts, multiply/divide -/

theorem mult_eq (x y : W32) :
    x.signExtend 64 * y.signExtend 64 = BitVec.ofInt 64 (asSigned x * asSigned y) := by
  simp only [BitVec.signExtend, asSigned, BitVec.ofInt_mul]

theorem multu_eq (x y : W32) :
    x.zeroExtend 64 * y.zeroExtend 64 = BitVec.ofNat 64 (x.toNat * y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.toNat_mul, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2^64), Nat.mod_eq_of_lt (by omega : y.toNat < 2^64)]

theorem setWidth_sx64 (x : W32) : (x.signExtend 64).setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_signExtend, hi]; omega
theorem mul_low (x y : W32) : low (x.signExtend 64 * y.signExtend 64) 32 = x * y := by
  simp only [low]
  rw [← BitVec.setWidth_eq_extractLsb' (by omega), BitVec.setWidth_mul _ _ (by omega), setWidth_sx64,
    setWidth_sx64]
theorem asSigned_eq_zero (y : W32) : (asSigned y == 0) = (y == 0#32) := by
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, asSigned]
  constructor
  · intro h; exact BitVec.toInt_inj.mp (by rw [h]; rfl)
  · intro h; subst h; rfl
theorem toNat_eq_zero' (y : W32) : (y.toNat == 0) = (y == 0#32) := by
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
  · intro h; subst h; rfl

/-! ## Value lemmas: bit operations -/

/-- The leading-bit count, as the manual's loop computes it. -/
def manualCount (x : W32) (b : Bool) : Nat :=
  match (List.range 32).reverse.find? (fun i => bit x i == b) with
  | some i => 31 - i
  | none => 32

theorem count_eq (x w : W32) (b : Bool) (hw : ∀ i < 32, w.getLsbD i = (bit x i == b)) :
    manualCount x b = countLeadingZeros w := by
  have key : ∀ k, k ≤ 32 →
      (match (List.range k).reverse.find? (fun i => bit x i == b) with
        | some i => 31 - i
        | none => 32) = countLeadingZerosFrom w k (32 - k) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.find?_cons]
      have hm : w.getMsbD (32 - (k + 1)) = (bit x k == b) := by
        rw [BitVec.getMsbD_eq_getLsbD, ← hw k (by omega)]
        simp only [show 32 - (k + 1) < 32 by omega, decide_true, Bool.true_and]
        congr 1; omega
      simp only [countLeadingZerosFrom, hm]
      cases bit x k == b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ih (by omega)]; congr 1; omega
      · simp only [↓reduceIte]; omega
  exact key 32 (by omega)

theorem clz_eq (x : W32) : manualCount x true = countLeadingZeros x :=
  count_eq x x true (fun i _ => by simp [bit])

theorem clo_eq (x : W32) : manualCount x false = countLeadingOnes x :=
  count_eq x (~~~x) false (fun i hi => by simp [bit, hi])

theorem wsbh_eq (x : W32) :
    (bits x 23 16 ++ bits x 31 24 ++ bits x 7 0 ++ bits x 15 8).setWidth 32 =
      (((x >>> 16) &&& 0xff#32) <<< 24) ||| (((x >>> 24) &&& 0xff#32) <<< 16) |||
        ((x &&& 0xff#32) <<< 8) ||| ((x >>> 8) &&& 0xff#32) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bits, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

end Refine
