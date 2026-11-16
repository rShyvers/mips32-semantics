import Semantics.Refine.Bridge
import Semantics.Refine.BridgeIntAlu

/-!
# Refine.IntArith — the integer arithmetic Operations against `execInstr`

`Refine.<ctor>_refines`: executing the instruction in the spec (`Manual.Execute`, from the fetched
word `w` whose format diagram is the instruction's) is the model's `execInstr`, seen through `abs`.
Every proof goes through the shared steps of `Refine/BridgeIntAlu.lean` (`refine_gpr`, `refine_exc`,
`alu_run`).
-/

namespace Refine

open Manual

/-- **ADD refines.** -/
theorem add_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.add rs rt rd) = some w) :
    Execute modelCtx w (.add rs rt rd) (abs s) = some (abs (execInstr s (.add rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x20#32 = w := Option.some.inj hw
  have hov := add_ovf (readReg s (regIdx rs)) (readReg s (regIdx rt))
  cases h : addOverflows (asSigned (readReg s (regIdx rs))) (asSigned (readReg s (regIdx rt)))
      (asSigned (readReg s (regIdx rs) + readReg s (regIdx rt))) <;> rw [h] at hov
  · refine refine_gpr s hg _ _ (Ops.ADD rs rt rd) rd (readReg s (regIdx rs) + readReg s (regIdx rt))
      (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ ?_
    · alu_run [Ops.ADD, readGPR_abs s hg.2.2, of_decide_eq_false hov, add33_low]
    · rw [execInstr_body s _ rfl rfl rfl]; exec_unfold; simp only [h]; rfl
  · refine refine_exc s _ _ (Ops.ADD rs rt rd) .IntegerOverflow excCodeOv (fun h => nomatch h)
      (by alu_space) (by alu_space) rfl ?_ rfl rfl ?_
    · alu_run [Ops.ADD, readGPR_abs s hg.2.2, ne_eq, of_decide_eq_true hov, not_false_eq_true]; rfl
    · rw [execInstr_body s _ rfl rfl rfl]; exec_unfold; simp only [h]; rfl

/-- **ADDU refines.** -/
theorem addu_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.addu rs rt rd) = some w) :
    Execute modelCtx w (.addu rs rt rd) (abs s) = some (abs (execInstr s (.addu rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x21#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.ADDU rs rt rd) rd
    (readReg s (regIdx rs) + readReg s (regIdx rt)) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.ADDU, readGPR_abs s hg.2.2]

/-- **SUB refines.** -/
theorem sub_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.sub rs rt rd) = some w) :
    Execute modelCtx w (.sub rs rt rd) (abs s) = some (abs (execInstr s (.sub rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x22#32 = w := Option.some.inj hw
  have hov := sub_ovf (readReg s (regIdx rs)) (readReg s (regIdx rt))
  cases h : subOverflows (asSigned (readReg s (regIdx rs))) (asSigned (readReg s (regIdx rt)))
      (asSigned (readReg s (regIdx rs) - readReg s (regIdx rt))) <;> rw [h] at hov
  · refine refine_gpr s hg _ _ (Ops.SUB rs rt rd) rd (readReg s (regIdx rs) - readReg s (regIdx rt))
      (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ ?_
    · alu_run [Ops.SUB, readGPR_abs s hg.2.2, hov, sub33_low]
    · rw [execInstr_body s _ rfl rfl rfl]; exec_unfold; simp only [h]; rfl
  · refine refine_exc s _ _ (Ops.SUB rs rt rd) .IntegerOverflow excCodeOv (fun h => nomatch h)
      (by alu_space) (by alu_space) rfl ?_ rfl rfl ?_
    · alu_run [Ops.SUB, readGPR_abs s hg.2.2, hov]; rfl
    · rw [execInstr_body s _ rfl rfl rfl]; exec_unfold; simp only [h]; rfl

/-- **SUBU refines.** -/
theorem subu_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.subu rs rt rd) = some w) :
    Execute modelCtx w (.subu rs rt rd) (abs s) = some (abs (execInstr s (.subu rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x23#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SUBU rs rt rd) rd
    (readReg s (regIdx rs) - readReg s (regIdx rt)) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.SUBU, readGPR_abs s hg.2.2]

/-- **AND refines.** -/
theorem and_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.and rs rt rd) = some w) :
    Execute modelCtx w (.and rs rt rd) (abs s) = some (abs (execInstr s (.and rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x24#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.AND rs rt rd) rd
    (readReg s (regIdx rs) &&& readReg s (regIdx rt)) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.AND, readGPR_abs s hg.2.2]

/-- **OR refines.** -/
theorem or_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.or rs rt rd) = some w) :
    Execute modelCtx w (.or rs rt rd) (abs s) = some (abs (execInstr s (.or rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x25#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.OR rs rt rd) rd
    (readReg s (regIdx rs) ||| readReg s (regIdx rt)) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.OR, readGPR_abs s hg.2.2]

/-- **XOR refines.** -/
theorem xor_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.xor rs rt rd) = some w) :
    Execute modelCtx w (.xor rs rt rd) (abs s) = some (abs (execInstr s (.xor rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x26#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.XOR rs rt rd) rd
    (readReg s (regIdx rs) ^^^ readReg s (regIdx rt)) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.XOR, readGPR_abs s hg.2.2]

/-- **NOR refines.** -/
theorem nor_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.nor rs rt rd) = some w) :
    Execute modelCtx w (.nor rs rt rd) (abs s) = some (abs (execInstr s (.nor rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x27#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.NOR rs rt rd) rd
    (~~~(readReg s (regIdx rs) ||| readReg s (regIdx rt))) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.NOR, readGPR_abs s hg.2.2]

/-- **SLT refines.** -/
theorem slt_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.slt rs rt rd) = some w) :
    Execute modelCtx w (.slt rs rt rd) (abs s) = some (abs (execInstr s (.slt rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x2A#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SLT rs rt rd) rd
    (if asSigned (readReg s (regIdx rs)) < asSigned (readReg s (regIdx rt)) then 1#32 else 0#32) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  by_cases hc : asSigned (readReg s (regIdx rs)) < asSigned (readReg s (regIdx rt)) <;>
    alu_run [Ops.SLT, readGPR_abs s hg.2.2, slt_w, one_w, hc, decide_true, decide_false] <;> rfl

/-- **SLTU refines.** -/
theorem sltu_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.sltu rs rt rd) = some w) :
    Execute modelCtx w (.sltu rs rt rd) (abs s) = some (abs (execInstr s (.sltu rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x2B#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SLTU rs rt rd) rd
    (if (readReg s (regIdx rs)).toNat < (readReg s (regIdx rt)).toNat then 1#32 else 0#32) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  by_cases hc : (readReg s (regIdx rs)).toNat < (readReg s (regIdx rt)).toNat <;>
    alu_run [Ops.SLTU, readGPR_abs s hg.2.2, ult_w, one_w, hc, decide_true, decide_false] <;> rfl

/-! ## Release 6: MUL/MUH/MULU/MUHU, DIV/MOD/DIVU/MODU, SELEQZ/SELNEZ, LSA

The value lemmas tie the manual's integer formulas (MD00086 Vol II-A Rev 6.06, p.301, p.169: the
product as a 64-bit string, truncated division) to the model's bit-vector operations. A zero divisor
is the oracle choice `Oracle.divByZero`, which `modelOracle` resolves as the model's `divOr` does. -/

theorem lo_word_mul (x y : W32) : Ops.lo_word (Ops.product64 (x.toInt * y.toInt)) = x * y := by
  have := mul_low x y
  rw [mult_eq] at this
  exact this

theorem hi_word_mul (x y : W32) : Ops.hi_word (Ops.product64 (x.toInt * y.toInt)) = mulHiS x y := by
  rw [mulHiS, mult_eq]; rfl

theorem lo_word_mulu (x y : W32) :
    Ops.lo_word (Ops.product64 ((x.toNat * y.toNat : Nat) : Int)) = x * y := by
  apply BitVec.eq_of_toNat_eq
  rw [Ops.product64, BitVec.ofInt_natCast]
  simp only [Ops.lo_word, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat,
    BitVec.toNat_mul]
  exact Nat.mod_mod_of_dvd _ (by decide)

theorem hi_word_mulu (x y : W32) :
    Ops.hi_word (Ops.product64 ((x.toNat * y.toNat : Nat) : Int)) = mulHiU x y := by
  rw [mulHiU, multu_eq, Ops.product64, BitVec.ofInt_natCast]; rfl

theorem sdiv_eq (x y : W32) : BitVec.ofInt 32 (x.toInt.tdiv y.toInt) = x.sdiv y := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt, BitVec.toInt_sdiv]

theorem srem_eq (x y : W32) : BitVec.ofInt 32 (x.toInt.tmod y.toInt) = x.srem y := by
  rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]

theorem udiv_eq (x y : W32) : BitVec.ofNat 32 (x.toNat / y.toNat) = x / y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_udiv]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)

theorem umod_eq (x y : W32) : BitVec.ofNat 32 (x.toNat % y.toNat) = x % y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_umod]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt)

theorem toInt_beq_zero (y : W32) : (y.toInt == 0) = (y == 0#32) := asSigned_eq_zero y

/-- `(low v 2).toNat` is the model's `(v &&& 3).toNat`. -/
theorem low2_and3 (v : W32) : (low v 2).toNat = (v &&& 3#32).toNat := by
  simp only [low, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_and,
    show (3#32).toNat = 2 ^ 2 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The opcode of an `sa2Format` word (LSA, ALIGN). -/
theorem opcode_sa2Format (op rs rt rd sub x fn : W32) :
    opcode (sa2Format op rs rt rd sub x fn) = op &&& 0x3F#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [opcode, sa2Format, fld, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- The function field of an `sa2Format` word. -/
theorem funct_sa2Format (op rs rt rd sub x fn : W32) :
    sa2Format op rs rt rd sub x fn &&& 0x3F#32 = fn &&& 0x3F#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [sa2Format, fld, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- **MUL refines.** -/
theorem mul_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.mul rs rt rd) = some w) :
    Execute modelCtx w (.mul rs rt rd) (abs s) = some (abs (execInstr s (.mul rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 2#32 0x18#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.MUL rs rt rd) rd
    (readReg s (regIdx rs) * readReg s (regIdx rt)) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.MUL, readGPR_abs s hg.2.2, lo_word_mul]

/-- **MUH refines.** -/
theorem muh_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.muh rs rt rd) = some w) :
    Execute modelCtx w (.muh rs rt rd) (abs s) = some (abs (execInstr s (.muh rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 3#32 0x18#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.MUH rs rt rd) rd
    (mulHiS (readReg s (regIdx rs)) (readReg s (regIdx rt))) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.MUH, readGPR_abs s hg.2.2, hi_word_mul]

/-- **MULU refines.** -/
theorem mulu_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.mulu rs rt rd) = some w) :
    Execute modelCtx w (.mulu rs rt rd) (abs s) = some (abs (execInstr s (.mulu rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 2#32 0x19#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.MULU rs rt rd) rd
    (readReg s (regIdx rs) * readReg s (regIdx rt)) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.MULU, readGPR_abs s hg.2.2, lo_word_mulu]

/-- **MUHU refines.** -/
theorem muhu_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.muhu rs rt rd) = some w) :
    Execute modelCtx w (.muhu rs rt rd) (abs s) = some (abs (execInstr s (.muhu rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 3#32 0x19#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.MUHU rs rt rd) rd
    (mulHiU (readReg s (regIdx rs)) (readReg s (regIdx rt))) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.MUHU, readGPR_abs s hg.2.2, hi_word_mulu]

/-- **DIV refines.** -/
theorem div_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.div rs rt rd) = some w) :
    Execute modelCtx w (.div rs rt rd) (abs s) = some (abs (execInstr s (.div rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 2#32 0x1A#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.DIV rs rt rd) rd
    (divOr BitVec.sdiv id (readReg s (regIdx rs)) (readReg s (regIdx rt))) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  by_cases hy : readReg s (regIdx rt) = 0#32
  · alu_run [Ops.DIV, Ops.divResult, readGPR_abs s hg.2.2, toInt_beq_zero, hy, divOr, beq_self_eq_true]
    rfl
  · alu_run [Ops.DIV, Ops.divResult, readGPR_abs s hg.2.2, toInt_beq_zero, hy, divOr, beq_iff_eq, sdiv_eq]

/-- **MOD refines.** -/
theorem mod_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.mod rs rt rd) = some w) :
    Execute modelCtx w (.mod rs rt rd) (abs s) = some (abs (execInstr s (.mod rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 3#32 0x1A#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.MOD rs rt rd) rd
    (divOr BitVec.srem (fun _ => 0#32) (readReg s (regIdx rs)) (readReg s (regIdx rt))) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  by_cases hy : readReg s (regIdx rt) = 0#32
  · alu_run [Ops.MOD, Ops.divResult, readGPR_abs s hg.2.2, toInt_beq_zero, hy, divOr, beq_self_eq_true]
    rfl
  · alu_run [Ops.MOD, Ops.divResult, readGPR_abs s hg.2.2, toInt_beq_zero, hy, divOr, beq_iff_eq, srem_eq]

/-- **DIVU refines.** -/
theorem divu_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.divu rs rt rd) = some w) :
    Execute modelCtx w (.divu rs rt rd) (abs s) = some (abs (execInstr s (.divu rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 2#32 0x1B#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.DIVU rs rt rd) rd
    (divOr (· / ·) id (readReg s (regIdx rs)) (readReg s (regIdx rt))) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  by_cases hy : readReg s (regIdx rt) = 0#32
  · alu_run [Ops.DIVU, Ops.divResult, readGPR_abs s hg.2.2, toNat_eq_zero', hy, divOr, beq_self_eq_true]
    rfl
  · alu_run [Ops.DIVU, Ops.divResult, readGPR_abs s hg.2.2, toNat_eq_zero', hy, divOr, beq_iff_eq, udiv_eq]

/-- **MODU refines.** -/
theorem modu_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.modu rs rt rd) = some w) :
    Execute modelCtx w (.modu rs rt rd) (abs s) = some (abs (execInstr s (.modu rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 3#32 0x1B#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.MODU rs rt rd) rd
    (divOr (· % ·) (fun _ => 0#32) (readReg s (regIdx rs)) (readReg s (regIdx rt))) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  by_cases hy : readReg s (regIdx rt) = 0#32
  · alu_run [Ops.MODU, Ops.divResult, readGPR_abs s hg.2.2, toNat_eq_zero', hy, divOr, beq_self_eq_true]
    rfl
  · alu_run [Ops.MODU, Ops.divResult, readGPR_abs s hg.2.2, toNat_eq_zero', hy, divOr, beq_iff_eq, umod_eq]

/-- **SELEQZ refines.** -/
theorem seleqz_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.seleqz rs rt rd) = some w) :
    Execute modelCtx w (.seleqz rs rt rd) (abs s) = some (abs (execInstr s (.seleqz rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x35#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SELEQZ rs rt rd) rd
    (if readReg s (regIdx rt) = 0#32 then readReg s (regIdx rs) else 0#32) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  by_cases hy : readReg s (regIdx rt) = 0#32 <;>
    alu_run [Ops.SELEQZ, readGPR_abs s hg.2.2, hy, beq_self_eq_true, beq_iff_eq, pure] <;> rfl

/-- **SELNEZ refines.** -/
theorem selnez_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.selnez rs rt rd) = some w) :
    Execute modelCtx w (.selnez rs rt rd) (abs s) = some (abs (execInstr s (.selnez rs rt rd))) := by
  obtain rfl : rFormat 0#32 rs rt rd 0#32 0x37#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SELNEZ rs rt rd) rd
    (if readReg s (regIdx rt) = 0#32 then 0#32 else readReg s (regIdx rs)) (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_
    (execInstr_body s _ rfl rfl rfl)
  by_cases hy : readReg s (regIdx rt) = 0#32 <;>
    alu_run [Ops.SELNEZ, readGPR_abs s hg.2.2, hy, bne_self_eq_false, bne_iff_ne, ne_eq,
      not_false_eq_true, not_true_eq_false, pure] <;> rfl

/-- **LSA refines.** -/
theorem lsa_refines (s : State) (hg : Good s) (rs rt rd sa w : W32)
    (hw : enc (.lsa rs rt rd sa) = some w) :
    Execute modelCtx w (.lsa rs rt rd sa) (abs s) = some (abs (execInstr s (.lsa rs rt rd sa))) := by
  obtain rfl : sa2Format 0#32 rs rt rd 0#32 sa 0x05#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.LSA rs rt rd sa) rd
    ((readReg s (regIdx rs) <<< ((sa &&& 3#32).toNat + 1)) + readReg s (regIdx rt))
    (fun h => nomatch h) ?_ ?_ rfl ?_ (execInstr_body s _ rfl rfl rfl)
  · rw [InCop1Space, opcode_sa2Format]; rfl
  · rw [InCop0Space, opcode_sa2Format]; rfl
  · alu_run [Ops.LSA, readGPR_abs s hg.2.2, low2_and3, sign_extend, BitVec.signExtend_eq]

end Refine
