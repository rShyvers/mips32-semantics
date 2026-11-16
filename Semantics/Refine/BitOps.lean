import Semantics.Refine.BridgeIntAlu
import Semantics.Refine.IntArith

/-!
# Refine.BitOps — count leading bits, sign extension, byte swap against `execInstr`

`Refine.<ctor>_refines` for `CLO`, `CLZ`, `SEB`, `SEH`, `WSBH`, `EXT`, `INS`. The manual's `for i in 31 .. 0 …
break` loop of `CLO`/`CLZ` (`manualCount`) is the model's `countLeadingOnes`/`countLeadingZeros`
(`clo_eq`, `clz_eq`).

`EXT` and `INS`: both sides read the 5-bit fields of the diagram (MD00086 Vol II-A Rev 6.06,
EXT p.183, INS p.192) and raise Reserved Instruction in the UNPREDICTABLE ranges; no side condition.
-/

namespace Refine

open Manual

/-- `CLO`'s Operation with the loop named `manualCount`. -/
theorem clo_run (rs rd : W32) (c : Ctx) (f : Frame) :
    (Ops.CLO rs rd).run c f =
      (setGPR (reg rd) (BitVec.ofNat 32 (manualCount (readGPR f.arch (reg rs)) false))).run c f := rfl

/-- `CLZ`'s Operation with the loop named `manualCount`. -/
theorem clz_run (rs rd : W32) (c : Ctx) (f : Frame) :
    (Ops.CLZ rs rd).run c f =
      (setGPR (reg rd) (BitVec.ofNat 32 (manualCount (readGPR f.arch (reg rs)) true))).run c f := rfl

/-- **CLO refines.** -/
theorem clo_refines (s : State) (hg : Good s) (rs rd w : W32)
    (hw : enc (.clo rs rd) = some w) :
    Execute modelCtx w (.clo rs rd) (abs s) = some (abs (execInstr s (.clo rs rd))) := by
  obtain rfl : rFormat 0#32 rs 0#32 rd 1#32 0x11#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.CLO rs rd) rd
    (BitVec.ofNat 32 (countLeadingOnes (readReg s (regIdx rs))))
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  rw [clo_run]
  alu_run [readGPR_abs s hg.2.2, clo_eq]

/-- **CLZ refines.** -/
theorem clz_refines (s : State) (hg : Good s) (rs rd w : W32)
    (hw : enc (.clz rs rd) = some w) :
    Execute modelCtx w (.clz rs rd) (abs s) = some (abs (execInstr s (.clz rs rd))) := by
  obtain rfl : rFormat 0#32 rs 0#32 rd 1#32 0x10#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.CLZ rs rd) rd
    (BitVec.ofNat 32 (countLeadingZeros (readReg s (regIdx rs))))
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  rw [clz_run]
  alu_run [readGPR_abs s hg.2.2, clz_eq]

/-- **SEB refines.** -/
theorem seb_refines (s : State) (hg : Good s) (rd rt w : W32)
    (hw : enc (.seb rd rt) = some w) :
    Execute modelCtx w (.seb rd rt) (abs s) = some (abs (execInstr s (.seb rd rt))) := by
  obtain rfl : rFormat 0x1F#32 0#32 rt rd 0x10#32 0x20#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SEB rd rt) rd (signExtLowByte (readReg s (regIdx rt)))
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.SEB, readGPR_abs s hg.2.2]
  rfl

/-- **SEH refines.** -/
theorem seh_refines (s : State) (hg : Good s) (rd rt w : W32)
    (hw : enc (.seh rd rt) = some w) :
    Execute modelCtx w (.seh rd rt) (abs s) = some (abs (execInstr s (.seh rd rt))) := by
  obtain rfl : rFormat 0x1F#32 0#32 rt rd 0x18#32 0x20#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.SEH rd rt) rd (signExt16 (readReg s (regIdx rt)))
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.SEH, readGPR_abs s hg.2.2]
  rfl

/-- **WSBH refines.** -/
theorem wsbh_refines (s : State) (hg : Good s) (rd rt w : W32)
    (hw : enc (.wsbh rd rt) = some w) :
    Execute modelCtx w (.wsbh rd rt) (abs s) = some (abs (execInstr s (.wsbh rd rt))) := by
  obtain rfl : rFormat 0x1F#32 0#32 rt rd 0x02#32 0x20#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.WSBH rd rt) rd
    ((((readReg s (regIdx rt) >>> 16) &&& 0xff#32) <<< 24) |||
      (((readReg s (regIdx rt) >>> 24) &&& 0xff#32) <<< 16) |||
      ((readReg s (regIdx rt) &&& 0xff#32) <<< 8) ||| ((readReg s (regIdx rt) >>> 8) &&& 0xff#32))
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.WSBH, readGPR_abs s hg.2.2, wsbh_eq]

/-- The model's `lowBitsMask n` is `2^n - 1` for `n ≤ 32`. -/
theorem lowBitsMask_toNat (n : Nat) (hn : n ≤ 32) : (lowBitsMask n).toNat = 2 ^ n - 1 := by
  unfold lowBitsMask
  rcases Nat.lt_or_eq_of_le hn with h | rfl
  · have h1 : (1#32 <<< n).toNat = 2 ^ n := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.one_mod_two_pow (by omega), Nat.one_mul]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) h)
    have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hp2 : 2 ^ n < 2 ^ 32 := Nat.pow_lt_pow_right (by omega) h
    rw [BitVec.toNat_sub, h1]
    simp only [BitVec.toNat_ofNat]
    omega
  · rfl

/-- Bit `i` of `lowBitsMask n` (`n ≤ 32`) is set iff `i < n`. -/
theorem lowBitsMask_getLsbD (n i : Nat) (hn : n ≤ 32) : (lowBitsMask n).getLsbD i = decide (i < n) := by
  have : lowBitsMask n = BitVec.ofNat 32 (2 ^ n - 1) := by
    apply BitVec.eq_of_toNat_eq; rw [lowBitsMask_toNat n hn, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := Nat.pow_le_pow_right (show 0 < 2 by omega) hn; omega)).symm
  rw [this, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases h : i < 32 <;> by_cases h' : i < n <;> simp [h, h'] <;> omega

/-- `EXT`'s `0^(32-(msbd+1)) || GPR[rs]msbd+lsb..lsb` is the model's shift-and-mask. -/
theorem ext_eq (x : W32) (lsb msbd : Nat) (hm : msbd < 32) :
    (0#(32 - (msbd + 1)) ++ low (x >>> lsb) (msbd + 1)).setWidth 32 = (x >>> lsb) &&& lowBitsMask (msbd + 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [low, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_and,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_zero, lowBitsMask_getLsbD _ _ (show msbd + 1 ≤ 32 by omega)]
  by_cases h : i < msbd + 1 <;> simp [h, hi]

/-- `INS`'s `GPR[rt]31..msb+1 || GPR[rs]msb-lsb..0 || GPR[rt]lsb-1..0` (for `lsb ≤ msb < 32`) is the
model's clear-and-or. -/
theorem ins_eq (x t : W32) (lsb msb : Nat) (hl : lsb ≤ msb) (hm : msb < 32) :
    (low (t >>> ((msb : Int) + 1).toNat) (31 - (msb : Int)).toNat ++ low x ((msb : Int) - (lsb : Int) + 1).toNat ++
        low t lsb).setWidth 32 =
      (t &&& ~~~(lowBitsMask (msb + 1 - lsb) <<< lsb)) ||| ((x &&& lowBitsMask (msb + 1 - lsb)) <<< lsb) := by
  have e1 : ((msb : Int) + 1).toNat = msb + 1 := by omega
  have e2 : (31 - (msb : Int)).toNat = 31 - msb := by omega
  have e3 : ((msb : Int) - (lsb : Int) + 1).toNat = msb + 1 - lsb := by omega
  rw [e1, e2, e3]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [low, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_extractLsb', lowBitsMask_getLsbD _ _ (show msb + 1 - lsb ≤ 32 by omega)]
  by_cases h1 : i < lsb
  · simp [h1, hi]
  · by_cases h2 : i < msb + 1
    · have h3 : i - lsb < msb + 1 - lsb := by omega
      simp [h1, h3]
    · have h3 : ¬ i - lsb < msb + 1 - lsb := by omega
      have h4 : i - lsb - (msb + 1 - lsb) < 31 - msb := by omega
      have h5 : msb + 1 + (i - lsb - (msb + 1 - lsb)) = i := by omega
      simp [h1, h3, h4, h5, hi]

/-- The model's `v &&& 31` is the 5-bit field `low v 5`. -/
theorem and31 (v : W32) : (v &&& 31#32).toNat = (low v 5).toNat := by
  rw [low5, BitVec.toNat_and, show (31#32).toNat = 2 ^ 5 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- **EXT refines**, for every constructor value: both sides read the diagram's 5-bit `msbd`/`lsb`
fields, and the UNPREDICTABLE range `lsb + msbd > 31` is Reserved Instruction on both sides
(`Oracle.extOutOfRange` of `modelOracle`). -/
theorem ext_refines (s : State) (hg : Good s) (rt rs pos size w : W32)
    (hw : enc (.ext rt rs pos size) = some w) :
    Execute modelCtx w (.ext rt rs pos size) (abs s) = some (abs (execInstr s (.ext rt rs pos size))) := by
  obtain rfl : rFormat 0x1F#32 rs rt (size - 1#32) pos 0x00#32 = w := Option.some.inj hw
  have hex := execInstr_body s (.ext rt rs pos size) rfl rfl rfl
  simp only [execBody, execTables, List.findSome?, execIntArith, execShift, execBitOps, Option.getD,
    and31] at hex
  by_cases hr : (low pos 5).toNat + (low (size - 1#32) 5).toNat > 31
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hr)] at hex
    refine refine_exc s _ _ (Ops.EXT rt rs pos size) .ReservedInstruction excCodeRI (fun h => nomatch h)
      (by alu_space) (by alu_space) rfl ?_ rfl (by decide) hex
    simp only [Ops.EXT, Pseudo.run, bind, GPR, Pseudo.oracle, Pseudo.get, hr, ↓reduceIte]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hr)] at hex
    refine refine_gpr s hg _ _ (Ops.EXT rt rs pos size) rt _ (fun h => nomatch h)
      (by alu_space) (by alu_space) rfl ?_ hex
    alu_run [Ops.EXT, readGPR_abs s hg.2.2, hr, decide_false,
      ext_eq _ _ _ (low5_lt (size - 1#32))]

/-- **INS refines**, for every constructor value: the 5-bit `msb`/`lsb` fields, Reserved Instruction for
`lsb > msb` on both sides (`Oracle.insLsbAboveMsb` of `modelOracle`). -/
theorem ins_refines (s : State) (hg : Good s) (rt rs pos size w : W32)
    (hw : enc (.ins rt rs pos size) = some w) :
    Execute modelCtx w (.ins rt rs pos size) (abs s) = some (abs (execInstr s (.ins rt rs pos size))) := by
  obtain rfl : rFormat 0x1F#32 rs rt (pos + size - 1#32) pos 0x04#32 = w := Option.some.inj hw
  have hex := execInstr_body s (.ins rt rs pos size) rfl rfl rfl
  simp only [execBody, execTables, List.findSome?, execIntArith, execShift, execBitOps, Option.getD,
    and31] at hex
  by_cases hr : (low pos 5).toNat > (low (pos + size - 1#32) 5).toNat
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hr)] at hex
    have hr' : ((low pos 5).toNat : Int) > ((low (pos + size - 1#32) 5).toNat : Int) := by omega
    refine refine_exc s _ _ (Ops.INS rt rs pos size) .ReservedInstruction excCodeRI (fun h => nomatch h)
      (by alu_space) (by alu_space) rfl ?_ rfl (by decide) hex
    simp only [Ops.INS, Pseudo.run, bind, GPR, Pseudo.oracle, Pseudo.get, hr', ↓reduceIte]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hr)] at hex
    have hr' : ¬ ((low pos 5).toNat : Int) > ((low (pos + size - 1#32) 5).toNat : Int) := by omega
    refine refine_gpr s hg _ _ (Ops.INS rt rs pos size) rt _ (fun h => nomatch h)
      (by alu_space) (by alu_space) rfl ?_ hex
    alu_run [Ops.INS, readGPR_abs s hg.2.2, hr', decide_false,
      ins_eq (readReg s (regIdx rs)) (readReg s (regIdx rt)) (low pos 5).toNat
        (low (pos + size - 1#32) 5).toNat (by omega) (low5_lt _)]

/-! ## Release 6: ALIGN, BITSWAP -/

/-- **ALIGN refines** (MD00086 Vol II-A Rev 6.06, ALIGN, p.39): both sides shift by the 2-bit `bp`. -/
theorem align_refines (s : State) (hg : Good s) (rs rt rd bp w : W32)
    (hw : enc (.align rs rt rd bp) = some w) :
    Execute modelCtx w (.align rs rt rd bp) (abs s) = some (abs (execInstr s (.align rs rt rd bp))) := by
  obtain rfl : sa2Format 0x1F#32 rs rt rd 2#32 bp 0x20#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.ALIGN rs rt rd bp) rd
    ((readReg s (regIdx rt) <<< (8 * (bp &&& 3#32).toNat)) |||
      (readReg s (regIdx rs) >>> (8 * (4 - (bp &&& 3#32).toNat))))
    (fun h => nomatch h) ?_ ?_ rfl ?_ (execInstr_body s _ rfl rfl rfl)
  · rw [InCop1Space, opcode_sa2Format]; rfl
  · rw [InCop0Space, opcode_sa2Format, funct_sa2Format]; rfl
  · alu_run [Ops.ALIGN, readGPR_abs s hg.2.2, low2_and3]

/-- `BITSWAP`'s `reverse_bits_in_byte` of each byte (p.92) is the model's `bitswapWord`. -/
theorem bitswap_eq (x : W32) :
    (Ops.reverse_bits_in_byte (x.extractLsb' 24 8) ++ Ops.reverse_bits_in_byte (x.extractLsb' 16 8) ++
      Ops.reverse_bits_in_byte (x.extractLsb' 8 8) ++ Ops.reverse_bits_in_byte (x.extractLsb' 0 8)) =
      bitswapWord x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Ops.reverse_bits_in_byte, bitswapWord, bit, BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofBool]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- **BITSWAP refines.** -/
theorem bitswap_refines (s : State) (hg : Good s) (rd rt w : W32)
    (hw : enc (.bitswap rd rt) = some w) :
    Execute modelCtx w (.bitswap rd rt) (abs s) = some (abs (execInstr s (.bitswap rd rt))) := by
  obtain rfl : rFormat 0x1F#32 0#32 rt rd 0#32 0x20#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.BITSWAP rd rt) rd (bitswapWord (readReg s (regIdx rt)))
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.BITSWAP, readGPR_abs s hg.2.2, bitswap_eq]

end Refine
