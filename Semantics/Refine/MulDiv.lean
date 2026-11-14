import Semantics.Refine.BridgeIntAlu

/-!
# Refine.MulDiv — multiply, divide, multiply-accumulate and the `HI`/`LO` moves against `execInstr`
(sub-wave 7C S1)

`Refine.<ctor>_refines` for `MULT`, `MULTU`, `DIV`, `DIVU`, `MFHI`, `MFLO`, `MTHI`, `MTLO`, `MUL`,
`MADD`, `MADDU`, `MSUB`, `MSUBU`. The 64-bit products are the model's `BitVec.ofInt`/`BitVec.ofNat` of
the integer product (`mult_eq`, `multu_eq`); the 33-bit `div`/`mod` of the manual truncate toward zero
as the model's `Int.tdiv`/`Int.tmod` (`div_lo`, `div_hi`). A zero divisor and `MUL`'s `HI`/`LO` are
the oracle's choices `divByZero`, `divuByZero`, `mulHILO`, which `modelOracle` resolves as "unchanged",
the model's behaviour.
-/

namespace Refine

open Manual

/-- **MULT refines.** -/
theorem mult_refines (s : State) (hg : Good s) (rs rt w : W32)
    (hw : enc (.mult rs rt) = some w) :
    Execute modelCtx w (.mult rs rt) (abs s) = some (abs (execInstr s (.mult rs rt))) := by
  obtain rfl : rFormat 0#32 rs rt 0#32 0#32 0x18#32 = w := Option.some.inj hw
  refine refine_ok s ({ s with lo := (BitVec.ofInt 64 (asSigned (readReg s (regIdx rs)) * asSigned (readReg s (regIdx rt)))).extractLsb 31 0, hi := (BitVec.ofInt 64 (asSigned (readReg s (regIdx rs)) * asSigned (readReg s (regIdx rt)))).extractLsb 63 32 }) _ _ (Ops.MULT rs rt)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl) rfl rfl
  alu_run [Ops.MULT, readGPR_abs s hg.2.2, mult_eq]
  rfl

/-- **MULTU refines.** -/
theorem multu_refines (s : State) (hg : Good s) (rs rt w : W32)
    (hw : enc (.multu rs rt) = some w) :
    Execute modelCtx w (.multu rs rt) (abs s) = some (abs (execInstr s (.multu rs rt))) := by
  obtain rfl : rFormat 0#32 rs rt 0#32 0#32 0x19#32 = w := Option.some.inj hw
  refine refine_ok s ({ s with lo := (BitVec.ofNat 64 ((readReg s (regIdx rs)).toNat * (readReg s (regIdx rt)).toNat)).extractLsb 31 0, hi := (BitVec.ofNat 64 ((readReg s (regIdx rs)).toNat * (readReg s (regIdx rt)).toNat)).extractLsb 63 32 }) _ _ (Ops.MULTU rs rt)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl) rfl rfl
  alu_run [Ops.MULTU, readGPR_abs s hg.2.2, multu_eq]
  rfl

/-- **DIV refines** (a zero divisor: the oracle's `HI`/`LO`, which `modelOracle` leaves). -/
theorem div_refines (s : State) (hg : Good s) (rs rt w : W32)
    (hw : enc (.div rs rt) = some w) :
    Execute modelCtx w (.div rs rt) (abs s) = some (abs (execInstr s (.div rs rt))) := by
  obtain rfl : rFormat 0#32 rs rt 0#32 0#32 0x1A#32 = w := Option.some.inj hw
  cases h : readReg s (regIdx rt) == 0#32
  · refine refine_ok s { s with lo := ofInt32 ((asSigned (readReg s (regIdx rs))).tdiv (asSigned (readReg s (regIdx rt)))), hi := ofInt32 ((asSigned (readReg s (regIdx rs))).tmod (asSigned (readReg s (regIdx rt)))) } _ _ (Ops.DIV rs rt)
      (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ ?_ rfl rfl
    · alu_run [Ops.DIV, readGPR_abs s hg.2.2, h, div_lo, div_hi]
      rfl
    · rw [execInstr_body s _ rfl rfl rfl]; simp only [execBody, asSigned_eq_zero, h]; rfl
  · refine refine_ok s s _ _ (Ops.DIV rs rt)
      (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ ?_ rfl rfl
    · alu_run [Ops.DIV, readGPR_abs s hg.2.2, h]
      rfl
    · rw [execInstr_body s _ rfl rfl rfl]; simp only [execBody, asSigned_eq_zero, h]; rfl

/-- **DIVU refines** (a zero divisor: the oracle's `HI`/`LO`, which `modelOracle` leaves). -/
theorem divu_refines (s : State) (hg : Good s) (rs rt w : W32)
    (hw : enc (.divu rs rt) = some w) :
    Execute modelCtx w (.divu rs rt) (abs s) = some (abs (execInstr s (.divu rs rt))) := by
  obtain rfl : rFormat 0#32 rs rt 0#32 0#32 0x1B#32 = w := Option.some.inj hw
  cases h : readReg s (regIdx rt) == 0#32
  · refine refine_ok s { s with lo := BitVec.ofNat 32 ((readReg s (regIdx rs)).toNat / (readReg s (regIdx rt)).toNat), hi := BitVec.ofNat 32 ((readReg s (regIdx rs)).toNat % (readReg s (regIdx rt)).toNat) } _ _ (Ops.DIVU rs rt)
      (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ ?_ rfl rfl
    · alu_run [Ops.DIVU, readGPR_abs s hg.2.2, h, divu_lo, divu_hi]
      rfl
    · rw [execInstr_body s _ rfl rfl rfl]; simp only [execBody, toNat_eq_zero', h]; rfl
  · refine refine_ok s s _ _ (Ops.DIVU rs rt)
      (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ ?_ rfl rfl
    · alu_run [Ops.DIVU, readGPR_abs s hg.2.2, h]
      rfl
    · rw [execInstr_body s _ rfl rfl rfl]; simp only [execBody, toNat_eq_zero', h]; rfl

/-- **MFHI refines.** -/
theorem mfhi_refines (s : State) (hg : Good s) (rd w : W32)
    (hw : enc (.mfhi rd) = some w) :
    Execute modelCtx w (.mfhi rd) (abs s) = some (abs (execInstr s (.mfhi rd))) := by
  obtain rfl : rFormat 0#32 0#32 0#32 rd 0#32 0x10#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.MFHI rd) rd s.hi
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.MFHI]
  rfl

/-- **MFLO refines.** -/
theorem mflo_refines (s : State) (hg : Good s) (rd w : W32)
    (hw : enc (.mflo rd) = some w) :
    Execute modelCtx w (.mflo rd) (abs s) = some (abs (execInstr s (.mflo rd))) := by
  obtain rfl : rFormat 0#32 0#32 0#32 rd 0#32 0x12#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.MFLO rd) rd s.lo
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.MFLO]
  rfl

/-- **MTHI refines.** -/
theorem mthi_refines (s : State) (hg : Good s) (rs w : W32)
    (hw : enc (.mthi rs) = some w) :
    Execute modelCtx w (.mthi rs) (abs s) = some (abs (execInstr s (.mthi rs))) := by
  obtain rfl : rFormat 0#32 rs 0#32 0#32 0#32 0x11#32 = w := Option.some.inj hw
  refine refine_ok s ({ s with hi := readReg s (regIdx rs) }) _ _ (Ops.MTHI rs)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl) rfl rfl
  alu_run [Ops.MTHI, readGPR_abs s hg.2.2]
  rfl

/-- **MTLO refines.** -/
theorem mtlo_refines (s : State) (hg : Good s) (rs w : W32)
    (hw : enc (.mtlo rs) = some w) :
    Execute modelCtx w (.mtlo rs) (abs s) = some (abs (execInstr s (.mtlo rs))) := by
  obtain rfl : rFormat 0#32 rs 0#32 0#32 0#32 0x13#32 = w := Option.some.inj hw
  refine refine_ok s ({ s with lo := readReg s (regIdx rs) }) _ _ (Ops.MTLO rs)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl) rfl rfl
  alu_run [Ops.MTLO, readGPR_abs s hg.2.2]
  rfl

/-- **MUL refines** (`HI`, `LO`: the oracle's `mulHILO`, which `modelOracle` leaves). -/
theorem mul_refines (s : State) (hg : Good s) (rs rt rd w : W32)
    (hw : enc (.mul rs rt rd) = some w) :
    Execute modelCtx w (.mul rs rt rd) (abs s) = some (abs (execInstr s (.mul rs rt rd))) := by
  obtain rfl : rFormat 0x1C#32 rs rt rd 0#32 0x02#32 = w := Option.some.inj hw
  refine refine_gpr s hg _ _ (Ops.MUL rs rt rd) rd (readReg s (regIdx rs) * readReg s (regIdx rt))
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl)
  alu_run [Ops.MUL, readGPR_abs s hg.2.2, mul_low]
  rfl

/-- **MADD refines.** -/
theorem madd_refines (s : State) (hg : Good s) (rs rt w : W32)
    (hw : enc (.madd rs rt) = some w) :
    Execute modelCtx w (.madd rs rt) (abs s) = some (abs (execInstr s (.madd rs rt))) := by
  obtain rfl : rFormat 0x1C#32 rs rt 0#32 0#32 0x00#32 = w := Option.some.inj hw
  refine refine_ok s ({ s with lo := ((s.hi ++ s.lo) + BitVec.ofInt 64 (asSigned (readReg s (regIdx rs)) * asSigned (readReg s (regIdx rt)))).extractLsb 31 0, hi := ((s.hi ++ s.lo) + BitVec.ofInt 64 (asSigned (readReg s (regIdx rs)) * asSigned (readReg s (regIdx rt)))).extractLsb 63 32 }) _ _ (Ops.MADD rs rt)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl) rfl rfl
  alu_run [Ops.MADD, readGPR_abs s hg.2.2, mult_eq]
  rfl

/-- **MADDU refines.** -/
theorem maddu_refines (s : State) (hg : Good s) (rs rt w : W32)
    (hw : enc (.maddu rs rt) = some w) :
    Execute modelCtx w (.maddu rs rt) (abs s) = some (abs (execInstr s (.maddu rs rt))) := by
  obtain rfl : rFormat 0x1C#32 rs rt 0#32 0#32 0x01#32 = w := Option.some.inj hw
  refine refine_ok s ({ s with lo := ((s.hi ++ s.lo) + BitVec.ofNat 64 ((readReg s (regIdx rs)).toNat * (readReg s (regIdx rt)).toNat)).extractLsb 31 0, hi := ((s.hi ++ s.lo) + BitVec.ofNat 64 ((readReg s (regIdx rs)).toNat * (readReg s (regIdx rt)).toNat)).extractLsb 63 32 }) _ _ (Ops.MADDU rs rt)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl) rfl rfl
  alu_run [Ops.MADDU, readGPR_abs s hg.2.2, multu_eq]
  rfl

/-- **MSUB refines.** -/
theorem msub_refines (s : State) (hg : Good s) (rs rt w : W32)
    (hw : enc (.msub rs rt) = some w) :
    Execute modelCtx w (.msub rs rt) (abs s) = some (abs (execInstr s (.msub rs rt))) := by
  obtain rfl : rFormat 0x1C#32 rs rt 0#32 0#32 0x04#32 = w := Option.some.inj hw
  refine refine_ok s ({ s with lo := ((s.hi ++ s.lo) - BitVec.ofInt 64 (asSigned (readReg s (regIdx rs)) * asSigned (readReg s (regIdx rt)))).extractLsb 31 0, hi := ((s.hi ++ s.lo) - BitVec.ofInt 64 (asSigned (readReg s (regIdx rs)) * asSigned (readReg s (regIdx rt)))).extractLsb 63 32 }) _ _ (Ops.MSUB rs rt)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl) rfl rfl
  alu_run [Ops.MSUB, readGPR_abs s hg.2.2, mult_eq]
  rfl

/-- **MSUBU refines.** -/
theorem msubu_refines (s : State) (hg : Good s) (rs rt w : W32)
    (hw : enc (.msubu rs rt) = some w) :
    Execute modelCtx w (.msubu rs rt) (abs s) = some (abs (execInstr s (.msubu rs rt))) := by
  obtain rfl : rFormat 0x1C#32 rs rt 0#32 0#32 0x05#32 = w := Option.some.inj hw
  refine refine_ok s ({ s with lo := ((s.hi ++ s.lo) - BitVec.ofNat 64 ((readReg s (regIdx rs)).toNat * (readReg s (regIdx rt)).toNat)).extractLsb 31 0, hi := ((s.hi ++ s.lo) - BitVec.ofNat 64 ((readReg s (regIdx rs)).toNat * (readReg s (regIdx rt)).toNat)).extractLsb 63 32 }) _ _ (Ops.MSUBU rs rt)
    (fun h => nomatch h) (by alu_space) (by alu_space) rfl ?_ (execInstr_body s _ rfl rfl rfl) rfl rfl
  alu_run [Ops.MSUBU, readGPR_abs s hg.2.2, multu_eq]
  rfl

end Refine
