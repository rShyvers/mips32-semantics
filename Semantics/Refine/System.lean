import Semantics.Refine.BridgeControl

/-!
# Refine.System — standby and hardware registers against `execInstr`

7C S3 proves `wait` (COP0 encoding space, a CTI: Reserved Instruction in a delay slot on both
sides, then the Coprocessor Unusable check) and `rdhwr` (SPECIAL3, its own access check, MD00086
Vol II-A Rev 6.06, RDHWR, Restrictions, p.333). The 7C merge adds `eret` (ERET p.177-178: COP0
space, a CTI, no delay slot: `PC ← temp` at time `I`).
-/

namespace Refine

open Manual

/-- **WAIT refines.** -/
theorem wait_refines (s : State) (code w : W32) (hw : enc (.wait code) = some w) :
    Execute modelCtx w (.wait code) (abs s) = some (abs (execInstr s (.wait code))) := by
  have hw' : w = fld 6 26 0x10#32 ||| fld 1 25 1#32 ||| fld 19 6 code ||| fld 6 0 0x20#32 :=
    (Option.some.inj hw).symm
  have hc0 : InCop0Space w = true := by subst hw'; simp [InCop0Space, opcode_wait]
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_wait]
  have hbl : isBranchLike (.wait code) = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w _ s t rfl rfl hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    rw [execute_cop0 w _ s _ (.inr hpb) hc1 hc0 rfl, execInstr_cop0 s _ (.inr hpb) rfl rfl]
    cases hu : cp0Usable s
    · rfl
    · simp only [↓reduceIte]
      show _ = some (abs (mkNext s { s with standby := true }))
      simp only [Pseudo.run, Ops.WAIT, Pseudo.modify, complete_plain, mkNext]
      rw [abs_advance _ _ (by rfl)]; rfl

/-- `HWREna` bit `rd`, the model's shift-and-mask against the manual's bit. -/
theorem hwrena_bit (x rd : W32) : ((x >>> rd) &&& 1#32 != 0#32) = bit x rd.toNat := by
  rw [show (1#32 : W32) = BitVec.twoPow 32 0 by decide, and_twoPow_ne _ 0 (by omega),
    BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, Nat.add_zero]; rfl

/-- `EBaseCPUNum` (`EBase` bits 9..0): 0 on both sides (one processor). -/
theorem cpunum_eq (s : State) :
    zero_extend (bits (EBaseRead (abs s)) 9 0) = ebaseValue s &&& 0x3FF#32 := by
  rw [show EBaseRead (abs s) = ebaseValue s from cprRead_ebase s]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [zero_extend, bits, ebaseValue, ebaseWriteMask, ebaseFixedBits, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or]
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega

/-- **RDHWR refines.** -/
theorem rdhwr_refines (s : State) (hg : Good s) (rt rd w : W32) (hw : enc (.rdhwr rt rd) = some w) :
    Execute modelCtx w (.rdhwr rt rd) (abs s) = some (abs (execInstr s (.rdhwr rt rd))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = fld 6 26 0x1F#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 6 0 0x3B#32 :=
    (Option.some.inj hw).symm
  have hc0 : InCop0Space w = false := by subst hw'; simp [InCop0Space, opcode_rdhwr]
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_rdhwr]
  rw [execute_run modelCtx w _ _ (Ops.RDHWR rt rd) rfl hc1 hc0 rfl]
  have hex : execInstr s (.rdhwr rt rd) =
      (match hwrValue s rd with
       | some v => if rdhwrAllowed s rd then mkNext s (writeReg s (regIdx rt) v)
                   else takeException s excCodeRI
       | none => takeException s excCodeRI) := by
    have h1 : isBranchLike (.rdhwr rt rd) = false := rfl
    have h2 : usesCop1 (.rdhwr rt rd) = false := rfl
    have h3 : usesCop0 (.rdhwr rt rd) = false := rfl
    unfold execInstr; rw [h1, h2, h3]; rfl
  rw [hex]
  have hri : GeneralExceptionProcessing modelImpl modelCtx.oracle .ReservedInstruction (abs s) =
      abs (takeException s excCodeRI) := gep_take s .ReservedInstruction rfl excCodeRI (by decide)
  simp only [hwrValue, rdhwrAllowed, hwrena_bit, Pseudo.run, Ops.RDHWR, bind, Pseudo.impl, Pseudo.get,
    cp0usable_abs, show modelCtx.impl = modelImpl from rfl]
  have hcpu := cpunum_eq s
  rw [show (abs s).HWREna = s.cp0HWREna from rfl]
  generalize rd.toNat = r
  cases hu : cp0Usable s <;> cases hb : bit s.cp0HWREna r <;> rcases r with _|_|_|_|r <;>
    simp only [Bool.or_false, Bool.or_true, Bool.and_false, Bool.and_true, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, ↓reduceIte, SignalException, hri, setGPR, pure,
      Nat.reduceAdd, Nat.reduceLT, decide_true, decide_false, show ∀ n : Nat, ¬ (n + 4 < 4) from fun n => by omega] <;>
    first
      | rfl
      | (rw [hcpu]; exact complete_writeReg s hsz _ _)
      | exact complete_writeReg s hsz _ _

/-- **ERET refines**: Reserved Instruction in a delay slot (the model's `ctiInSlot`), Coprocessor
Unusable without CP0 access, else `PC ← ErrorEPC` and `ERL ← 0` (ERL = 1) or `PC ← EPC` and `EXL ← 0`,
and `LLbit ← 0`. -/
theorem eret_refines (s : State) (w : W32) (hw : enc .eret = some w) :
    Execute modelCtx w .eret (abs s) = some (abs (execInstr s .eret)) := by
  have hw' : w = fld 6 26 0x10#32 ||| fld 1 25 1#32 ||| fld 6 0 0x18#32 := (Option.some.inj hw).symm
  have hc0 : InCop0Space w = true := by subst hw'; simp [InCop0Space, opcode_eret]
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_eret]
  have hbl : isBranchLike .eret = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w _ s t rfl rfl hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    rw [execute_cop0 w _ s _ (.inr hpb) hc1 hc0 rfl, execInstr_cop0 s _ (.inr hpb) rfl rfl]
    cases hu : cp0Usable s
    · rfl
    · simp only [↓reduceIte, execBody]
      simp only [Pseudo.run, Ops.ERET, bind, Pseudo.get, Pseudo.modify, setPC, pure, erl_abs]
      unfold erlSet
      cases (s.cp0Status &&& statusErlMask != 0#32)
      · simp [Complete, abs, hpb, readReg, readFpReg, statusExlMask]
      · simp [Complete, abs, hpb, readReg, readFpReg, statusErlMask]

end Refine
