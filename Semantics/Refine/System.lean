import Semantics.Refine.BridgeMem
import Semantics.Refine.Cycle

/-!
# Refine.System — standby and hardware registers against `execInstr`

`wait` (COP0 encoding space, a CTI: Reserved Instruction in a delay slot on both
sides, then the Coprocessor Unusable check), `pause` (a CTI outside the COP0 space) and `rdhwr` (SPECIAL3, its own access check, MD00086
Vol II-A Rev 6.06, RDHWR, Restrictions, p.333). Also `eret` (ERET p.177-178: COP0
space, a CTI, no delay slot: `PC ← temp` at time `I`).
-/

namespace Refine

open Manual

/-- The model's `wait` test, `interruptRequests s == 0`, is the manual's `InterruptRequests = 0`. -/
theorem wait_cond (s : State) :
    (interruptRequests s == 0#32) = decide (InterruptRequests modelImpl (abs s) = 0#8) := by
  have hr := interruptRequests_abs s
  cases h : (interruptRequests s == 0#32)
  · have : (interruptRequests s != 0#32) = true := by simp [bne, h]
    rw [hr] at this; simp only [decide_eq_true_eq] at this; simp [this]
  · have : (interruptRequests s != 0#32) = false := by simp [bne, h]
    rw [hr] at this; simp only [decide_eq_false_iff_not, Decidable.not_not] at this; simp [this]

/-- **WAIT refines** (the Release 6 Operation, p.442-443): Reserved Instruction in a delay slot (a
CTI), Coprocessor Unusable without CP0 access, else the lower power mode exactly when no request is
pending and not masked out. -/
theorem wait_refines (s : State) (code w : W32) (hw : enc (.wait code) = some w) :
    Execute modelCtx w (.wait code) (abs s) = some (abs (execInstr s (.wait code))) := by
  have hw' : w = fld 6 26 0x10#32 ||| fld 1 25 1#32 ||| fld 19 6 code ||| fld 6 0 0x20#32 :=
    (Option.some.inj hw).symm
  have hc0 : InCop0Space w = true := by subst hw'; simp [InCop0Space, opcode_wait]
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_wait]
  have hbl : isBranchLike (.wait code) = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w _ s t rfl hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    rw [execute_cop0 w _ s _ (.inr hpb) hc1 hc0 rfl, execInstr_cop0 s _ (.inr hpb) rfl rfl]
    cases hu : cp0Usable s
    · rfl
    · simp only [↓reduceIte]
      show _ = some (abs (mkNext s { s with standby := interruptRequests s == 0#32 }))
      simp only [Pseudo.run, Ops.WAIT, bind, Pseudo.impl, Pseudo.get, cp0usable_abs, hu, ↓reduceIte,
        Pseudo.modify, complete_plain, mkNext, show modelCtx.impl = modelImpl from rfl, wait_cond]
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

/-- `Config5.XNP` (bit 13) as `RDHWR` register 5 reads it: the model's `xnpValue`. -/
theorem xnp_eq (s : State) : zero_extend (bits (Config5Read modelImpl (abs s)) 13 13) = xnpValue := by
  simp only [Config5Read, abs]
  by_cases h : s.cp0Config5SBRI = true <;> simp only [h, ↓reduceIte] <;> decide

/-- **RDHWR refines** (Release 6, with `sel`): Reserved Instruction for `sel ≠ 0` on both sides,
else the register read with its access check; registers 5 (`XNP`) and 29 (`UserLocal`) are
implemented. -/
theorem rdhwr_refines (s : State) (hg : Good s) (rt rd sel w : W32)
    (hw : enc (.rdhwr rt rd sel) = some w) :
    Execute modelCtx w (.rdhwr rt rd sel) (abs s) = some (abs (execInstr s (.rdhwr rt rd sel))) := by
  obtain ⟨hsz, -, h0⟩ := hg
  have hw' : w = fld 6 26 0x1F#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 3 6 sel ||| fld 6 0 0x3B#32 :=
    (Option.some.inj hw).symm
  have hc0 : InCop0Space w = false := by
    subst hw'; simp only [InCop0Space, opcode_rdhwr]
    rw [show (fld 6 26 0x1F#32 ||| fld 5 16 rt ||| fld 5 11 rd ||| fld 3 6 sel ||| fld 6 0 0x3B#32) &&&
      0x3F#32 = 0x3B#32 by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        simp only [fld, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
        rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;> simp <;> omega]
    rfl
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_rdhwr]
  rw [execute_run modelCtx w _ _ (Ops.RDHWR rt rd sel) rfl hc1 hc0 rfl]
  have hex : execInstr s (.rdhwr rt rd sel) =
      (if sel != 0#32 then takeException s excCodeRI else
       match hwrValue s rd with
       | some v => if rdhwrAllowed s rd then mkNext s (writeReg s (regIdx rt) v)
                   else takeException s excCodeRI
       | none => takeException s excCodeRI) := by
    have h1 : isBranchLike (.rdhwr rt rd sel) = false := rfl
    have h2 : usesCop1 (.rdhwr rt rd sel) = false := rfl
    have h3 : usesCop0 (.rdhwr rt rd sel) = false := rfl
    unfold execInstr; rw [h1, h2, h3]; rfl
  rw [hex]
  have hri : GeneralExceptionProcessing modelImpl modelCtx.oracle .ReservedInstruction (abs s) =
      abs (takeException s excCodeRI) := gep_take s .ReservedInstruction rfl excCodeRI (by decide)
  cases hs : (sel != 0#32)
  · simp only [hwrValue, rdhwrAllowed, hwrena_bit, Pseudo.run, Ops.RDHWR, bind, Pseudo.impl,
      Pseudo.get, cp0usable_abs, show modelCtx.impl = modelImpl from rfl, hs, Bool.false_eq_true,
      ↓reduceIte]
    have hcpu := cpunum_eq s
    have hxnp := xnp_eq s
    rw [show (abs s).HWREna = s.cp0HWREna from rfl, show (abs s).UserLocal = s.cp0UserLocal from rfl]
    generalize rd.toNat = r
    by_cases hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 29
    · rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;>
        cases hen : (cp0Usable s || bit s.cp0HWREna _) <;>
        simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, SignalException, hri,
          setGPR, pure] <;>
        first
          | rfl
          | (rw [hcpu]; exact complete_writeReg s hsz _ _)
          | (rw [hxnp]; exact complete_writeReg s hsz _ _)
          | exact complete_writeReg s hsz _ _
    · simp only [not_or] at hr
      obtain ⟨h0', h1', h2', h3', h5', h29'⟩ := hr
      cases hen : (cp0Usable s || bit s.cp0HWREna r) <;>
        simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, SignalException, hri] <;>
        (repeat' split) <;>
        first
          | (exfalso; simp_all)
          | rfl
          | simp only [SignalException, hri]
  · simp only [Pseudo.run, Ops.RDHWR, bind, Pseudo.impl, Pseudo.get, hs, ↓reduceIte, SignalException,
      show modelCtx.impl = modelImpl from rfl, hri]

/-- **PAUSE refines** (Release 6): Reserved Instruction in a delay slot (a CTI); otherwise, with
`LLbit = 1`, `EPC ← PC + 4` and the lower power mode of `WAIT` (the pin of `Ops.PAUSE`), and nothing
with `LLbit = 0`. -/
theorem pause_refines (s : State) (w : W32) (hw : enc .pause = some w) :
    Execute modelCtx w .pause (abs s) = some (abs (execInstr s .pause)) := by
  obtain rfl : rFormat 0#32 0#32 0#32 0#32 5#32 0#32 = w := Option.some.inj hw
  have hc0 : InCop0Space (rFormat 0#32 0#32 0#32 0#32 5#32 0#32) = false := by
    rw [inCop0_rFormat]; rfl
  have hc1 : InCop1Space (rFormat 0#32 0#32 0#32 0#32 5#32 0#32) = false := by
    rw [inCop1_rFormat]; rfl
  have hbl : isBranchLike .pause = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot _ _ s t rfl hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    rw [execute_cti_run _ _ s Ops.PAUSE hpb hc1 hc0 rfl]
    unfold execInstr; rw [hbl, hpb]
    simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      show usesCop1 .pause = false from rfl, show usesCop0 .pause = false from rfl, Bool.false_and]
    exec_unfold
    simp only [Pseudo.run, Ops.PAUSE, bind, Pseudo.get, PC, Pseudo.modify,
      show (abs s).LLbit = s.llBit from rfl, show (abs s).PC = s.pc from rfl]
    cases hl : s.llBit
    · simp only [Bool.false_eq_true, ↓reduceIte, pure]
      exact congrArg some (complete_nop s)
    · simp only [↓reduceIte, complete_plain, mkNext]
      rw [abs_advance _ _ (by rfl)]
      simp [hpb, hl, abs, readReg, readFpReg64]

/-- **ERET refines**: Reserved Instruction in a delay slot (Release 6), Coprocessor
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
    rw [execute_cti_slot w _ s t rfl hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    rw [execute_cop0 w _ s _ (.inr hpb) hc1 hc0 rfl, execInstr_cop0 s _ (.inr hpb) rfl rfl]
    cases hu : cp0Usable s
    · rfl
    · simp only [↓reduceIte]; exec_unfold
      simp only [Pseudo.run, Ops.ERET, bind, Pseudo.get, Pseudo.modify, setPC, pure, erl_abs]
      unfold erlSet
      cases (s.cp0Status &&& statusErlMask != 0#32)
      · simp [Complete, abs, hpb, readReg, readFpReg64, statusExlMask]
      · simp [Complete, abs, hpb, readReg, readFpReg64, statusErlMask]

/-- **ERETNC refines** (MD00086 Vol II-A Rev 6.06, ERETNC, p.179-180): Reserved Instruction in a delay
slot, Coprocessor Unusable without CP0 access, else as `ERET` but with `LLbit` unchanged. -/
theorem eretnc_refines (s : State) (w : W32) (hw : enc .eretnc = some w) :
    Execute modelCtx w .eretnc (abs s) = some (abs (execInstr s .eretnc)) := by
  have hw' : w = fld 6 26 0x10#32 ||| fld 1 25 1#32 ||| fld 1 6 1#32 ||| fld 6 0 0x18#32 :=
    (Option.some.inj hw).symm
  have hop : opcode w = 0x10#32 := by subst hw'; opcode_tac
  have hc0 : InCop0Space w = true := by simp [InCop0Space, hop]
  have hc1 : InCop1Space w = false := by simp [InCop1Space, hop]
  have hbl : isBranchLike .eretnc = true := rfl
  cases hpb : s.pendingBranch with
  | some t =>
    rw [execute_cti_slot w _ s t rfl hpb]
    unfold execInstr; rw [hbl, hpb]; rfl
  | none =>
    rw [execute_cop0 w _ s _ (.inr hpb) hc1 hc0 rfl, execInstr_cop0 s _ (.inr hpb) rfl rfl]
    cases hu : cp0Usable s
    · rfl
    · simp only [↓reduceIte]; exec_unfold
      simp only [Pseudo.run, Ops.ERETNC, bind, Pseudo.get, Pseudo.modify, setPC, pure, erl_abs]
      unfold erlSet
      cases (s.cp0Status &&& statusErlMask != 0#32)
      · simp [Complete, abs, hpb, readReg, readFpReg64, statusExlMask]
      · simp [Complete, abs, hpb, readReg, readFpReg64, statusErlMask]

/-- **CACHE refines** (MD00086 Vol II-A Rev 6.06, CACHE, p.114-119): Coprocessor Unusable without CP0
access; else the address translation of `GPR[base] + sign_extend(offset)` (an Address Error, AdEL,
if it fails) and no cache operation (no cache: "In Release 6, the instruction in this case should
perform no operation", p.119). -/
theorem cache_refines (s : State) (hg : Good s) (base op off w : W32)
    (hw : enc (.cache base op off) = some w) :
    Execute modelCtx w (.cache base op off) (abs s) = some (abs (execInstr s (.cache base op off))) := by
  obtain ⟨-, -, h0⟩ := hg
  have hw' : w = off9Format base op off 0x25#32 := (Option.some.inj hw).symm
  have hc0 : InCop0Space w = true := by
    subst hw'; simp [InCop0Space, opcode_off9Format, funct_off9Format]
  have hc1 : InCop1Space w = false := by subst hw'; simp [InCop1Space, opcode_off9Format]
  rw [execute_cop0 w _ s _ (.inl rfl) hc1 hc0 rfl, execInstr_cop0 s _ (.inl rfl) rfl rfl]
  cases hu : cp0Usable s
  · rfl
  · simp only [↓reduceIte]
    show _ = some (abs (match translate s (readReg s (regIdx base) + signExt9 off) with
      | none => takeAddressException s excCodeAdEL (readReg s (regIdx base) + signExt9 off)
      | some _ => mkNext s s))
    simp only [Pseudo.run, Ops.CACHE, bind, GPR, readGPR_abs s h0, ← regIdx_eq_reg, offset9]
    rw [addrTrans_run s _ .DATA .LOAD modelCtx { arch := abs s } rfl]
    cases translate s (readReg s (regIdx base) + signExt9 off)
    · simp only
      rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl,
        gep_adel]
    · exact congrArg some (complete_nop s)

/-! ## DVP, EVP: no-ops without multi-threading (`Config5.VP = 0`) -/

theorem opcode_vp (rt sc : W32) :
    opcode (fld 6 26 0x10#32 ||| fld 5 21 0x0B#32 ||| fld 5 16 rt ||| fld 1 5 sc ||| fld 3 0 4#32) =
      0x10#32 := by opcode_tac

/-- DVP and EVP (`sc` = 1 / 0) refine: Coprocessor Unusable without CP0 access, else no operation
(MD00086 Vol II-A Rev 6.06, DVP p.172, EVP p.181: with `Config5VP = 0` "this instruction must be
treated as a NOP instruction"). -/
theorem vp_refines (s : State) (i : Instruction) (rt sc w : W32)
    (hi : i = .dvp rt ∨ i = .evp rt) (hop : Manual.Operation i = some (pure ()))
    (hw : w = fld 6 26 0x10#32 ||| fld 5 21 0x0B#32 ||| fld 5 16 rt ||| fld 1 5 sc ||| fld 3 0 4#32)
    (hx : execBody s i = mkNext s s) :
    Execute modelCtx w i (abs s) = some (abs (execInstr s i)) := by
  have hc0 : InCop0Space w = true := by subst hw; simp [InCop0Space, opcode_vp]
  have hc1 : InCop1Space w = false := by subst hw; simp [InCop1Space, opcode_vp]
  have hb : isBranchLike i = false := by rcases hi with rfl | rfl <;> rfl
  have hu1 : usesCop1 i = false := by rcases hi with rfl | rfl <;> rfl
  have hu0 : usesCop0 i = true := by rcases hi with rfl | rfl <;> rfl
  have hcti : IsCTI i = false := by rcases hi with rfl | rfl <;> rfl
  rw [execute_cop0 w _ s _ (.inl hcti) hc1 hc0 hop, execInstr_cop0 s _ (.inl hb) hu1 hu0]
  cases hu : cp0Usable s
  · rfl
  · simp only [↓reduceIte, hx]
    exact congrArg some (complete_nop s)

/-- **DVP refines.** -/
theorem dvp_refines (s : State) (rt w : W32) (hw : enc (.dvp rt) = some w) :
    Execute modelCtx w (.dvp rt) (abs s) = some (abs (execInstr s (.dvp rt))) :=
  vp_refines s _ rt 1#32 w (.inl rfl) rfl (Option.some.inj hw).symm rfl

/-- **EVP refines.** -/
theorem evp_refines (s : State) (rt w : W32) (hw : enc (.evp rt) = some w) :
    Execute modelCtx w (.evp rt) (abs s) = some (abs (execInstr s (.evp rt))) :=
  vp_refines s _ rt 0#32 w (.inr rfl) rfl (Option.some.inj hw).symm rfl

end Refine
