import Lean.Elab.Tactic
import Semantics.Specs.Invariants
import Semantics.Specs.RegFileSize
import Semantics.Env
import Semantics.Refine.Defs

/-!
# Refine.Invariant — two more invariants of the reachable states (7D)

* `FcsrReservedZero s`: the stored FCSR bits 31..25, 23..18 are 0 (`Refine/Defs.lean`: the Release 6
  reserved FCC bits, `Impl`, bit 20, and the read-only `ABS2008`/`NAN2008`, which `Mips.Fp.readFCSR`
  adds on read). Every write of the model keeps them 0 (`fpUpdate` leaves them, `CTC1` writes the
  `writeControl` results, which mask them with `fcsrWritableMask` or leave them).
* `StatusImplemented s`: `Status` holds only the bits this profile implements (`statusWriteMask`):
  `mtc0` masks its value, the exception entry sets `EXL`, `di`/`ei` clear/set `IE`, `eret` clears
  `EXL`/`ERL`, the Reset sets `BEV`/`ERL`, the boot convention writes `CU1`.

Both are preserved by `step` (for every state, `step_preserves_*`) and hold after `resetState`,
`hostedStart`, `load p`. The proof of `step` follows `execInstr_zeroKept` (`Specs/Invariants.lean`):
a `Kept` predicate, its lemmas for each result shape of `execInstr`, one `split` loop.
-/

namespace Refine

/-- The FCSR bits that are not R/W on this profile: 31..25, 23..18 (`FcsrReservedZero`). -/
def fcsrReservedBits : W32 := 0xFEFC0000#32

/-- The FCSR property on a word. -/
def RZ (x : W32) : Prop := x &&& 0xFEFC0000#32 = 0#32

/-- The Status property on a word. -/
def SI (x : W32) : Prop := x &&& statusWriteMask = x

/-! ## Bits -/

private theorem rbit : ∀ i : Fin 32,
    (0xFEFC0000#32).getLsbD i.val = decide (18 ≤ i.val ∧ i.val ≠ 24) := by decide

private theorem rcases13 (i : Nat) (h1 : 18 ≤ i) (h2 : i < 32) (h3 : i ≠ 24) :
    i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega

/-- Two words with the same bits 31..25, 23..18 agree on `RZ`. -/
theorem rz_congr (x y : W32) (h : ∀ i, 18 ≤ i → i < 32 → i ≠ 24 → x.getLsbD i = y.getLsbD i) :
    RZ x ↔ RZ y := by
  have key : x &&& 0xFEFC0000#32 = y &&& 0xFEFC0000#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, rbit ⟨i, hi⟩]
    by_cases h1 : 18 ≤ i ∧ i ≠ 24
    · rw [h i h1.1 hi h1.2]
    · simp [h1]
  unfold RZ; rw [key]

theorem rz_fpUpdate (f : W32) (g : Mips.Fp.Flags) : RZ (Mips.Fp.fpUpdate f g).1 ↔ RZ f := by
  apply rz_congr; intro i h1 h2 h3
  rcases rcases13 i h1 h2 h3 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    unfold Mips.Fp.fpUpdate Mips.Fp.raiseFlags
    split <;> simp [Mips.Fp.fcsrCauseMask, BitVec.getLsbD_of_ge]

private theorem rz_keep (f g : W32)
    (h : ∀ i, 18 ≤ i → i < 32 → i ≠ 24 → g.getLsbD i = f.getLsbD i) (hf : RZ f) : RZ g :=
  (rz_congr g f h).mpr hf

theorem rz_writeControl (f v g : W32) (n : Nat) (h : Mips.Fp.writeControl f n v = some g)
    (hf : RZ f) : RZ g := by
  unfold Mips.Fp.writeControl at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact hf
  · refine rz_keep _ _ (fun i h1 h2 h3 => ?_) hf
    rcases rcases13 i h1 h2 h3 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [Mips.Fp.writeFEXR, Mips.Fp.fcsrCauseMask, Mips.Fp.fcsrFlagsMask]
  · refine rz_keep _ _ (fun i h1 h2 h3 => ?_) hf
    rcases rcases13 i h1 h2 h3 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [Mips.Fp.writeFENR, Mips.Fp.fcsrEnablesMask, Mips.Fp.fcsrRMMask,
      Mips.Fp.fcsrFSMask]
  · unfold RZ Mips.Fp.writeFCSR Mips.Fp.fcsrWritableMask
    rw [BitVec.and_assoc, show (0x0103FFFF#32 &&& 0xFEFC0000#32) = 0#32 by decide,
      BitVec.and_zero]

theorem si_or_exl (x : W32) : SI (x ||| statusExlMask) ↔ SI x := by
  unfold SI
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have := congrArg (·.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] at this ⊢
    rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i <;>
      simp_all [statusWriteMask, statusExlMask]
  · intro h
    rw [BitVec.and_or_distrib_right, h]; rfl

theorem si_or_mask (x m : W32) (hm : m &&& statusWriteMask = m) (h : SI x) : SI (x ||| m) := by
  unfold SI at *; rw [BitVec.and_or_distrib_right, h, hm]

theorem si_and (x y : W32) (h : SI x) : SI (x &&& y) := by
  unfold SI at *
  rw [BitVec.and_assoc, BitVec.and_comm y, ← BitVec.and_assoc, h]

theorem si_mask (x : W32) : SI (x &&& statusWriteMask) := by
  unfold SI; rw [BitVec.and_assoc, BitVec.and_self]

/-! ## The `Kept` predicate and the result shapes of `execInstr` -/

/-- `r` keeps both properties of `s`. -/
def Kept (s r : State) : Prop := (RZ s.fcsr → RZ r.fcsr) ∧ (SI s.cp0Status → SI r.cp0Status)

theorem advance_fcsr (o r : State) : (advance o r).fcsr = r.fcsr := by
  unfold advance; split <;> rfl
theorem advance_cp0Status (o r : State) : (advance o r).cp0Status = r.cp0Status := by
  unfold advance; split <;> rfl
theorem mkNext_fcsr (o r : State) : (mkNext o r).fcsr = r.fcsr := advance_fcsr o r
theorem mkNext_cp0Status (o r : State) : (mkNext o r).cp0Status = r.cp0Status :=
  advance_cp0Status o r
theorem writeFpReg_fcsr (s : State) (i : Fin 32) (v : W32) : (writeFpReg s i v).fcsr = s.fcsr := rfl
theorem writeFpReg_cp0Status (s : State) (i : Fin 32) (v : W32) :
    (writeFpReg s i v).cp0Status = s.cp0Status := rfl
theorem writeFpD_fcsr (s : State) (f : W32) (v : BitVec 64) : (writeFpD s f v).fcsr = s.fcsr := rfl
theorem writeFpD_cp0Status (s : State) (f : W32) (v : BitVec 64) :
    (writeFpD s f v).cp0Status = s.cp0Status := rfl
theorem exceptionEntry_fcsr (s : State) (c ce : W32) : (exceptionEntry s c ce).fcsr = s.fcsr := rfl
theorem exceptionEntry_cp0Status (s : State) (c ce : W32) :
    (exceptionEntry s c ce).cp0Status = s.cp0Status ||| statusExlMask := rfl
theorem takeException_fcsr (s : State) (c : W32) : (takeException s c).fcsr = s.fcsr := rfl
theorem takeException_cp0Status (s : State) (c : W32) :
    (takeException s c).cp0Status = s.cp0Status ||| statusExlMask := rfl
theorem takeAddressException_fcsr (s : State) (c a : W32) :
    (takeAddressException s c a).fcsr = s.fcsr := rfl
theorem takeAddressException_cp0Status (s : State) (c a : W32) :
    (takeAddressException s c a).cp0Status = s.cp0Status ||| statusExlMask := rfl
theorem takeCoprocessorUnusable_fcsr (s : State) : (takeCoprocessorUnusable s).fcsr = s.fcsr := rfl
theorem takeCoprocessorUnusable_cp0Status (s : State) :
    (takeCoprocessorUnusable s).cp0Status = s.cp0Status ||| statusExlMask := rfl
theorem takeCop0Unusable_fcsr (s : State) : (takeCop0Unusable s).fcsr = s.fcsr := rfl
theorem takeCop0Unusable_cp0Status (s : State) :
    (takeCop0Unusable s).cp0Status = s.cp0Status ||| statusExlMask := rfl

theorem writeMemByte_fcsr (s s' : State) (a : W32) (v : UInt8) (h : writeMemByte s a v = some s') :
    s'.fcsr = s.fcsr ∧ s'.cp0Status = s.cp0Status := by
  unfold writeMemByte at h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h; exact ⟨rfl, rfl⟩
theorem writeMemHalf_fcsr (s s' : State) (a v : W32) (h : writeMemHalf s a v = some s') :
    s'.fcsr = s.fcsr ∧ s'.cp0Status = s.cp0Status := by
  unfold writeMemHalf at h; split at h <;> try simp only [reduceCtorEq] at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h; exact ⟨rfl, rfl⟩
theorem writeMemWord_fcsr (s s' : State) (a v : W32) (h : writeMemWord s a v = some s') :
    s'.fcsr = s.fcsr ∧ s'.cp0Status = s.cp0Status := by
  unfold writeMemWord at h; split at h <;> try simp only [reduceCtorEq] at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h; exact ⟨rfl, rfl⟩
theorem writeMemByte_getD_fcsr (s : State) (a : W32) (v : UInt8) :
    ((writeMemByte s a v).getD s).fcsr = s.fcsr := by
  unfold writeMemByte; cases translate s a <;> rfl
theorem writeMemByte_getD_cp0Status (s : State) (a : W32) (v : UInt8) :
    ((writeMemByte s a v).getD s).cp0Status = s.cp0Status := by
  unfold writeMemByte; cases translate s a <;> rfl

theorem kept_fpFinishS (s : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags) :
    Kept s (fpFinishS s fd r) := by
  unfold fpFinishS Kept; dsimp only
  split
  · exact ⟨fun h => (rz_fpUpdate _ _).mpr h, fun h => (si_or_exl _).mpr h⟩
  · simp only [mkNext_fcsr, mkNext_cp0Status, writeFpReg_fcsr, writeFpReg_cp0Status]
    exact ⟨fun h => (rz_fpUpdate _ _).mpr h, id⟩

theorem kept_fpFinishD (s : State) (fd : W32) (r : BitVec 64 × Mips.Fp.Flags) :
    Kept s (fpFinishD s fd r) := by
  unfold fpFinishD Kept; dsimp only
  split
  · exact ⟨fun h => (rz_fpUpdate _ _).mpr h, fun h => (si_or_exl _).mpr h⟩
  · simp only [mkNext_fcsr, mkNext_cp0Status, writeFpD_fcsr, writeFpD_cp0Status]
    exact ⟨fun h => (rz_fpUpdate _ _).mpr h, id⟩

theorem kept_fpFinishS_iff (s : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags) :
    Kept s (fpFinishS s fd r) ↔ True := iff_true_intro (kept_fpFinishS s fd r)
theorem kept_fpFinishD_iff (s : State) (fd : W32) (r : BitVec 64 × Mips.Fp.Flags) :
    Kept s (fpFinishD s fd r) ↔ True := iff_true_intro (kept_fpFinishD s fd r)
theorem kept_trans {s t r : State} (h1 : Kept s t) (h2 : Kept t r) : Kept s r :=
  ⟨fun h => h2.1 (h1.1 h), fun h => h2.2 (h1.2 h)⟩

theorem kept_fpThen {α : Type} (s : State) (r : α × Mips.Fp.Flags) (k : State → α → State)
    (h : ∀ p, Kept { s with fcsr := (Mips.Fp.fpUpdate s.fcsr r.2).1 }
      (k { s with fcsr := (Mips.Fp.fpUpdate s.fcsr r.2).1 } p)) :
    Kept s (fpThen s r k) := by
  unfold fpThen; dsimp only
  split
  · exact ⟨fun h => (rz_fpUpdate _ _).mpr h, fun h => (si_or_exl _).mpr h⟩
  · exact kept_trans (t := { s with fcsr := (Mips.Fp.fpUpdate s.fcsr r.2).1 })
      ⟨fun h => (rz_fpUpdate _ _).mpr h, id⟩ (h _)

/-- Forward step for the loop below: for every hypothesis `writeMem… s a v = some s'` add
`s'.fcsr = s.fcsr ∧ s'.cp0Status = s.cp0Status`, and for `writeControl f n v = some g` add
`RZ f → RZ g`. -/
elab "kp_fwd" : tactic => Lean.Elab.Tactic.withMainContext do
  for d in (← Lean.getLCtx) do
    if d.isImplementationDetail then continue
    for (lem, n) in [(``writeMemByte_fcsr, 4), (``writeMemHalf_fcsr, 4), (``writeMemWord_fcsr, 4),
        (``rz_writeControl, 4)] do
      try
        let args : Array (Option Lean.Expr) := (Array.replicate n none).push (some d.toExpr)
        let pf ← Lean.Meta.mkAppOptM lem args
        let ty ← Lean.Meta.inferType pf
        Lean.Elab.Tactic.liftMetaTactic fun g => do
          let (_, g) ← (← g.assert `hkp ty pf).intro1
          return [g]
      catch _ => pure ()

/-- Push the two projections of a `Kept` goal through every primitive. -/
macro "kp_simp" : tactic => `(tactic|
  simp only [Kept, mkNext_fcsr, mkNext_cp0Status, writeReg_proj_fcsr, writeReg_proj_cp0Status,
    writeFpReg_fcsr, writeFpReg_cp0Status, writeFpD_fcsr, writeFpD_cp0Status,
    exceptionEntry_fcsr, exceptionEntry_cp0Status, takeException_fcsr, takeException_cp0Status,
    takeAddressException_fcsr, takeAddressException_cp0Status, takeCoprocessorUnusable_fcsr,
    takeCoprocessorUnusable_cp0Status, takeCop0Unusable_fcsr, takeCop0Unusable_cp0Status,
    writeMemByte_getD_fcsr, writeMemByte_getD_cp0Status, si_or_exl, *])

/-- The FCSR half of a leaf. -/
macro "kp_rz" : tactic => `(tactic| first
  | exact id
  | (intro h; assumption)
  | (intro h; apply_assumption; assumption))

/-- The Status half of a leaf. -/
macro "kp_si" : tactic => `(tactic| first
  | exact id
  | exact si_and _ _
  | exact fun _ => si_mask _
  | exact fun h => si_or_mask _ _ (by decide) h)

/-- Close a `Kept` leaf. -/
macro "kp_close" : tactic => `(tactic| ((try simp only [kept_fpFinishS_iff, kept_fpFinishD_iff])
  <;> kp_simp <;> exact ⟨by kp_rz, by kp_si⟩))

set_option maxHeartbeats 4000000 in
/-- **Every instruction keeps both properties.** -/
theorem execInstr_kept (s : State) (instr : Instruction) : Kept s (execInstr s instr) := by
  unfold execInstr
  split
  · exact ⟨id, fun h => (si_or_exl _).mpr h⟩
  · split
    · exact ⟨id, fun h => (si_or_exl _).mpr h⟩
    · split
      · exact ⟨id, fun h => (si_or_exl _).mpr h⟩
      · cases instr <;> exec_unfold <;>
          repeat' (first | (kp_fwd; kp_close; done) | split | (apply kept_fpThen; intro _))

/-! ## `step` -/

theorem stepCore_kept (s : State) : Kept s (stepCore s) := by
  unfold stepCore
  split
  · exact ⟨id, fun h => (si_or_exl _).mpr h⟩
  split
  · unfold standbyStep; split <;> exact ⟨id, id⟩
  unfold execute
  split
  · exact ⟨id, fun h => (si_or_exl _).mpr h⟩
  · split
    · split
      · exact ⟨id, fun h => (si_or_exl _).mpr h⟩
      · split
        · exact ⟨id, fun h => (si_or_exl _).mpr h⟩
        · split <;> exact ⟨id, fun h => (si_or_exl _).mpr h⟩
    · exact execInstr_kept _ _

theorem step_preserves_fcsrReservedZero (s : State) (h : FcsrReservedZero s) :
    FcsrReservedZero (step s) :=
  (stepCore_kept s).1 h

theorem step_preserves_statusImplemented (s : State) (h : StatusImplemented s) :
    StatusImplemented (step s) :=
  (stepCore_kept s).2 h

theorem run_preserves_fcsrReservedZero (s : State) (n : Nat) (h : FcsrReservedZero s) :
    FcsrReservedZero (run s n) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih _ (step_preserves_fcsrReservedZero s h)

theorem run_preserves_statusImplemented (s : State) (n : Nat) (h : StatusImplemented s) :
    StatusImplemented (run s n) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih _ (step_preserves_statusImplemented s h)

/-! ## Reset and the loader -/

theorem resetException_fcsrReservedZero (s : State) (h : FcsrReservedZero s) :
    FcsrReservedZero (resetException s) := h

theorem resetException_statusImplemented (s : State) (h : StatusImplemented s) :
    StatusImplemented (resetException s) := by
  show SI (s.cp0Status ||| statusBevMask ||| statusErlMask)
  exact si_or_mask _ _ (by decide) (si_or_mask _ _ (by decide) h)

theorem resetState_fcsrReservedZero : FcsrReservedZero resetState := by
  unfold FcsrReservedZero; decide
theorem resetState_statusImplemented : StatusImplemented resetState := by
  unfold StatusImplemented; decide
theorem hostedStart_fcsrReservedZero : FcsrReservedZero hostedStart := by
  unfold FcsrReservedZero; decide
theorem hostedStart_statusImplemented : StatusImplemented hostedStart := by
  unfold StatusImplemented; decide
theorem load_fcsrReservedZero (p : Program) : FcsrReservedZero (load p) :=
  hostedStart_fcsrReservedZero
theorem load_statusImplemented (p : Program) : StatusImplemented (load p) :=
  hostedStart_statusImplemented

end Refine
