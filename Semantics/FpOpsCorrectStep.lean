import Semantics.FpOpsCorrectIEEE
import Semantics.Specs.FpuArith

/-!
# FpOpsCorrectStep — the multiply-add family "as if separate instructions"

MD00086 Vol II-A Rev 6.06, MADD.fmt (p.256): "The results and flags are as if separate floating-point
multiply and add instructions were executed"; MSUB.fmt p.287, NMADD.fmt p.308 ("... and negate"),
NMSUB.fmt p.310. `MaddSpec` (`Semantics/FpOpsSpec.lean`) states that reading: each step an operation
meeting its own reference (`MulSpec`, `AddSpec`, `SignOpSpec`), with the FCSR per instruction
(`OpAcc`): after each step Cause is the union of the exceptions of the steps so far (MD00082 Vol I-A
Rev 6.01, Table 6.8 `Cause`, p.94) and the trap check is made; Flags |= that union only if no step
traps ("The Cause bits are ORed into the Flag bits if no exception is taken", MADD.fmt p.256). The
theorems below prove that `step` on each of the eight instructions produces the state of an outcome
`MaddSpec` allows: the Floating-Point exception with the FCSR of the trapping step, or `fd` written
with the final value and the FCSR of the whole instruction (Wave 12a).
-/

namespace Mips.Fp

/-- The outcome `fpUpdate` gives an operation result `r`. -/
def outcomeOf {w : Nat} (fcsr : BitVec 32) (r : BitVec w × Flags) : FpOutcome Nat :=
  if (fpUpdate fcsr r.2).2 then .trap (fpUpdate fcsr r.2).1 else .done (fpUpdate fcsr r.2).1 r.1.toNat

theorem opStep_of {w : Nat} {Op : Nat × Flags → Prop} (fcsr : BitVec 32) (r : BitVec w × Flags)
    (h : Op (r.1.toNat, r.2)) : OpStep Op fcsr (outcomeOf fcsr r) :=
  ⟨(r.1.toNat, r.2), h, _, _, fpUpdate_spec fcsr r.2,
    fun ht => by simp [outcomeOf, ht], fun ht => by simp [outcomeOf, ht]⟩

end Mips.Fp

open Mips.Fp

/-- `fpThen` unfolded. -/
theorem fpThen_unfold {α : Type} (s : State) (r : α × Flags) (k : State → α → State) :
    fpThen s r k = if (fpUpdate s.fcsr r.2).2 then takeException { s with fcsr := (fpUpdate s.fcsr r.2).1 } excCodeFPE
      else k { s with fcsr := (fpUpdate s.fcsr r.2).1 } r.1 := rfl

theorem fpFinishS_unfold (s : State) (fd : W32) (r : BitVec 32 × Flags) :
    fpFinishS s fd r = if (fpUpdate s.fcsr r.2).2 then takeException { s with fcsr := (fpUpdate s.fcsr r.2).1 } excCodeFPE
      else mkNext s (writeFpReg { s with fcsr := (fpUpdate s.fcsr r.2).1 } (regIdx fd) r.1) := rfl

theorem fpFinishD_unfold (s : State) (fd : W32) (r : BitVec 64 × Flags) :
    fpFinishD s fd r = if (fpUpdate s.fcsr r.2).2 then takeException { s with fcsr := (fpUpdate s.fcsr r.2).1 } excCodeFPE
      else mkNext s (writeFpD { s with fcsr := (fpUpdate s.fcsr r.2).1 } fd r.1) := rfl

/-! ## Generic compositions -/

/-- `fpStep` unfolded. -/
theorem fpStep_unfold {α : Type} (s : State) (r : α × Flags) (k : State → α → State) :
    fpStep s r k = if fpeEnabled s.fcsr r.2 then takeException { s with fcsr := setCause s.fcsr r.2 } excCodeFPE
      else k { s with fcsr := setCause s.fcsr r.2 } r.1 := rfl

/-- The state an instruction writing the single `fd` leaves for an outcome. -/
def outcomeStateS (s : State) (fd : W32) : FpOutcome Nat → State
  | .trap c => takeException { s with fcsr := c } excCodeFPE
  | .done c v => mkNext s (writeFpReg { s with fcsr := c } (regIdx fd) (BitVec.ofNat 32 v))

/-- The state an instruction writing the double `fd` leaves for an outcome. -/
def outcomeStateD (s : State) (fd : W32) : FpOutcome Nat → State
  | .trap c => takeException { s with fcsr := c } excCodeFPE
  | .done c v => mkNext s (writeFpD { s with fcsr := c } fd (BitVec.ofNat 64 v))

theorem outcomeStateS_fcsr (s : State) (fd : W32) (c : BitVec 32) (o : FpOutcome Nat) :
    outcomeStateS { s with fcsr := c } fd o = outcomeStateS s fd o := by
  cases o <;> rfl

theorem outcomeStateD_fcsr (s : State) (fd : W32) (c : BitVec 32) (o : FpOutcome Nat) :
    outcomeStateD { s with fcsr := c } fd o = outcomeStateD s fd o := by
  cases o <;> rfl

/-- `fpFinishS` from a state whose Cause an earlier operation wrote: the outcome of the union `r.2`
from the FCSR before the instruction. -/
theorem finishS_setCause (s : State) (fd : W32) (c : Flags) (r : BitVec 32 × Flags) :
    fpFinishS { s with fcsr := setCause s.fcsr c } fd r = outcomeStateS s fd (outcomeOf s.fcsr r) := by
  rw [← outcomeStateS_fcsr s fd (setCause s.fcsr c), fpFinishS_unfold]
  simp only [fpUpdate_setCause, outcomeOf]
  split <;> simp [outcomeStateS]

theorem finishD_setCause (s : State) (fd : W32) (c : Flags) (r : BitVec 64 × Flags) :
    fpFinishD { s with fcsr := setCause s.fcsr c } fd r = outcomeStateD s fd (outcomeOf s.fcsr r) := by
  rw [← outcomeStateD_fcsr s fd (setCause s.fcsr c), fpFinishD_unfold]
  simp only [fpUpdate_setCause, outcomeOf]
  split <;> simp [outcomeStateD]

/-- The last operation of the instruction meets `OpAcc … OpDone` with the outcome `fpUpdate` gives the
union of the exceptions. -/
theorem opAcc_last {w : Nat} (Op : Nat × Flags → Prop) (fcsr : BitVec 32) (acc : Flags)
    (r : BitVec w × Flags) (h : Op (r.1.toNat, r.2)) :
    OpAcc Op fcsr acc OpDone (outcomeOf fcsr (accFlags acc r)) :=
  ⟨(r.1.toNat, r.2), h, _, _, fpUpdate_spec fcsr (acc.or r.2),
    fun ht => by simp [outcomeOf, accFlags, ht],
    fun ht => by simp [outcomeOf, accFlags, ht, OpDone]⟩

/-- An operation that is not the last: it traps (`fpeEnabled` on the union), or the instruction
continues. -/
theorem opAcc_mid {w : Nat} {β : Type} (Op : Nat × Flags → Prop) (fcsr : BitVec 32) (acc : Flags)
    (r : BitVec w × Flags) (h : Op (r.1.toNat, r.2))
    (next : Flags → Nat → BitVec 32 → FpOutcome β → Prop) (out : FpOutcome β)
    (ht : fpeEnabled fcsr (acc.or r.2) = true → out = .trap (setCause fcsr (acc.or r.2)))
    (hn : fpeEnabled fcsr (acc.or r.2) = false →
      next (acc.or r.2) r.1.toNat (fpUpdate fcsr (acc.or r.2)).1 out) :
    OpAcc Op fcsr acc next out := by
  refine ⟨(r.1.toNat, r.2), h, _, _, fpUpdate_spec fcsr (acc.or r.2), fun h1 => ?_, fun h1 => ?_⟩
  · rw [fpUpdate_trap] at h1
    rw [ht h1, fpUpdate_of_enabled _ _ h1]
  · rw [fpUpdate_trap] at h1
    exact hn h1

/-- Two operations, the second completing to the single `fd`. -/
theorem two_stepsS (s : State) (fd : W32) (r1 : BitVec 32 × Flags) (r2 : BitVec 32 → BitVec 32 × Flags)
    (Op1 : Nat × Flags → Prop) (Op2 : Nat → Nat × Flags → Prop) (h1 : Op1 (r1.1.toNat, r1.2))
    (h2 : ∀ p : BitVec 32, Op2 p.toNat ((r2 p).1.toNat, (r2 p).2)) :
    ∃ out, OpAcc Op1 s.fcsr Flags.none (fun acc p _ out1 => OpAcc (Op2 p) s.fcsr acc OpDone out1) out ∧
      fpStep s r1 (fun s1 p => fpFinishS s1 fd (accFlags r1.2 (r2 p))) = outcomeStateS s fd out := by
  rw [fpStep_unfold]
  cases he : fpeEnabled s.fcsr r1.2
  · refine ⟨outcomeOf s.fcsr (accFlags r1.2 (r2 r1.1)), ?_, ?_⟩
    · refine opAcc_mid Op1 s.fcsr Flags.none r1 h1 _ _ (fun h => ?_) (fun _ => ?_)
      · rw [Flags.none_or, he] at h; cases h
      · rw [Flags.none_or]; exact opAcc_last (Op2 r1.1.toNat) s.fcsr r1.2 (r2 r1.1) (h2 r1.1)
    · simp only [Bool.false_eq_true, ite_false]; exact finishS_setCause s fd r1.2 _
  · refine ⟨.trap (setCause s.fcsr r1.2), ?_, rfl⟩
    refine opAcc_mid Op1 s.fcsr Flags.none r1 h1 _ _ (fun _ => by rw [Flags.none_or]) (fun h => ?_)
    rw [Flags.none_or, he] at h; cases h

/-- Two operations, the second completing to the double `fd`. -/
theorem two_stepsD (s : State) (fd : W32) (r1 : BitVec 64 × Flags) (r2 : BitVec 64 → BitVec 64 × Flags)
    (Op1 : Nat × Flags → Prop) (Op2 : Nat → Nat × Flags → Prop) (h1 : Op1 (r1.1.toNat, r1.2))
    (h2 : ∀ p : BitVec 64, Op2 p.toNat ((r2 p).1.toNat, (r2 p).2)) :
    ∃ out, OpAcc Op1 s.fcsr Flags.none (fun acc p _ out1 => OpAcc (Op2 p) s.fcsr acc OpDone out1) out ∧
      fpStep s r1 (fun s1 p => fpFinishD s1 fd (accFlags r1.2 (r2 p))) = outcomeStateD s fd out := by
  rw [fpStep_unfold]
  cases he : fpeEnabled s.fcsr r1.2
  · refine ⟨outcomeOf s.fcsr (accFlags r1.2 (r2 r1.1)), ?_, ?_⟩
    · refine opAcc_mid Op1 s.fcsr Flags.none r1 h1 _ _ (fun h => ?_) (fun _ => ?_)
      · rw [Flags.none_or, he] at h; cases h
      · rw [Flags.none_or]; exact opAcc_last (Op2 r1.1.toNat) s.fcsr r1.2 (r2 r1.1) (h2 r1.1)
    · simp only [Bool.false_eq_true, ite_false]; exact finishD_setCause s fd r1.2 _
  · refine ⟨.trap (setCause s.fcsr r1.2), ?_, rfl⟩
    refine opAcc_mid Op1 s.fcsr Flags.none r1 h1 _ _ (fun _ => by rw [Flags.none_or]) (fun h => ?_)
    rw [Flags.none_or, he] at h; cases h

/-- Three operations, the third completing to the single `fd`. -/
theorem three_stepsS (s : State) (fd : W32) (r1 : BitVec 32 × Flags) (r2 : BitVec 32 → BitVec 32 × Flags)
    (r3 : BitVec 32 → BitVec 32 × Flags)
    (Op1 : Nat × Flags → Prop) (Op2 : Nat → Nat × Flags → Prop) (Op3 : Nat → Nat × Flags → Prop)
    (h1 : Op1 (r1.1.toNat, r1.2)) (h2 : ∀ p : BitVec 32, Op2 p.toNat ((r2 p).1.toNat, (r2 p).2))
    (h3 : ∀ q : BitVec 32, Op3 q.toNat ((r3 q).1.toNat, (r3 q).2)) :
    ∃ out, OpAcc Op1 s.fcsr Flags.none (fun acc p _ out1 =>
        OpAcc (Op2 p) s.fcsr acc (fun acc2 q _ out2 => OpAcc (Op3 q) s.fcsr acc2 OpDone out2) out1) out ∧
      fpStep s r1 (fun s1 p => fpStep s1 (accFlags r1.2 (r2 p))
        (fun s2 q => fpFinishS s2 fd (accFlags (accFlags r1.2 (r2 p)).2 (r3 q)))) =
        outcomeStateS s fd out := by
  rw [fpStep_unfold]
  cases he : fpeEnabled s.fcsr r1.2
  · simp only [Bool.false_eq_true, ite_false]
    rw [fpStep_unfold]
    simp only [fpeEnabled_setCause]
    have hm : ∀ out, (fun acc p (_ : BitVec 32) out1 =>
        OpAcc (Op2 p) s.fcsr acc (fun acc2 q _ out2 => OpAcc (Op3 q) s.fcsr acc2 OpDone out2) out1)
          (Flags.none.or r1.2) r1.1.toNat (fpUpdate s.fcsr (Flags.none.or r1.2)).1 out →
        OpAcc Op1 s.fcsr Flags.none (fun acc p _ out1 =>
          OpAcc (Op2 p) s.fcsr acc (fun acc2 q _ out2 => OpAcc (Op3 q) s.fcsr acc2 OpDone out2) out1) out :=
      fun out hx => opAcc_mid Op1 s.fcsr Flags.none r1 h1 _ _ (fun h => by rw [Flags.none_or, he] at h; cases h)
        (fun _ => hx)
    cases he2 : fpeEnabled s.fcsr (accFlags r1.2 (r2 r1.1)).2
    · refine ⟨outcomeOf s.fcsr (accFlags (accFlags r1.2 (r2 r1.1)).2 (r3 (r2 r1.1).1)), hm _ ?_, ?_⟩
      · simp only [Flags.none_or]
        refine opAcc_mid (Op2 r1.1.toNat) s.fcsr r1.2 (r2 r1.1) (h2 r1.1) _ _ (fun h => ?_) (fun _ => ?_)
        · simp only [accFlags] at he2; rw [he2] at h; cases h
        · exact opAcc_last (Op3 (r2 r1.1).1.toNat) s.fcsr _ (r3 (r2 r1.1).1) (h3 _)
      · simp only [Bool.false_eq_true, ite_false]
        show fpFinishS { s with fcsr := setCause (setCause s.fcsr r1.2) (accFlags r1.2 (r2 r1.1)).2 } fd _ = _
        rw [setCause_setCause]; exact finishS_setCause s fd _ _
    · refine ⟨.trap (setCause s.fcsr (accFlags r1.2 (r2 r1.1)).2), hm _ ?_, ?_⟩
      · simp only [Flags.none_or]
        refine opAcc_mid (Op2 r1.1.toNat) s.fcsr r1.2 (r2 r1.1) (h2 r1.1) _ _ (fun _ => rfl) (fun h => ?_)
        · simp only [accFlags] at he2; rw [he2] at h; cases h
      · simp only [ite_true]
        show takeException { s with fcsr := setCause (setCause s.fcsr r1.2) (accFlags r1.2 (r2 r1.1)).2 } excCodeFPE =
          takeException { s with fcsr := setCause s.fcsr (accFlags r1.2 (r2 r1.1)).2 } excCodeFPE
        rw [setCause_setCause]
  · refine ⟨.trap (setCause s.fcsr r1.2), ?_, rfl⟩
    refine opAcc_mid Op1 s.fcsr Flags.none r1 h1 _ _ (fun _ => by rw [Flags.none_or]) (fun h => ?_)
    rw [Flags.none_or, he] at h; cases h

/-- Three operations, the third completing to the double `fd`. -/
theorem three_stepsD (s : State) (fd : W32) (r1 : BitVec 64 × Flags) (r2 : BitVec 64 → BitVec 64 × Flags)
    (r3 : BitVec 64 → BitVec 64 × Flags)
    (Op1 : Nat × Flags → Prop) (Op2 : Nat → Nat × Flags → Prop) (Op3 : Nat → Nat × Flags → Prop)
    (h1 : Op1 (r1.1.toNat, r1.2)) (h2 : ∀ p : BitVec 64, Op2 p.toNat ((r2 p).1.toNat, (r2 p).2))
    (h3 : ∀ q : BitVec 64, Op3 q.toNat ((r3 q).1.toNat, (r3 q).2)) :
    ∃ out, OpAcc Op1 s.fcsr Flags.none (fun acc p _ out1 =>
        OpAcc (Op2 p) s.fcsr acc (fun acc2 q _ out2 => OpAcc (Op3 q) s.fcsr acc2 OpDone out2) out1) out ∧
      fpStep s r1 (fun s1 p => fpStep s1 (accFlags r1.2 (r2 p))
        (fun s2 q => fpFinishD s2 fd (accFlags (accFlags r1.2 (r2 p)).2 (r3 q)))) =
        outcomeStateD s fd out := by
  rw [fpStep_unfold]
  cases he : fpeEnabled s.fcsr r1.2
  · simp only [Bool.false_eq_true, ite_false]
    rw [fpStep_unfold]
    simp only [fpeEnabled_setCause]
    have hm : ∀ out, (fun acc p (_ : BitVec 32) out1 =>
        OpAcc (Op2 p) s.fcsr acc (fun acc2 q _ out2 => OpAcc (Op3 q) s.fcsr acc2 OpDone out2) out1)
          (Flags.none.or r1.2) r1.1.toNat (fpUpdate s.fcsr (Flags.none.or r1.2)).1 out →
        OpAcc Op1 s.fcsr Flags.none (fun acc p _ out1 =>
          OpAcc (Op2 p) s.fcsr acc (fun acc2 q _ out2 => OpAcc (Op3 q) s.fcsr acc2 OpDone out2) out1) out :=
      fun out hx => opAcc_mid Op1 s.fcsr Flags.none r1 h1 _ _ (fun h => by rw [Flags.none_or, he] at h; cases h)
        (fun _ => hx)
    cases he2 : fpeEnabled s.fcsr (accFlags r1.2 (r2 r1.1)).2
    · refine ⟨outcomeOf s.fcsr (accFlags (accFlags r1.2 (r2 r1.1)).2 (r3 (r2 r1.1).1)), hm _ ?_, ?_⟩
      · simp only [Flags.none_or]
        refine opAcc_mid (Op2 r1.1.toNat) s.fcsr r1.2 (r2 r1.1) (h2 r1.1) _ _ (fun h => ?_) (fun _ => ?_)
        · simp only [accFlags] at he2; rw [he2] at h; cases h
        · exact opAcc_last (Op3 (r2 r1.1).1.toNat) s.fcsr _ (r3 (r2 r1.1).1) (h3 _)
      · simp only [Bool.false_eq_true, ite_false]
        show fpFinishD { s with fcsr := setCause (setCause s.fcsr r1.2) (accFlags r1.2 (r2 r1.1)).2 } fd _ = _
        rw [setCause_setCause]; exact finishD_setCause s fd _ _
    · refine ⟨.trap (setCause s.fcsr (accFlags r1.2 (r2 r1.1)).2), hm _ ?_, ?_⟩
      · simp only [Flags.none_or]
        refine opAcc_mid (Op2 r1.1.toNat) s.fcsr r1.2 (r2 r1.1) (h2 r1.1) _ _ (fun _ => rfl) (fun h => ?_)
        · simp only [accFlags] at he2; rw [he2] at h; cases h
      · simp only [ite_true]
        show takeException { s with fcsr := setCause (setCause s.fcsr r1.2) (accFlags r1.2 (r2 r1.1)).2 } excCodeFPE =
          takeException { s with fcsr := setCause s.fcsr (accFlags r1.2 (r2 r1.1)).2 } excCodeFPE
        rw [setCause_setCause]
  · refine ⟨.trap (setCause s.fcsr r1.2), ?_, rfl⟩
    refine opAcc_mid Op1 s.fcsr Flags.none r1 h1 _ _ (fun _ => by rw [Flags.none_or]) (fun h => ?_)
    rw [Flags.none_or, he] at h; cases h

/-! ## The eight instructions -/

/-- **`MADD.S` is "as if separate floating-point multiply and add instructions were executed"**
(MD00086 Vol II-A Rev 6.06, MADD.fmt p.256): `step` delivers the state of an outcome `MaddSpec`
allows (kind 0). -/
theorem maddS_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.maddS fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : FpOutcome Nat, MaddSpec binary32 (envOf s.fcsr) 0 s.fcsr (readFpReg s (regIdx fr)).toNat
        (readFpReg s (regIdx fs)).toNat (readFpReg s (regIdx ft)).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpReg { s with fcsr := c } (regIdx fd) (BitVec.ofNat 32 v))) := by
  rw [maddS_spec_raw s w fd fr fs ft hfetch hdecode hpb hcu hexec]
  dsimp only
  obtain ⟨out, h, e⟩ := two_stepsS s fd (r1 := f32Mul (envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
    (Op1 := binary32.MulSpec (envOf s.fcsr) (readFpReg s (regIdx fs)).toNat (readFpReg s (regIdx ft)).toNat)
    (r2 := fun p => f32Add (envOf s.fcsr) p (readFpReg s (regIdx fr)))
    (Op2 := fun p => binary32.AddSpec (envOf s.fcsr) false p (readFpReg s (regIdx fr)).toNat)
    (h1 := f32Mul_spec (envOf s.fcsr) _ _)
    (h2 := (fun p => f32Add_spec (envOf s.fcsr) p (readFpReg s (regIdx fr))))
  exact ⟨out, by simpa [MaddSpec] using h, by rw [e]; cases out <;> rfl⟩

/-- **`MSUB.S`** "as if separate" multiply and subtract (MSUB.fmt p.287; kind 1). -/
theorem msubS_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.msubS fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : FpOutcome Nat, MaddSpec binary32 (envOf s.fcsr) 1 s.fcsr (readFpReg s (regIdx fr)).toNat
        (readFpReg s (regIdx fs)).toNat (readFpReg s (regIdx ft)).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpReg { s with fcsr := c } (regIdx fd) (BitVec.ofNat 32 v))) := by
  rw [msubS_spec_raw s w fd fr fs ft hfetch hdecode hpb hcu hexec]
  dsimp only
  obtain ⟨out, h, e⟩ := two_stepsS s fd (r1 := f32Mul (envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
    (Op1 := binary32.MulSpec (envOf s.fcsr) (readFpReg s (regIdx fs)).toNat (readFpReg s (regIdx ft)).toNat)
    (r2 := fun p => f32Sub (envOf s.fcsr) p (readFpReg s (regIdx fr)))
    (Op2 := fun p => binary32.AddSpec (envOf s.fcsr) true p (readFpReg s (regIdx fr)).toNat)
    (h1 := f32Mul_spec (envOf s.fcsr) _ _)
    (h2 := (fun p => f32Sub_spec (envOf s.fcsr) p (readFpReg s (regIdx fr))))
  exact ⟨out, by simpa [MaddSpec] using h, by rw [e]; cases out <;> rfl⟩

/-- **`NMADD.S`** "as if separate" multiply, add and negate (NMADD.fmt p.308; kind 2). -/
theorem nmaddS_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.nmaddS fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : FpOutcome Nat, MaddSpec binary32 (envOf s.fcsr) 2 s.fcsr (readFpReg s (regIdx fr)).toNat
        (readFpReg s (regIdx fs)).toNat (readFpReg s (regIdx ft)).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpReg { s with fcsr := c } (regIdx fd) (BitVec.ofNat 32 v))) := by
  rw [nmaddS_spec_raw s w fd fr fs ft hfetch hdecode hpb hcu hexec]
  dsimp only
  obtain ⟨out, h, e⟩ := three_stepsS s fd (r1 := f32Mul (envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
    (Op1 := binary32.MulSpec (envOf s.fcsr) (readFpReg s (regIdx fs)).toNat (readFpReg s (regIdx ft)).toNat)
    (r2 := fun p => f32Add (envOf s.fcsr) (readFpReg s (regIdx fr)) p)
    (Op2 := fun p => binary32.AddSpec (envOf s.fcsr) false (readFpReg s (regIdx fr)).toNat p)
    (r3 := f32Neg)
    (Op3 := fun q => binary32.SignOpSpec false q)
    (h1 := f32Mul_spec (envOf s.fcsr) _ _)
    (h2 := (fun p => f32Add_spec (envOf s.fcsr) (readFpReg s (regIdx fr)) p))
    (h3 := f32Neg_spec)
  exact ⟨out, by simpa [MaddSpec] using h, by rw [e]; cases out <;> rfl⟩

/-- **`NMSUB.S`** "as if separate" multiply, subtract and negate (NMSUB.fmt p.310; kind 3). -/
theorem nmsubS_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.nmsubS fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : FpOutcome Nat, MaddSpec binary32 (envOf s.fcsr) 3 s.fcsr (readFpReg s (regIdx fr)).toNat
        (readFpReg s (regIdx fs)).toNat (readFpReg s (regIdx ft)).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpReg { s with fcsr := c } (regIdx fd) (BitVec.ofNat 32 v))) := by
  rw [nmsubS_spec_raw s w fd fr fs ft hfetch hdecode hpb hcu hexec]
  dsimp only
  obtain ⟨out, h, e⟩ := three_stepsS s fd (r1 := f32Mul (envOf s.fcsr) (readFpReg s (regIdx fs)) (readFpReg s (regIdx ft)))
    (Op1 := binary32.MulSpec (envOf s.fcsr) (readFpReg s (regIdx fs)).toNat (readFpReg s (regIdx ft)).toNat)
    (r2 := fun p => f32Sub (envOf s.fcsr) p (readFpReg s (regIdx fr)))
    (Op2 := fun p => binary32.AddSpec (envOf s.fcsr) true p (readFpReg s (regIdx fr)).toNat)
    (r3 := f32Neg)
    (Op3 := fun q => binary32.SignOpSpec false q)
    (h1 := f32Mul_spec (envOf s.fcsr) _ _)
    (h2 := (fun p => f32Sub_spec (envOf s.fcsr) p (readFpReg s (regIdx fr))))
    (h3 := f32Neg_spec)
  exact ⟨out, by simpa [MaddSpec] using h, by rw [e]; cases out <;> rfl⟩

/-- **`MADD.D`** (kind 0). -/
theorem maddD_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.maddD fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : FpOutcome Nat, MaddSpec binary64 (envOf s.fcsr) 0 s.fcsr (readFpD s fr).toNat
        (readFpD s fs).toNat (readFpD s ft).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpD { s with fcsr := c } fd (BitVec.ofNat 64 v))) := by
  rw [maddD_spec_raw s w fd fr fs ft hfetch hdecode hpb hcu hexec]
  dsimp only
  obtain ⟨out, h, e⟩ := two_stepsD s fd (r1 := f64Mul (envOf s.fcsr) (readFpD s fs) (readFpD s ft))
    (Op1 := binary64.MulSpec (envOf s.fcsr) (readFpD s fs).toNat (readFpD s ft).toNat)
    (r2 := fun p => f64Add (envOf s.fcsr) p (readFpD s fr))
    (Op2 := fun p => binary64.AddSpec (envOf s.fcsr) false p (readFpD s fr).toNat)
    (h1 := f64Mul_spec (envOf s.fcsr) _ _)
    (h2 := (fun p => f64Add_spec (envOf s.fcsr) p (readFpD s fr)))
  exact ⟨out, by simpa [MaddSpec] using h, by rw [e]; cases out <;> rfl⟩

/-- **`MSUB.D`** (kind 1). -/
theorem msubD_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.msubD fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : FpOutcome Nat, MaddSpec binary64 (envOf s.fcsr) 1 s.fcsr (readFpD s fr).toNat
        (readFpD s fs).toNat (readFpD s ft).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpD { s with fcsr := c } fd (BitVec.ofNat 64 v))) := by
  rw [msubD_spec_raw s w fd fr fs ft hfetch hdecode hpb hcu hexec]
  dsimp only
  obtain ⟨out, h, e⟩ := two_stepsD s fd (r1 := f64Mul (envOf s.fcsr) (readFpD s fs) (readFpD s ft))
    (Op1 := binary64.MulSpec (envOf s.fcsr) (readFpD s fs).toNat (readFpD s ft).toNat)
    (r2 := fun p => f64Sub (envOf s.fcsr) p (readFpD s fr))
    (Op2 := fun p => binary64.AddSpec (envOf s.fcsr) true p (readFpD s fr).toNat)
    (h1 := f64Mul_spec (envOf s.fcsr) _ _)
    (h2 := (fun p => f64Sub_spec (envOf s.fcsr) p (readFpD s fr)))
  exact ⟨out, by simpa [MaddSpec] using h, by rw [e]; cases out <;> rfl⟩

/-- **`NMADD.D`** (kind 2). -/
theorem nmaddD_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.nmaddD fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : FpOutcome Nat, MaddSpec binary64 (envOf s.fcsr) 2 s.fcsr (readFpD s fr).toNat
        (readFpD s fs).toNat (readFpD s ft).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpD { s with fcsr := c } fd (BitVec.ofNat 64 v))) := by
  rw [nmaddD_spec_raw s w fd fr fs ft hfetch hdecode hpb hcu hexec]
  dsimp only
  obtain ⟨out, h, e⟩ := three_stepsD s fd (r1 := f64Mul (envOf s.fcsr) (readFpD s fs) (readFpD s ft))
    (Op1 := binary64.MulSpec (envOf s.fcsr) (readFpD s fs).toNat (readFpD s ft).toNat)
    (r2 := fun p => f64Add (envOf s.fcsr) (readFpD s fr) p)
    (Op2 := fun p => binary64.AddSpec (envOf s.fcsr) false (readFpD s fr).toNat p)
    (r3 := f64Neg)
    (Op3 := fun q => binary64.SignOpSpec false q)
    (h1 := f64Mul_spec (envOf s.fcsr) _ _)
    (h2 := (fun p => f64Add_spec (envOf s.fcsr) (readFpD s fr) p))
    (h3 := f64Neg_spec)
  exact ⟨out, by simpa [MaddSpec] using h, by rw [e]; cases out <;> rfl⟩

/-- **`NMSUB.D`** (kind 3). -/
theorem nmsubD_separate (s : State) (w fd fr fs ft : W32) (hfetch : readMemWord s s.pc = some w)
    (hdecode : decode w = some (.nmsubD fd fr fs ft)) (hpb : s.pendingBranch = none)
    (hcu : cu1Enabled s = true) (hexec : executesInstr s = true) :
    ∃ out : FpOutcome Nat, MaddSpec binary64 (envOf s.fcsr) 3 s.fcsr (readFpD s fr).toNat
        (readFpD s fs).toNat (readFpD s ft).toNat out ∧
      step s = timerTick (match out with
        | .trap c => takeException { s with fcsr := c } excCodeFPE
        | .done c v => mkNext s (writeFpD { s with fcsr := c } fd (BitVec.ofNat 64 v))) := by
  rw [nmsubD_spec_raw s w fd fr fs ft hfetch hdecode hpb hcu hexec]
  dsimp only
  obtain ⟨out, h, e⟩ := three_stepsD s fd (r1 := f64Mul (envOf s.fcsr) (readFpD s fs) (readFpD s ft))
    (Op1 := binary64.MulSpec (envOf s.fcsr) (readFpD s fs).toNat (readFpD s ft).toNat)
    (r2 := fun p => f64Sub (envOf s.fcsr) p (readFpD s fr))
    (Op2 := fun p => binary64.AddSpec (envOf s.fcsr) true p (readFpD s fr).toNat)
    (r3 := f64Neg)
    (Op3 := fun q => binary64.SignOpSpec false q)
    (h1 := f64Mul_spec (envOf s.fcsr) _ _)
    (h2 := (fun p => f64Sub_spec (envOf s.fcsr) p (readFpD s fr)))
    (h3 := f64Neg_spec)
  exact ⟨out, by simpa [MaddSpec] using h, by rw [e]; cases out <;> rfl⟩
