import Semantics.FpOpsCorrectIEEE
import Semantics.Specs.FpuArith

/-!
# FpOpsCorrectStep — the multiply-add family "as if separate instructions"

MD00086 Vol II-A Rev 6.06, MADD.fmt (p.256): "The results and flags are as if separate floating-point
multiply and add instructions were executed"; MSUB.fmt p.287, NMADD.fmt p.308 ("... and negate"),
NMSUB.fmt p.310. `MaddSpec` (`Semantics/FpOpsSpec.lean`) states that reading: each step an operation
meeting its own reference (`MulSpec`, `AddSpec`, `SignOpSpec`), each its own FCSR update and trap
check (`FcsrSpec`). The theorems below prove that `step` on each of the eight instructions produces
the state of an outcome `MaddSpec` allows: the Floating-Point exception with the FCSR of the
trapping step, or `fd` written with the final value and the FCSR of the last step.

Also: `fpThen_spec`, `fpFinishS_spec` — one step of `step`'s FP completion is the outcome of
`OpStep` for the FCSR reference `FcsrSpec`.
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

section generic
variable (s : State) (fd : W32)

theorem finishS_outcome (r : BitVec 32 × Flags) :
    fpFinishS s fd r = (match outcomeOf s.fcsr r with
      | .trap c => takeException { s with fcsr := c } excCodeFPE
      | .done c v => mkNext s (writeFpReg { s with fcsr := c } (regIdx fd) (BitVec.ofNat 32 v))) := by
  rw [fpFinishS_unfold]; simp only [outcomeOf]; split <;> simp

theorem finishD_outcome (r : BitVec 64 × Flags) :
    fpFinishD s fd r = (match outcomeOf s.fcsr r with
      | .trap c => takeException { s with fcsr := c } excCodeFPE
      | .done c v => mkNext s (writeFpD { s with fcsr := c } fd (BitVec.ofNat 64 v))) := by
  rw [fpFinishD_unfold]; simp only [outcomeOf]; split <;> simp

theorem then_outcome {w : Nat} (r : BitVec w × Flags) (k : State → BitVec w → State) {β : Type}
    (g : State → FpOutcome β → State) (P : BitVec 32 → Nat → FpOutcome β → Prop)
    (hk : ∀ c (p : BitVec w), ∃ out, P c p.toNat out ∧ k { s with fcsr := c } p = g { s with fcsr := c } out)
    (hg : ∀ c out, g { s with fcsr := c } out = g s out)
    (htrap : ∀ c, g s (.trap c) = takeException { s with fcsr := c } excCodeFPE) :
    ∃ out, OpThen (outcomeOf s.fcsr r) P out ∧ fpThen s r k = g s out := by
  rw [fpThen_unfold]
  cases ht : (fpUpdate s.fcsr r.2).2
  · obtain ⟨out, h1, h2⟩ := hk (fpUpdate s.fcsr r.2).1 r.1
    refine ⟨out, ?_, ?_⟩
    · simp only [outcomeOf, ht, Bool.false_eq_true, ite_false, OpThen]; exact h1
    · simp only [Bool.false_eq_true, ite_false]; rw [h2, hg]
  · refine ⟨.trap (fpUpdate s.fcsr r.2).1, ?_, ?_⟩
    · simp [outcomeOf, ht, OpThen]
    · simp only [ite_true]; rw [htrap]

end generic

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

/-- Two operations, the second completing to the single `fd`. -/
theorem two_stepsS (s : State) (fd : W32) (r1 : BitVec 32 × Flags) (r2 : BitVec 32 → BitVec 32 × Flags)
    (Op1 : Nat × Flags → Prop) (Op2 : Nat → Nat × Flags → Prop) (h1 : Op1 (r1.1.toNat, r1.2))
    (h2 : ∀ p : BitVec 32, Op2 p.toNat ((r2 p).1.toNat, (r2 p).2)) :
    ∃ out, (∃ o1, OpStep Op1 s.fcsr o1 ∧ OpThen o1 (fun c1 p out1 => OpStep (Op2 p) c1 out1) out) ∧
      fpThen s r1 (fun s1 p => fpFinishS s1 fd (r2 p)) = outcomeStateS s fd out := by
  obtain ⟨out, h, e⟩ := then_outcome s r1 (fun s1 p => fpFinishS s1 fd (r2 p)) (fun st o => outcomeStateS st fd o) (fun c1 p out1 => OpStep (Op2 p) c1 out1)
    (fun c p => ⟨outcomeOf c (r2 p), opStep_of c (r2 p) (h2 p), by
      rw [finishS_outcome]; cases outcomeOf c (r2 p) <;> rfl⟩)
    (fun c o => outcomeStateS_fcsr s fd c o) (fun _ => rfl)
  exact ⟨out, ⟨_, opStep_of s.fcsr r1 h1, h⟩, e⟩

/-- Two operations, the second completing to the double `fd`. -/
theorem two_stepsD (s : State) (fd : W32) (r1 : BitVec 64 × Flags) (r2 : BitVec 64 → BitVec 64 × Flags)
    (Op1 : Nat × Flags → Prop) (Op2 : Nat → Nat × Flags → Prop) (h1 : Op1 (r1.1.toNat, r1.2))
    (h2 : ∀ p : BitVec 64, Op2 p.toNat ((r2 p).1.toNat, (r2 p).2)) :
    ∃ out, (∃ o1, OpStep Op1 s.fcsr o1 ∧ OpThen o1 (fun c1 p out1 => OpStep (Op2 p) c1 out1) out) ∧
      fpThen s r1 (fun s1 p => fpFinishD s1 fd (r2 p)) = outcomeStateD s fd out := by
  obtain ⟨out, h, e⟩ := then_outcome s r1 (fun s1 p => fpFinishD s1 fd (r2 p)) (fun st o => outcomeStateD st fd o) (fun c1 p out1 => OpStep (Op2 p) c1 out1)
    (fun c p => ⟨outcomeOf c (r2 p), opStep_of c (r2 p) (h2 p), by
      rw [finishD_outcome]; cases outcomeOf c (r2 p) <;> rfl⟩)
    (fun c o => outcomeStateD_fcsr s fd c o) (fun _ => rfl)
  exact ⟨out, ⟨_, opStep_of s.fcsr r1 h1, h⟩, e⟩

/-- Three operations, the third completing to the single `fd`. -/
theorem three_stepsS (s : State) (fd : W32) (r1 : BitVec 32 × Flags) (r2 : BitVec 32 → BitVec 32 × Flags)
    (r3 : BitVec 32 → BitVec 32 × Flags)
    (Op1 : Nat × Flags → Prop) (Op2 : Nat → Nat × Flags → Prop) (Op3 : Nat → Nat × Flags → Prop)
    (h1 : Op1 (r1.1.toNat, r1.2)) (h2 : ∀ p : BitVec 32, Op2 p.toNat ((r2 p).1.toNat, (r2 p).2))
    (h3 : ∀ q : BitVec 32, Op3 q.toNat ((r3 q).1.toNat, (r3 q).2)) :
    ∃ out, (∃ o1, OpStep Op1 s.fcsr o1 ∧ OpThen o1 (fun c1 p out1 =>
        ∃ o2, OpStep (Op2 p) c1 o2 ∧ OpThen o2 (fun c2 q out2 => OpStep (Op3 q) c2 out2) out1) out) ∧
      fpThen s r1 (fun s1 p => fpThen s1 (r2 p) (fun s2 q => fpFinishS s2 fd (r3 q))) =
        outcomeStateS s fd out := by
  obtain ⟨out, h, e⟩ := then_outcome s r1 (fun s1 p => fpThen s1 (r2 p) (fun s2 q => fpFinishS s2 fd (r3 q))) (fun st o => outcomeStateS st fd o)
    (fun c1 p out1 => ∃ o2, OpStep (Op2 p) c1 o2 ∧ OpThen o2 (fun c2 q out2 => OpStep (Op3 q) c2 out2) out1)
    (fun c p => by
      obtain ⟨out1, ha, hb⟩ := two_stepsS { s with fcsr := c } fd (r2 p) r3 (Op2 p.toNat) Op3 (h2 p) h3
      exact ⟨out1, ha, hb.trans (outcomeStateS_fcsr s fd c out1)⟩)
    (fun c o => outcomeStateS_fcsr s fd c o) (fun _ => rfl)
  exact ⟨out, ⟨_, opStep_of s.fcsr r1 h1, h⟩, e⟩

/-- Three operations, the third completing to the double `fd`. -/
theorem three_stepsD (s : State) (fd : W32) (r1 : BitVec 64 × Flags) (r2 : BitVec 64 → BitVec 64 × Flags)
    (r3 : BitVec 64 → BitVec 64 × Flags)
    (Op1 : Nat × Flags → Prop) (Op2 : Nat → Nat × Flags → Prop) (Op3 : Nat → Nat × Flags → Prop)
    (h1 : Op1 (r1.1.toNat, r1.2)) (h2 : ∀ p : BitVec 64, Op2 p.toNat ((r2 p).1.toNat, (r2 p).2))
    (h3 : ∀ q : BitVec 64, Op3 q.toNat ((r3 q).1.toNat, (r3 q).2)) :
    ∃ out, (∃ o1, OpStep Op1 s.fcsr o1 ∧ OpThen o1 (fun c1 p out1 =>
        ∃ o2, OpStep (Op2 p) c1 o2 ∧ OpThen o2 (fun c2 q out2 => OpStep (Op3 q) c2 out2) out1) out) ∧
      fpThen s r1 (fun s1 p => fpThen s1 (r2 p) (fun s2 q => fpFinishD s2 fd (r3 q))) =
        outcomeStateD s fd out := by
  obtain ⟨out, h, e⟩ := then_outcome s r1 (fun s1 p => fpThen s1 (r2 p) (fun s2 q => fpFinishD s2 fd (r3 q))) (fun st o => outcomeStateD st fd o)
    (fun c1 p out1 => ∃ o2, OpStep (Op2 p) c1 o2 ∧ OpThen o2 (fun c2 q out2 => OpStep (Op3 q) c2 out2) out1)
    (fun c p => by
      obtain ⟨out1, ha, hb⟩ := two_stepsD { s with fcsr := c } fd (r2 p) r3 (Op2 p.toNat) Op3 (h2 p) h3
      exact ⟨out1, ha, hb.trans (outcomeStateD_fcsr s fd c out1)⟩)
    (fun c o => outcomeStateD_fcsr s fd c o) (fun _ => rfl)
  exact ⟨out, ⟨_, opStep_of s.fcsr r1 h1, h⟩, e⟩

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
