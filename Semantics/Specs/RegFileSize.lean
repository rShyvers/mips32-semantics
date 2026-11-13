import Lean.Elab.Tactic
import Semantics.Specs.Lemmas

/-!
# RegFileSize — `step` and `run` keep both register files at 32 entries

Several theorems carry a side condition `s.regs.size = 32` or `s.fpRegs.size = 32` (reading a
register back after writing it needs the write to be in bounds: `writeReg_reads_back`,
`fpCompletesS_ok`, `jal_sets_ra`, …). This file shows the side condition is an invariant:
`initialState` satisfies it, and `step` — hence `run` — never changes the size of `regs` or
`fpRegs`, for any instruction.

The proof has the same structure as `execInstr_zeroKept` (`Invariants.lean`): every way
`execInstr` builds a result goes through `writeReg` / `writeFpReg` / `writeFpD` (an in-place
`Array.set!`, which keeps the size), `writeMem*` or a `{ s with … }` update of other fields
(which do not touch either array). `SizesKept`, the `sizesKept_*` lemmas, `sk_fwd` and `sk_simp`
are proof devices; the statements to read are `step_preserves_regfile_sizes`,
`run_preserves_regfile_sizes`, `initialState_regfile_sizes` and the two `_wellFormed` corollaries.

## Theorems in this file
-/

set_option maxRecDepth 4000

/-- `SizesKept s r`: if the step result `r` is a next state, its `regs` and `fpRegs` have the
same sizes as those of `s`. (A halt satisfies this vacuously.) Proof device. -/
def SizesKept (s : State) (r : StepResult) : Prop :=
  ∀ s', r = StepResult.next s' → s'.regs.size = s.regs.size ∧ s'.fpRegs.size = s.fpRegs.size

/-! ## The state primitives keep the sizes -/

theorem writeReg_regs_size (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).regs.size = s.regs.size := by
  unfold writeReg; split
  · rfl
  · simp

theorem writeFpReg_fpRegs_size (s : State) (i : Fin 32) (v : W32) :
    (writeFpReg s i v).fpRegs.size = s.fpRegs.size := by
  unfold writeFpReg; simp

theorem writeFpReg_regs' (s : State) (i : Fin 32) (v : W32) :
    (writeFpReg s i v).regs = s.regs := rfl

theorem writeFpD_regs' (s : State) (f : W32) (v : BitVec 64) :
    (writeFpD s f v).regs = s.regs := rfl

theorem writeFpD_fpRegs_size (s : State) (f : W32) (v : BitVec 64) :
    (writeFpD s f v).fpRegs.size = s.fpRegs.size := by
  unfold writeFpD; rw [writeFpReg_fpRegs_size, writeFpReg_fpRegs_size]

theorem writeMemWord_fpRegs (s stored : State) (addr v : W32)
    (h : writeMemWord s addr v = some stored) : stored.fpRegs = s.fpRegs := by
  unfold writeMemWord at h
  split at h
  · cases h
  · injection h with h'
    rw [← h']

theorem writeMemHalf_fpRegs (s stored : State) (addr v : W32)
    (h : writeMemHalf s addr v = some stored) : stored.fpRegs = s.fpRegs := by
  unfold writeMemHalf at h
  split at h
  · cases h
  · injection h with h'
    rw [← h']

theorem writeMemByte_fpRegs (s stored : State) (addr : W32) (v : UInt8)
    (h : writeMemByte s addr v = some stored) : stored.fpRegs = s.fpRegs := by
  unfold writeMemByte at h
  injection h with h'
  rw [← h']

theorem writeMemByte_getD_regs' (s d : State) (a : W32) (v : UInt8) :
    ((writeMemByte s a v).getD d).regs = s.regs := rfl

theorem writeMemByte_getD_fpRegs (s d : State) (a : W32) (v : UInt8) :
    ((writeMemByte s a v).getD d).fpRegs = s.fpRegs := rfl

theorem advance_regs' (orig result : State) : (advance orig result).regs = result.regs := by
  unfold advance; split <;> rfl

theorem advance_fpRegs (orig result : State) : (advance orig result).fpRegs = result.fpRegs := by
  unfold advance; split <;> rfl

/-! ## The result shapes of `execInstr` -/

theorem sizesKept_halt (s : State) (h : HaltReason) : SizesKept s (.halt h) ↔ True :=
  iff_true_intro (fun _ h' => by cases h')

theorem sizesKept_next (s r : State) :
    SizesKept s (.next r) ↔ (r.regs.size = s.regs.size ∧ r.fpRegs.size = s.fpRegs.size) :=
  ⟨fun h => h r rfl, fun h _ h' => by cases h'; exact h⟩

theorem sizesKept_mkNext (s r : State) :
    SizesKept s (mkNext s r) ↔ (r.regs.size = s.regs.size ∧ r.fpRegs.size = s.fpRegs.size) := by
  unfold mkNext
  rw [sizesKept_next, advance_regs', advance_fpRegs]

theorem sizesKept_takeException (s : State) (c : W32) :
    SizesKept s (takeException s c) ↔ True :=
  iff_true_intro (fun _ h' => by cases h'; exact ⟨rfl, rfl⟩)

/-- An exception taken from a state `t` that differs from `s` (the FP paths record FCSR
first). -/
theorem sizesKept_takeException' (s t : State) (c : W32) :
    SizesKept s (takeException t c) ↔ (t.regs.size = s.regs.size ∧ t.fpRegs.size = s.fpRegs.size) :=
  ⟨fun h => h (exceptionEntry t c) rfl, fun h _ h' => by cases h'; exact h⟩

theorem sizesKept_takeAddressException (s : State) (c a : W32) :
    SizesKept s (takeAddressException s c a) ↔ True :=
  iff_true_intro (fun _ h' => by cases h'; exact ⟨rfl, rfl⟩)

theorem sizesKept_exceptionEntry (s : State) (c ce : W32) :
    SizesKept s (StepResult.next (exceptionEntry s c ce)) ↔ True :=
  iff_true_intro (fun _ h' => by cases h'; exact ⟨rfl, rfl⟩)

theorem sizesKept_takeCoprocessorUnusable (s : State) :
    SizesKept s (takeCoprocessorUnusable s) ↔ True :=
  iff_true_intro (fun _ h' => by cases h'; exact ⟨rfl, rfl⟩)

theorem sizesKept_fpFinishS (s : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags) :
    SizesKept s (fpFinishS s fd r) ↔ True :=
  iff_true_intro (by
    intro s' h
    unfold fpFinishS at h
    dsimp only at h
    split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h
      refine ⟨?_, ?_⟩
      · show (advance _ _).regs.size = _
        rw [advance_regs']; rfl
      · show (advance _ _).fpRegs.size = _
        rw [advance_fpRegs, writeFpReg_fpRegs_size])

theorem sizesKept_fpFinishD (s : State) (fd : W32) (r : BitVec 64 × Mips.Fp.Flags) :
    SizesKept s (fpFinishD s fd r) ↔ True :=
  iff_true_intro (by
    intro s' h
    unfold fpFinishD at h
    dsimp only at h
    split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h
      refine ⟨?_, ?_⟩
      · show (advance _ _).regs.size = _
        rw [advance_regs']; rfl
      · show (advance _ _).fpRegs.size = _
        rw [advance_fpRegs, writeFpD_fpRegs_size])

theorem sizesKept_fpFinishCmp (s : State) (cc : W32) (r : Bool × Mips.Fp.Flags) :
    SizesKept s (fpFinishCmp s cc r) ↔ True :=
  iff_true_intro (by
    intro s' h
    unfold fpFinishCmp at h
    dsimp only at h
    split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h
      refine ⟨?_, ?_⟩
      · show (advance _ _).regs.size = _
        rw [advance_regs']
      · show (advance _ _).fpRegs.size = _
        rw [advance_fpRegs])

/-- Forward step for the tactic loop below: for every hypothesis
`writeMem{Byte,Half,Word} s a v = some s'` in the context, add `s'.regs = s.regs` and
`s'.fpRegs = s.fpRegs`. -/
elab "sk_fwd" : tactic => Lean.Elab.Tactic.withMainContext do
  for d in (← Lean.getLCtx) do
    if d.isImplementationDetail then continue
    for lem in [``writeMemByte_regs, ``writeMemHalf_regs, ``writeMemWord_regs,
                ``writeMemByte_fpRegs, ``writeMemHalf_fpRegs, ``writeMemWord_fpRegs] do
      try
        let pf ← Lean.Meta.mkAppOptM lem #[none, none, none, none, some d.toExpr]
        let ty ← Lean.Meta.inferType pf
        Lean.Elab.Tactic.liftMetaTactic fun g => do
          let (_, g) ← (← g.assert `hsz ty pf).intro1
          return [g]
      catch _ => pure ()

/-- Simp set for the tactic loop below: reduce a `SizesKept` goal about one of `execInstr`'s
result shapes to statements about `regs.size` / `fpRegs.size`, and push those through every
state-update primitive (plus the equations `sk_fwd` put in the context). -/
macro "sk_simp" : tactic => `(tactic|
  simp only [sizesKept_halt, sizesKept_next, sizesKept_mkNext, sizesKept_takeException,
    sizesKept_takeException', sizesKept_takeAddressException, sizesKept_takeCoprocessorUnusable,
    sizesKept_fpFinishS, sizesKept_fpFinishD, sizesKept_fpFinishCmp,
    writeReg_regs_size, writeReg_proj_fpRegs, writeFpReg_regs', writeFpReg_fpRegs_size,
    writeFpD_regs', writeFpD_fpRegs_size, writeMemByte_getD_regs', writeMemByte_getD_fpRegs,
    and_self, *])

-- ~180 constructors through one generic tactic loop
set_option maxHeartbeats 4000000 in
/-- **No instruction changes the size of `regs` or `fpRegs`**, in any state (including one with
a pending delay-slot transfer). Proved structurally, not by a per-instruction case list. -/
theorem execInstr_sizesKept (s : State) (instr : Instruction) :
    SizesKept s (execInstr s instr) := by
  unfold execInstr
  split
  · exact (sizesKept_halt _ _).mpr trivial
  · split
    · exact (sizesKept_takeCoprocessorUnusable _).mpr trivial
    · unfold execBody
      cases instr <;> dsimp only <;> repeat' (first | (sk_fwd; sk_simp; done) | split)

/-! ## Statements -/

/-- **`step` never changes the size of either register file**, for any program, state and
instruction (including every exception path). -/
theorem step_preserves_regfile_sizes (p : Program) (s s' : State)
    (hstep : step p s = StepResult.next s') :
    s'.regs.size = s.regs.size ∧ s'.fpRegs.size = s.fpRegs.size := by
  unfold step at hstep
  split at hstep
  · split at hstep
    · exact (sizesKept_takeAddressException s _ _).mpr trivial _ hstep
    · split at hstep <;> cases hstep
  · split at hstep
    · split at hstep
      · exact (sizesKept_takeCoprocessorUnusable s).mpr trivial _ hstep
      · split at hstep
        · exact (sizesKept_exceptionEntry s _ _).mpr trivial _ hstep
        · exact (sizesKept_takeException s _).mpr trivial _ hstep
    · exact execInstr_sizesKept _ _ _ hstep

/-- **Well-formedness is preserved by `step`**: if both register files have 32 entries before a
step, they have 32 entries after it. This discharges the `hsize` / `hsize32` side conditions of
the per-instruction theorems along any execution that starts well-formed. -/
theorem step_preserves_wellFormed (p : Program) (s s' : State) (hwf : s.RegFilesWF)
    (hstep : step p s = StepResult.next s') : s'.RegFilesWF := by
  obtain ⟨h1, h2⟩ := step_preserves_regfile_sizes p s s' hstep
  exact ⟨h1.trans hwf.1, h2.trans hwf.2⟩

/-- `run`'s inner loop keeps the sizes: each iteration is one `step`. -/
theorem run_go_preserves_regfile_sizes (p : Program) (fuel : Nat) (s : State) (steps : Nat) :
    (run.go p fuel s steps).finalState.regs.size = s.regs.size ∧
      (run.go p fuel s steps).finalState.fpRegs.size = s.fpRegs.size := by
  induction fuel generalizing s steps with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    unfold run.go
    split
    · exact ⟨rfl, rfl⟩
    · next s1 h =>
      obtain ⟨h1, h2⟩ := step_preserves_regfile_sizes p s s1 h
      obtain ⟨i1, i2⟩ := ih s1 (steps + 1)
      exact ⟨i1.trans h1, i2.trans h2⟩

/-- **Whole-run invariant: the final state of any run has register files of the same sizes as
the start state.** -/
theorem run_preserves_regfile_sizes (p : Program) (s₀ : State) (maxSteps : Nat) :
    (run p s₀ maxSteps).finalState.regs.size = s₀.regs.size ∧
      (run p s₀ maxSteps).finalState.fpRegs.size = s₀.fpRegs.size :=
  run_go_preserves_regfile_sizes p maxSteps s₀ 0

/-- **`initialState` is well-formed**: 32 general registers and 32 FP registers. -/
theorem initialState_regfile_sizes (pc : W32) : (initialState pc).RegFilesWF := by
  constructor
  · simp [initialState]
  · simp [initialState]

/-- **Every run from a well-formed state ends in a well-formed state.** -/
theorem run_preserves_wellFormed (p : Program) (s₀ : State) (maxSteps : Nat) (hwf : s₀.RegFilesWF) :
    (run p s₀ maxSteps).finalState.RegFilesWF := by
  obtain ⟨h1, h2⟩ := run_preserves_regfile_sizes p s₀ maxSteps
  exact ⟨h1.trans hwf.1, h2.trans hwf.2⟩

/-- **Every state reached by `run` from `initialState` is well-formed.** -/
theorem run_initialState_wellFormed (p : Program) (pc : W32) (maxSteps : Nat) :
    (run p (initialState pc) maxSteps).finalState.RegFilesWF :=
  run_preserves_wellFormed p _ maxSteps (initialState_regfile_sizes pc)
