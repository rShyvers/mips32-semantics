import Lean.Elab.Tactic
import Semantics.Specs.Lemmas

/-!
# Invariants — `$zero` is preserved by `step` and `run`

`step_preserves_zero_register` is proved structurally for every instruction at once;
`ZeroKept`, the `zeroKept_*` lemmas and the `zk_fwd`/`zk_simp` tactics are its proof devices.

## Theorems in this file (25)

  `writeReg_preserves_zero_slot` `writeReg_regs_zero` `writeFpReg_regs` `writeFpD_regs`
  `writeMemByte_getD_regs` `advance_regs` `zeroKept_halt` `zeroKept_next` `zeroKept_mkNext`
  `zeroKept_takeException` `zeroKept_takeException'` `zeroKept_takeAddressException`
  `zeroKept_exceptionEntry` `zeroKept_takeCoprocessorUnusable` `zeroKept_fpFinishS`
  `zeroKept_fpFinishD` `zeroKept_fpFinishCmp` `execInstr_zeroKept` `step_preserves_zero_register`
  `step_zero_register_reads_zero` `run_go_preserves_zero_register` `run_preserves_zero_register`
  `run_initialState_zero_register` `zero_write_not_observable`
  `step_preserves_zero_register_nontrivial`
-/

set_option maxRecDepth 4000

/-- **`$zero` is never actually written.** Writing any value to any register
never changes what register `0` reads back: either the write targets `0`
itself (ignored outright, INSTRUCTION-REF Global rule §2) or it targets a
different register, which cannot disturb slot `0`. This is the building
block for "`$zero` always reads `0`" as a full-run invariant: every write in
the simulator goes through `writeReg`, so register `0` can never pick up a
nonzero value no matter how many steps run, as long as it started at `0`
(which `initialState` guarantees — see `State.lean`). -/
theorem writeReg_preserves_zero_slot (s : State) (i : Fin 32) (v : W32) :
    readReg (writeReg s i v) 0 = readReg s 0 := by
  unfold writeReg readReg
  split
  · rfl
  · next h =>
    have hne : i ≠ (0 : Fin 32) := by
      intro heq; exact h (by simp [heq])
    simp [Array.set!, Array.getD_eq_getD_getElem?, hne]

/-! ## `$zero` is preserved by every step — structural proof

The proof below does **not** go instruction by instruction. It shows that
the only ways `execInstr` (`step`'s dispatch) ever builds a
`StepResult` — `mkNext`, `takeException`, a literal `StepResult.next`/
`StepResult.halt` — keep register slot `0` intact as long as the result
state's register file was produced from `s`'s by `writeReg` (which ignores
writes to register `0`), `writeFpReg`/`writeFpD`/`writeMem*` (which
never touch `regs`), or a `{ s with … }` update of non-`regs` fields. One
generic tactic loop (`split` on every `if`/`match`, then simplify with
those facts) then discharges every `Instruction` constructor at once.

Because the loop is generic, **an instruction added to `Instruction`/
`execInstr` later is covered automatically** provided its register writes go
through `writeReg` — no new case is needed here. If a future instruction
wrote `regs` some other way, `execInstr_zeroKept` would fail to compile,
which is the desired behavior (the invariant would need a real argument).

`ZeroKept`, the `zeroKept_*` lemmas, `zk_fwd` and `zk_simp` are proof devices; the statements
to read start at `step_preserves_zero_register`. -/

/-- `ZeroKept s r`: if the step result `r` is a next state, register `0`
reads the same there as in `s`. (A halt satisfies this vacuously.) -/
def ZeroKept (s : State) (r : StepResult) : Prop :=
  ∀ s', r = StepResult.next s' → readReg s' 0 = readReg s 0

/-- `writeReg_preserves_zero_slot`, restated on the raw `regs` array (the
normal form the `zk_simp` simp set below works in). -/
theorem writeReg_regs_zero (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).regs.getD 0 0#32 = s.regs.getD 0 0#32 :=
  writeReg_preserves_zero_slot s i v

/-- `writeFpReg` only touches `fpRegs`. -/
theorem writeFpReg_regs (s : State) (i : Fin 32) (v : W32) :
    (writeFpReg s i v).regs = s.regs := rfl

/-- `Step.lean`'s `writeFpD` (two `writeFpReg` calls) only touches
`fpRegs`. -/
theorem writeFpD_regs (s : State) (f : W32) (v : BitVec 64) :
    (writeFpD s f v).regs = s.regs := rfl

/-- `(writeMemByte s a v).getD d` (the shape `swl`/`swr` use) keeps `regs`. -/
theorem writeMemByte_getD_regs (s d : State) (a : W32) (v : UInt8) :
    ((writeMemByte s a v).getD d).regs = s.regs := rfl

/-- `Step.lean`'s `advance` (delay-slot resolution / `pc + 4`) only
touches `pc` and `pendingBranch`. -/
theorem advance_regs (orig result : State) : (advance orig result).regs = result.regs := by
  unfold advance; split <;> rfl

theorem zeroKept_halt (s : State) (h : HaltReason) : ZeroKept s (.halt h) ↔ True :=
  iff_true_intro (fun _ h' => by cases h')

theorem zeroKept_next (s r : State) :
    ZeroKept s (.next r) ↔ r.regs.getD 0 0#32 = s.regs.getD 0 0#32 :=
  ⟨fun h => h r rfl, fun h _ h' => by cases h'; exact h⟩

theorem zeroKept_mkNext (s r : State) :
    ZeroKept s (mkNext s r) ↔ r.regs.getD 0 0#32 = s.regs.getD 0 0#32 := by
  unfold mkNext
  rw [zeroKept_next, advance_regs]

theorem zeroKept_takeException (s : State) (c : W32) :
    ZeroKept s (takeException s c) ↔ True :=
  iff_true_intro (fun _ h' => by cases h'; rfl)

/-- An exception taken from a state `t` that differs from `s` outside `regs`
(the FP paths record FCSR first). -/
theorem zeroKept_takeException' (s t : State) (c : W32) :
    ZeroKept s (takeException t c) ↔ t.regs.getD 0 0#32 = s.regs.getD 0 0#32 :=
  ⟨fun h => h (exceptionEntry t c) rfl, fun h _ h' => by cases h'; exact h⟩

theorem zeroKept_takeAddressException (s : State) (c a : W32) :
    ZeroKept s (takeAddressException s c a) ↔ True :=
  iff_true_intro (fun _ h' => by cases h'; rfl)

theorem zeroKept_exceptionEntry (s : State) (c ce : W32) :
    ZeroKept s (StepResult.next (exceptionEntry s c ce)) ↔ True :=
  iff_true_intro (fun _ h' => by cases h'; rfl)

theorem zeroKept_takeCoprocessorUnusable (s : State) :
    ZeroKept s (takeCoprocessorUnusable s) ↔ True :=
  iff_true_intro (fun _ h' => by cases h'; rfl)

/-- The three ways an FP computational instruction completes
(`fpFinishS`/`fpFinishD`/`fpFinishCmp`: Floating Point exception, or FCSR
update plus an FP-register / condition-code write) never touch `regs`. -/
theorem zeroKept_fpFinishS (s : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags) :
    ZeroKept s (fpFinishS s fd r) ↔ True :=
  iff_true_intro (by
    intro s' h
    unfold fpFinishS at h
    dsimp only at h
    split at h
    · cases h; rfl
    · cases h
      show (advance _ _).regs.getD 0 0#32 = _
      rw [advance_regs]; rfl)

theorem zeroKept_fpFinishD (s : State) (fd : W32) (r : BitVec 64 × Mips.Fp.Flags) :
    ZeroKept s (fpFinishD s fd r) ↔ True :=
  iff_true_intro (by
    intro s' h
    unfold fpFinishD at h
    dsimp only at h
    split at h
    · cases h; rfl
    · cases h
      show (advance _ _).regs.getD 0 0#32 = _
      rw [advance_regs]; rfl)

theorem zeroKept_fpFinishCmp (s : State) (cc : W32) (r : Bool × Mips.Fp.Flags) :
    ZeroKept s (fpFinishCmp s cc r) ↔ True :=
  iff_true_intro (by
    intro s' h
    unfold fpFinishCmp at h
    dsimp only at h
    split at h
    · cases h; rfl
    · cases h
      show (advance _ _).regs.getD 0 0#32 = _
      rw [advance_regs]; rfl)

/-- Forward step for the tactic loop below: for every hypothesis of the
form `writeMem{Byte,Half,Word} s a v = some s'` in the context (these
appear when `split` case-splits a store instruction's `match` on the write
result), add the fact `s'.regs = s.regs`. -/
elab "zk_fwd" : tactic => Lean.Elab.Tactic.withMainContext do
  for d in (← Lean.getLCtx) do
    if d.isImplementationDetail then continue
    for lem in [``writeMemByte_regs, ``writeMemHalf_regs, ``writeMemWord_regs] do
      try
        let pf ← Lean.Meta.mkAppOptM lem #[none, none, none, none, some d.toExpr]
        let ty ← Lean.Meta.inferType pf
        Lean.Elab.Tactic.liftMetaTactic fun g => do
          let (_, g) ← (← g.assert `hregs ty pf).intro1
          return [g]
      catch _ => pure ()

/-- Simp set for the tactic loop below: reduce a `ZeroKept` goal about one
of `execInstr`'s result shapes to a statement about `regs[0]`, and push
that through every state-update primitive (plus any `regs` equations
`zk_fwd` put in the context). -/
macro "zk_simp" : tactic => `(tactic|
  simp only [zeroKept_halt, zeroKept_next, zeroKept_mkNext, zeroKept_takeException,
    zeroKept_takeException', zeroKept_takeAddressException, zeroKept_takeCoprocessorUnusable, zeroKept_fpFinishS,
    zeroKept_fpFinishD, zeroKept_fpFinishCmp,
    writeReg_regs_zero, writeFpReg_regs, writeFpD_regs, writeMemByte_getD_regs, *])

-- ~180 constructors through one generic tactic loop
set_option maxHeartbeats 4000000 in
/-- **Every instruction keeps `$zero`.** `execInstr` (the dispatch
`step` calls after fetch/decode) never changes what register `0` reads,
for any instruction and any state — including states with a pending
delay-slot transfer. Proved structurally (see the section comment above),
not by a per-instruction case list. -/
theorem execInstr_zeroKept (s : State) (instr : Instruction) :
    ZeroKept s (execInstr s instr) := by
  unfold execInstr
  split
  · exact (zeroKept_halt _ _).mpr trivial
  · split
    · exact (zeroKept_takeCoprocessorUnusable _).mpr trivial
    · unfold execBody
      cases instr <;> dsimp only <;> repeat' (first | (zk_fwd; zk_simp; done) | split)

/-- **Global invariant: `$zero` is never changed by a step.** If `step`
produces a next state, register `0` reads the same thing after the step as
before — for **every** instruction, with no side conditions (INSTRUCTION-REF
Global rule 2, "writes to `$zero` are a no-op"). Proof: `step` is
fetch/decode followed by `execInstr`; see `execInstr_zeroKept`. -/
theorem step_preserves_zero_register (p : Program) (s s' : State)
    (hstep : step p s = StepResult.next s') : readReg s' 0 = readReg s 0 := by
  unfold step at hstep
  split at hstep
  · split at hstep
    · exact (zeroKept_takeAddressException s _ _).mpr trivial _ hstep
    · split at hstep <;> cases hstep
  · split at hstep
    · split at hstep
      · exact (zeroKept_takeCoprocessorUnusable s).mpr trivial _ hstep
      · split at hstep
        · exact (zeroKept_exceptionEntry s _ _).mpr trivial _ hstep
        · exact (zeroKept_takeException s _).mpr trivial _ hstep
    · exact execInstr_zeroKept _ _ _ hstep

/-- **`$zero` reads `0` after any step**, given it read `0` before
(which `initialState` guarantees). The plain-English form of
`step_preserves_zero_register`. -/
theorem step_zero_register_reads_zero (p : Program) (s s' : State)
    (hzero : readReg s 0 = 0#32) (hstep : step p s = StepResult.next s') :
    readReg s' 0 = 0#32 := by
  rw [step_preserves_zero_register p s s' hstep, hzero]

/-- `run`'s inner loop never changes `$zero`: each iteration is one `step`
(`step_preserves_zero_register`). -/
theorem run_go_preserves_zero_register (p : Program) (fuel : Nat) (s : State) (steps : Nat) :
    readReg (run.go p fuel s steps).finalState 0 = readReg s 0 := by
  induction fuel generalizing s steps with
  | zero => rfl
  | succ n ih =>
    unfold run.go
    split
    · rfl
    · next s1 h =>
      rw [ih s1 (steps + 1)]
      exact step_preserves_zero_register p s s1 h

/-- **Whole-run invariant: `$zero` is the same at the end of any run as at
its start**, for any program, any start state, any step budget. -/
theorem run_preserves_zero_register (p : Program) (s₀ : State) (maxSteps : Nat) :
    readReg (run p s₀ maxSteps).finalState 0 = readReg s₀ 0 :=
  run_go_preserves_zero_register p maxSteps s₀ 0

/-- **`$zero` reads `0` at the end of every run started from
`initialState`.** -/
theorem run_initialState_zero_register (p : Program) (pc : W32) (maxSteps : Nat) :
    readReg (run p (initialState pc) maxSteps).finalState 0 = 0#32 := by
  rw [run_preserves_zero_register]; rfl

/-- **A write to `$zero` is never observable.** No matter what value gets
"written" to register `0`, reading it straight back always gives `0` —
exactly INSTRUCTION-REF Global rule 2, stated as a rejection of the bad
behavior "the write took effect". -/
theorem zero_write_not_observable (s : State) (v : W32) (hv : readReg s 0 ≠ v) :
    readReg (writeReg s 0 v) 0 ≠ v := by
  rw [writeReg_preserves_zero_slot]
  exact hv

#guard decide (readReg (writeReg (initialState textBase) 0 0xdeadbeef#32) 0 ≠ 0xdeadbeef#32) = true

/-- **Hypothesis-carrying form of `step_preserves_zero_register`**, kept
kept under its earlier name: a corollary of the structural theorem
`step_preserves_zero_register`, which needs none of the
`hfetch`/`hdecode`/`hpb` hypotheses (history: `docs/PROOF-NOTES.md`). -/
theorem step_preserves_zero_register_nontrivial (p : Program) (s s' : State) (w : W32)
    (instr : Instruction)
    (_hfetch : fetchWord p s.pc = some w) (_hdecode : decode w = some instr)
    (_hpb : s.pendingBranch = none)
    (hstep : step p s = StepResult.next s') :
    readReg s' 0 = readReg s 0 :=
  step_preserves_zero_register p s s' hstep
