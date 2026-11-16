import Lean.Elab.Tactic
import Semantics.Specs.Lemmas

/-!
# Invariants — `$zero` is preserved by `step` and `run`

`step_preserves_zero_register` is proved structurally for every instruction at once;
`ZeroKept`, the `zeroKept_*` lemmas and the `zk_fwd`/`zk_simp` tactics are its proof devices.

## Theorems in this file (23)

  `writeReg_preserves_zero_slot` `writeReg_regs_zero` `writeFpReg_regs` `writeFpD_regs`
  `writeMemByte_getD_regs` `advance_regs` `zeroKept_next` `zeroKept_mkNext`
  `zeroKept_takeException` `zeroKept_takeException'` `zeroKept_takeAddressException`
  `zeroKept_exceptionEntry` `zeroKept_takeCoprocessorUnusable` `zeroKept_fpFinishS`
  `zeroKept_fpFinishD` `execInstr_zeroKept` `step_preserves_zero_register`
  `step_zero_register_reads_zero` `run_preserves_zero_register`
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
the only ways `execInstr` (`step`'s dispatch) ever builds its result
state — `mkNext`, `takeException`, a literal `{ s with … }` — keep register slot `0` intact as long as the result
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

/-- `ZeroKept s r`: register `0` reads the same in the result state `r` as in `s`. -/
def ZeroKept (s : State) (r : State) : Prop :=
  readReg r 0 = readReg s 0

/-- `writeReg_preserves_zero_slot`, restated on the raw `regs` array (the
normal form the `zk_simp` simp set below works in). -/
theorem writeReg_regs_zero (s : State) (i : Fin 32) (v : W32) :
    (writeReg s i v).regs.getD 0 0#32 = s.regs.getD 0 0#32 :=
  writeReg_preserves_zero_slot s i v

/-- `writeFpReg` only touches `fpRegs`. -/
theorem writeFpReg_regs (s : State) (i : Fin 32) (v : W32) :
    (writeFpReg s i v).regs = s.regs := rfl

/-- `writeFpD` (one 64-bit `writeFpReg64`) only touches
`fpRegs`. -/
theorem writeFpD_regs (s : State) (f : W32) (v : BitVec 64) :
    (writeFpD s f v).regs = s.regs := rfl

/-- `(writeMemByte s a v).getD s` (the shape `swl`/`swr` use) keeps `regs`. -/
theorem writeMemByte_getD_regs (s : State) (a : W32) (v : UInt8) :
    ((writeMemByte s a v).getD s).regs = s.regs := by
  unfold writeMemByte; cases translate s a <;> rfl

/-- `Step.lean`'s `advance` (delay-slot resolution / `pc + 4`) only
touches `pc` and `pendingBranch`. -/
theorem advance_regs (orig result : State) : (advance orig result).regs = result.regs := by
  unfold advance; split <;> rfl

theorem zeroKept_next (s r : State) :
    ZeroKept s r ↔ r.regs.getD 0 0#32 = s.regs.getD 0 0#32 := Iff.rfl

theorem zeroKept_mkNext (s r : State) :
    ZeroKept s (mkNext s r) ↔ r.regs.getD 0 0#32 = s.regs.getD 0 0#32 := by
  unfold mkNext
  rw [zeroKept_next, advance_regs]

theorem zeroKept_takeException (s : State) (c : W32) :
    ZeroKept s (takeException s c) ↔ True :=
  iff_true_intro rfl

/-- An exception taken from a state `t` that differs from `s` outside `regs`
(the FP paths record FCSR first). -/
theorem zeroKept_takeException' (s t : State) (c : W32) :
    ZeroKept s (takeException t c) ↔ t.regs.getD 0 0#32 = s.regs.getD 0 0#32 := Iff.rfl

theorem zeroKept_takeAddressException (s : State) (c a : W32) :
    ZeroKept s (takeAddressException s c a) ↔ True :=
  iff_true_intro rfl

theorem zeroKept_exceptionEntry (s : State) (c ce : W32) :
    ZeroKept s (exceptionEntry s c ce) ↔ True :=
  iff_true_intro rfl

theorem zeroKept_takeCoprocessorUnusable (s : State) :
    ZeroKept s (takeCoprocessorUnusable s) ↔ True :=
  iff_true_intro rfl

/-- The three ways an FP computational instruction completes
(`fpFinishS`/`fpFinishD`: Floating Point exception, or FCSR
update plus an FP-register write) never touch `regs`. -/
theorem zeroKept_fpFinishS (s : State) (fd : W32) (r : BitVec 32 × Mips.Fp.Flags) :
    ZeroKept s (fpFinishS s fd r) ↔ True :=
  iff_true_intro (by
    show readReg (fpFinishS s _ r) 0 = readReg s 0
    unfold fpFinishS
    dsimp only
    split
    · rfl
    · show (advance _ _).regs.getD 0 0#32 = _
      rw [advance_regs]; rfl)

theorem zeroKept_fpFinishD (s : State) (fd : W32) (r : BitVec 64 × Mips.Fp.Flags) :
    ZeroKept s (fpFinishD s fd r) ↔ True :=
  iff_true_intro (by
    show readReg (fpFinishD s _ r) 0 = readReg s 0
    unfold fpFinishD
    dsimp only
    split
    · rfl
    · show (advance _ _).regs.getD 0 0#32 = _
      rw [advance_regs]; rfl)

/-- One FP operation completed through `fpThen` keeps `$zero` when every
continuation does, from the state with the FCSR updated. -/
theorem zeroKept_fpThen {α : Type} (s : State) (r : α × Mips.Fp.Flags) (k : State → α → State)
    (h : ∀ p, ZeroKept { s with fcsr := (Mips.Fp.fpUpdate s.fcsr r.2).1 }
      (k { s with fcsr := (Mips.Fp.fpUpdate s.fcsr r.2).1 } p)) :
    ZeroKept s (fpThen s r k) := by
  unfold fpThen
  dsimp only
  split
  · rfl
  · exact h _

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
  simp only [zeroKept_mkNext, zeroKept_takeException,
    zeroKept_takeException', zeroKept_takeAddressException, zeroKept_takeCoprocessorUnusable, zeroKept_fpFinishS,
    zeroKept_fpFinishD,
    writeReg_regs_zero, writeFpReg_regs, writeFpD_regs, writeMemByte_getD_regs, *])

/-- The fallback of the loop below, for a result built directly as `{ s with … }` (branches,
`eret`): unfold `ZeroKept` itself (`zeroKept_next` is definitional, so it must not be in `zk_simp`,
where it would fire before the more specific lemmas). -/
macro "zk_simp_next" : tactic => `(tactic|
  simp only [zeroKept_next, writeReg_regs_zero, writeFpReg_regs, writeFpD_regs,
    writeMemByte_getD_regs, *])

-- all 203 constructors through one generic tactic loop
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
  · exact (zeroKept_takeException _ _).mpr trivial
  · split
    · exact (zeroKept_takeCoprocessorUnusable _).mpr trivial
    · split
      · exact (zeroKept_exceptionEntry _ _ _).mpr trivial
      · cases instr <;> exec_unfold <;>
          repeat' (first | (zk_fwd; zk_simp; done) | (zk_fwd; zk_simp_next; done) | split |
            (apply zeroKept_fpThen; intro _))

/-- **Global invariant: `$zero` is never changed by a step.** Register `0` reads the same thing
after a step as before — for **every** state and instruction, with no side conditions
(INSTRUCTION-REF Global rule 2, "writes to `$zero` are a no-op"). Proof: `step` is an interrupt
entry, a standby step (neither writes a GPR), or fetch/decode (whose failures are exceptions)
followed by `execInstr`; see `execInstr_zeroKept`. -/
theorem step_preserves_zero_register (s : State) : readReg (step s) 0 = readReg s 0 := by
  unfold step stepCore
  split
  · rfl
  split
  · unfold standbyStep; split <;> rfl
  unfold execute
  split
  · rfl
  · split
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl
    · exact execInstr_zeroKept _ _

/-- **`$zero` reads `0` after any step**, given it read `0` before
(which `initialState` guarantees). The plain-English form of
`step_preserves_zero_register`. -/
theorem step_zero_register_reads_zero (s : State) (hzero : readReg s 0 = 0#32) :
    readReg (step s) 0 = 0#32 := by
  rw [step_preserves_zero_register s, hzero]

/-- **Whole-run invariant: `$zero` is the same at the end of any run as at
its start**, for any start state and any number of steps. -/
theorem run_preserves_zero_register (s₀ : State) (n : Nat) :
    readReg (run s₀ n) 0 = readReg s₀ 0 := by
  induction n generalizing s₀ with
  | zero => rfl
  | succ n ih => rw [run, ih, step_preserves_zero_register]

/-- **`$zero` reads `0` at the end of every run started from
`initialState`.** -/
theorem run_initialState_zero_register (pc : W32) (n : Nat) :
    readReg (run (initialState pc) n) 0 = 0#32 := by
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
under its earlier name: a corollary of the structural theorem
`step_preserves_zero_register`, which needs none of the
`hfetch`/`hdecode`/`hpb` hypotheses (history: `docs/PROOF-NOTES.md`). -/
theorem step_preserves_zero_register_nontrivial (s s' : State) (w : W32)
    (instr : Instruction)
    (_hfetch : readMemWord s s.pc = some w) (_hdecode : decode w = some instr)
    (_hpb : s.pendingBranch = none)
    (hstep : step s = s') :
    readReg s' 0 = readReg s 0 := by
  rw [← hstep]; exact step_preserves_zero_register s
