import Semantics.Specs.Lemmas

/-!
# Tactics — the two proof scripts shared by the per-instruction specs

Almost every `<ctor>_spec_raw` theorem has the same shape

    theorem add_spec_raw (s : State) (w rs rt rd : W32)
        (hfetch : readMemWord s s.pc = some w) (hdecode : decode w = some (.add rs rt rd))
        (hpb : s.pendingBranch = none) :
        step s = <right-hand side written with the public state primitives> := by
      step_spec

and the same proof: `step` fetches `w` from memory (`hfetch`), decodes it (`hdecode`), and the arm of
`execInstr` for that constructor is, by computation, the right-hand side. The two macros below
are that proof, written once. They prove nothing by themselves: every use is elaborated and
kernel-checked at the theorem that calls it (`lake check` replays all of them).

Both macros refer to the theorem's binders **by name** (`s`, `hfetch`, `hdecode`, `hpb`, and
`hcu` for the FPU one), which is why they are declared with `hygiene false`. A theorem that
names these differently, or whose proof needs more than computation, keeps an explicit proof.

There are no statements in this file.
-/

set_option hygiene false in
/-- `step_spec` proves `step s = rhs` for an instruction that is not in a delay slot, given

* `hfetch  : readMemWord s s.pc = some w` (the fetch: the word in memory at `pc`),
* `hdecode : decode w = some (.ctor …)`,
* `hpb     : s.pendingBranch = none`.

Steps: (1) split `s` into its fields and substitute `pendingBranch := none`, so that `advance`
/ `mkNext` compute; (2) unfold `step`, rewrite the fetch and the decode; (3) both sides are now
the same term up to computation: `rfl`. -/
macro "step_spec" : tactic => `(tactic| (
  obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, pb, llBit, cp0Status, cp0Cause, cp0Epc,
    cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
  simp only at hpb
  subst hpb
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  try dsimp only
  rfl))

set_option hygiene false in
/-- `fp_step_spec` is `step_spec` for coprocessor-1 instructions, whose theorems carry the extra
hypothesis `hcu : cu1Enabled s = true` (otherwise the instruction raises Coprocessor Unusable,
`fp_coprocessor_unusable`).

Steps: (1) unfold `step`, rewrite the fetch and the decode; (2) `execInstr_eq_body` discharges
the delay-slot and Coprocessor-Unusable guards of `execInstr` using `hpb` and `hcu`, leaving the
instruction's own arm; (3) close the goal: for an arithmetic instruction the arm ends in
`fpFinishS`/`fpFinishD`/`fpFinishCmp`; the statement's right-hand side is `fpCompletesS`/`D`/`Cmp`,
which `fpFinish*_eq` (right to left) turns back into `fpFinish*`, and then `rfl` (`rw` fails at
once when the statement has no such call, so the alternatives are tried cheaply); for a
non-arithmetic one (moves, loads, stores, control registers,
branches) it is `rfl` after substituting `pendingBranch := none`, as in `step_spec`. -/
macro "fp_step_spec" : tactic => `(tactic| (
  unfold step
  rw [hfetch]
  dsimp only
  rw [hdecode]
  dsimp only
  rw [execInstr_eq_body s _ (Or.inr hpb) (Or.inr hcu)]
  first
    | (rw [← fpFinishS_eq s _ _ hpb]; rfl)
    | (rw [← fpFinishD_eq s _ _ hpb]; rfl)
    | (rw [← fpFinishCmp_eq s _ _ hpb]; rfl)
    | (obtain ⟨pc, regs, hi, lo, fpRegs, fcsr, mem, pb, llBit, cp0Status, cp0Cause, cp0Epc,
         cp0BadVAddr, cp0ErrorEpc, llAddr, cp0EBase⟩ := s
       simp only at hpb
       subst hpb
       rfl)))
