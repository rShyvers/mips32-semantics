import Semantics.Refine.Cycle
import Semantics.Refine.Invariant
import Semantics.Refine.IntArith
import Semantics.Refine.Shift
import Semantics.Refine.BitOps
import Semantics.Refine.Immediate
import Semantics.Refine.Memory
import Semantics.Refine.Atomic
import Semantics.Refine.Trap
import Semantics.Refine.Syscall
import Semantics.Refine.Branch
import Semantics.Refine.Jump
import Semantics.Refine.Cp0
import Semantics.Refine.System
import Semantics.Refine.FpuArith
import Semantics.Refine.FpuConvert
import Semantics.Refine.FpuMemory
import Semantics.Refine.FpuMove
import Semantics.Refine.FpuControl
import Semantics.Refine.PcRel
import Semantics.Refine.CompactBranch
import Semantics.Refine.FpuR6

/-!
# Refine.Instr — the per-instruction refinement of every constructor

`InstrRefines i` is the shape of the per-instruction theorems `Refine.<ctor>_refines`
(`docs/MANUAL-SPEC.md` I.2 item 9), quantified over the states the cycle executes an instruction
in: the invariant `Inv s` (`Refine/Defs.lean`), and `w` is a fetched word
that `decode`s to `i` (so `enc i = some w` by `decode_enc`, `Refine/Decode.lean`).

`allInstrRefines` collects the per-constructor theorems: it does `cases i` and, in the goal of
constructor `c`, applies `Refine.c_refines` found by name (`apply_ctor_lemma`, below). It is also the
completeness check of plan §6.3 for the refinements: a constructor added to `Instruction` without a
`Refine.<ctor>_refines` makes `apply_ctor_lemma` fail on its case (naming the missing theorem), and the
build fails.
-/

namespace Refine

open Manual

/-- **The per-instruction refinement of `i`**: from every state the cycle executes `i` in, the
spec's `Execute` of `i` (fetched as `w`) is the model's `execInstr`. -/
def InstrRefines (i : Instruction) : Prop :=
  ∀ (s : State) (w : W32), Inv s → decode w = some i → enc i = some w →
    Execute modelCtx w i (abs s) = some (abs (execInstr s i))

/-! ## Dispatch by constructor name -/

open Lean Meta Elab Tactic in
/-- The constructor `c` of the first `Instruction.c …` application in `e` (pre-order), if any. -/
def firstInstrCtor? (e : Expr) : MetaM (Option Name) := do
  let env ← getEnv
  let isCtor (f : Expr) : Bool := match f.constName? with
    | some n => n.getPrefix == ``Instruction && (env.find? n).any (·.isCtor)
    | none => false
  return (e.find? (fun s => isCtor s.getAppFn)).bind (·.getAppFn.constName?)

open Lean Meta Elab Tactic in
/-- **`apply_ctor_lemma "pre" "suf" (at h)? (else tac)?`** — apply the per-constructor lemma by name.

It reads the constructor `c` of the first `Instruction.c …` in the goal (or in hypothesis `h` with
`at h`), and `apply`s `Refine.<pre>c<suf>` (e.g. `"" "_refines"` gives `Refine.add_refines`). The
arguments are found by unification with the goal; every premise left over must be closed by
`assumption`, else the tactic fails. If that theorem does not exist it runs `tac`, or, without
`else`, fails with an error naming the missing theorem. -/
syntax (name := applyCtorLemma) "apply_ctor_lemma " str str (" at " ident)? (" else " tacticSeq)? : tactic

open Lean Meta Elab Tactic in
@[tactic applyCtorLemma] def evalApplyCtorLemma : Tactic := fun stx => withMainContext do
  let pre := stx[1].isStrLit?.getD ""; let suf := stx[2].isStrLit?.getD ""
  let src ← if stx[3].isNone then getMainTarget
    else do instantiateMVars (← getLocalDeclFromUserName stx[3][1].getId).type
  let some c ← firstInstrCtor? src
    | throwError "apply_ctor_lemma: no `Instruction` constructor in {src}"
  let thm := `Refine ++ Name.mkSimple (pre ++ c.getString! ++ suf)
  if (← getEnv).contains thm then
    let gs ← (← getMainGoal).apply (← mkConstWithFreshMVarLevels thm)
    for g in gs do
      unless ← g.isAssigned do
        unless (← g.assumptionCore) do
          throwError "apply_ctor_lemma: `{thm}` left a premise no hypothesis closes:{indentD (← g.getType)}"
    replaceMainGoal []
  else if stx[4].isNone then
    throwError "apply_ctor_lemma: constructor `{c}` has no theorem `{thm}`"
  else evalTactic stx[4][1]

/-- **Every instruction refines its Operation**: `cases i`, then `Refine.<ctor>_refines` of each
constructor, its `Good s` / `FcsrReservedZero s` / `enc` premises taken from the hypotheses. -/
theorem allInstrRefines (i : Instruction) : InstrRefines i := by
  cases i <;> (intro s w ⟨hg, hres, _⟩ _ hw; apply_ctor_lemma "" "_refines")

end Refine
