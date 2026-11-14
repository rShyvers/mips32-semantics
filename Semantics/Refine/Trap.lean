import Semantics.Refine.BridgeMem

/-!
# Refine.Trap — the conditional traps and BREAK against `execInstr` (7C S2)

Each conditional trap is `if <comparison> then SignalException(Trap)` (MD00086 Vol II-A Rev 6.06,
TEQ p.416 ... TNEI p.439); the model's is `if <comparison> then takeException s excCodeTr else
mkNext s s`. `trap_finish` (BridgeMem) closes both outcomes once the two comparisons are shown equal.
-/

namespace Refine

open Manual

theorem toNat_zero_append (x : W32) : (0#1 ++ x).toNat = x.toNat := by
  rw [BitVec.toNat_append]; simp

theorem ult_ext (x y : W32) : (0#1 ++ x).ult (0#1 ++ y) = decide (x.toNat < y.toNat) := by
  rw [BitVec.ult, toNat_zero_append, toNat_zero_append]

theorem ule_ext (x y : W32) : (0#1 ++ x).ule (0#1 ++ y) = decide (x.toNat ≤ y.toNat) := by
  rw [BitVec.ule, toNat_zero_append, toNat_zero_append]

/-- **TEQ refines.** -/
theorem teq_refines (s : State) (hg : Good s) (rs rt code w : W32)
    (hw : enc (.teq rs rt code) = some w) :
    Execute modelCtx w (.teq rs rt code) (abs s) = some (abs (execInstr s (.teq rs rt code))) := by
  s2_open Ops.TEQ (Ops.TEQ rs rt code)
  exact trap_finish s _ _ rfl

/-- **TNE refines.** -/
theorem tne_refines (s : State) (hg : Good s) (rs rt code w : W32)
    (hw : enc (.tne rs rt code) = some w) :
    Execute modelCtx w (.tne rs rt code) (abs s) = some (abs (execInstr s (.tne rs rt code))) := by
  s2_open Ops.TNE (Ops.TNE rs rt code)
  exact trap_finish s _ _ (by rw [Bool.eq_iff_iff]; simp)

/-- **TLT refines.** -/
theorem tlt_refines (s : State) (hg : Good s) (rs rt code w : W32)
    (hw : enc (.tlt rs rt code) = some w) :
    Execute modelCtx w (.tlt rs rt code) (abs s) = some (abs (execInstr s (.tlt rs rt code))) := by
  s2_open Ops.TLT (Ops.TLT rs rt code)
  exact trap_finish s _ _ (by rw [BitVec.slt]; rfl)

/-- **TGE refines.** -/
theorem tge_refines (s : State) (hg : Good s) (rs rt code w : W32)
    (hw : enc (.tge rs rt code) = some w) :
    Execute modelCtx w (.tge rs rt code) (abs s) = some (abs (execInstr s (.tge rs rt code))) := by
  s2_open Ops.TGE (Ops.TGE rs rt code)
  exact trap_finish s _ _ (by rw [BitVec.sle]; rfl)

/-- **TLTU refines.** -/
theorem tltu_refines (s : State) (hg : Good s) (rs rt code w : W32)
    (hw : enc (.tltu rs rt code) = some w) :
    Execute modelCtx w (.tltu rs rt code) (abs s) = some (abs (execInstr s (.tltu rs rt code))) := by
  s2_open Ops.TLTU (Ops.TLTU rs rt code)
  exact trap_finish s _ _ (ult_ext _ _)

/-- **TGEU refines.** -/
theorem tgeu_refines (s : State) (hg : Good s) (rs rt code w : W32)
    (hw : enc (.tgeu rs rt code) = some w) :
    Execute modelCtx w (.tgeu rs rt code) (abs s) = some (abs (execInstr s (.tgeu rs rt code))) := by
  s2_open Ops.TGEU (Ops.TGEU rs rt code)
  exact trap_finish s _ _ (ule_ext _ _)

/-- **TEQI refines.** -/
theorem teqi_refines (s : State) (hg : Good s) (rs imm w : W32)
    (hw : enc (.teqi rs imm) = some w) :
    Execute modelCtx w (.teqi rs imm) (abs s) = some (abs (execInstr s (.teqi rs imm))) := by
  s2_open Ops.TEQI (Ops.TEQI rs imm)
  exact trap_finish s _ _ rfl

/-- **TNEI refines.** -/
theorem tnei_refines (s : State) (hg : Good s) (rs imm w : W32)
    (hw : enc (.tnei rs imm) = some w) :
    Execute modelCtx w (.tnei rs imm) (abs s) = some (abs (execInstr s (.tnei rs imm))) := by
  s2_open Ops.TNEI (Ops.TNEI rs imm)
  exact trap_finish s _ _ (by rw [Bool.eq_iff_iff]; simp)

/-- **TGEI refines.** -/
theorem tgei_refines (s : State) (hg : Good s) (rs imm w : W32)
    (hw : enc (.tgei rs imm) = some w) :
    Execute modelCtx w (.tgei rs imm) (abs s) = some (abs (execInstr s (.tgei rs imm))) := by
  s2_open Ops.TGEI (Ops.TGEI rs imm)
  exact trap_finish s _ _ (by rw [BitVec.sle]; rfl)

/-- **TGEIU refines.** -/
theorem tgeiu_refines (s : State) (hg : Good s) (rs imm w : W32)
    (hw : enc (.tgeiu rs imm) = some w) :
    Execute modelCtx w (.tgeiu rs imm) (abs s) = some (abs (execInstr s (.tgeiu rs imm))) := by
  s2_open Ops.TGEIU (Ops.TGEIU rs imm)
  exact trap_finish s _ _ (ule_ext _ _)

/-- **TLTI refines.** -/
theorem tlti_refines (s : State) (hg : Good s) (rs imm w : W32)
    (hw : enc (.tlti rs imm) = some w) :
    Execute modelCtx w (.tlti rs imm) (abs s) = some (abs (execInstr s (.tlti rs imm))) := by
  s2_open Ops.TLTI (Ops.TLTI rs imm)
  exact trap_finish s _ _ (by rw [BitVec.slt]; rfl)

/-- **TLTIU refines.** -/
theorem tltiu_refines (s : State) (hg : Good s) (rs imm w : W32)
    (hw : enc (.tltiu rs imm) = some w) :
    Execute modelCtx w (.tltiu rs imm) (abs s) = some (abs (execInstr s (.tltiu rs imm))) := by
  s2_open Ops.TLTIU (Ops.TLTIU rs imm)
  exact trap_finish s _ _ (ult_ext _ _)

/-- **BREAK refines.** -/
theorem break_refines (s : State) (hg : Good s) (code w : W32)
    (hw : enc (.break code) = some w) :
    Execute modelCtx w (.break code) (abs s) = some (abs (execInstr s (.break code))) := by
  s2_open Ops.BREAK (Ops.BREAK code)
  simp only [SignalException]
  rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl,
    gep_take s .Breakpoint rfl excCodeBp (by decide)]
  rfl

end Refine
