import Semantics.Refine.Trap

/-!
# Refine.Syscall — SYSCALL against `execInstr`

The architecture's `SYSCALL` is `SignalException(SystemCall)` (MD00086 Vol II-A Rev 6.06, SYSCALL,
p.415); the hosted services of `Env.lean` are the environment and are not part of `execInstr`.
-/

namespace Refine

open Manual

/-- **SYSCALL refines.** -/
theorem syscall_refines (s : State) (hg : Good s) (code w : W32)
    (hw : enc (.syscall code) = some w) :
    Execute modelCtx w (.syscall code) (abs s) = some (abs (execInstr s (.syscall code))) := by
  s2_open Ops.SYSCALL (Ops.SYSCALL code)
  simp only [SignalException]
  rw [show modelCtx.oracle = modelOracle from rfl, show modelCtx.impl = modelImpl from rfl,
    gep_take s .SystemCall rfl excCodeSys (by decide)]
  rfl

end Refine
